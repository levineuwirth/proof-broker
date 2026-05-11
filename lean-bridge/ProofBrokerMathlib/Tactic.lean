/-
Mathlib-flavored extension to `ProofBroker.Tactic`.

Importing `ProofBrokerMathlib` activates two things for the
`proof_broker` / `proof_broker_term` tactics:

1. **LRA reach** for `proof_broker`: registers a Real reifier + a
   `linarith`-based closer. With the cert verification gating the
   call (the OCaml-side verifier has already accepted the proof),
   `linarith` produces an axiom-free proof term — same contract as
   `omega` for LIA.

2. **Tier 2 case-split term-mode** for `proof_broker_term` on
   LRA goals: the new `closeViaCaseSplitReal` destructs the cert's
   named disjunctive IR hypothesis and applies, per branch, the
   matching lemma's Farkas witness via `rFarkasContradict` from
   `ProofBrokerMathlib.TermMode`. Cert is fully consumed: every
   Farkas multiplier flows through the proof term. No `linarith`
   call on the per-branch arithmetic (only on the narrow
   strict-positivity polynomial-identity subgoal).

`ProofBroker` (the core lib) is Mathlib-free and stays so:
projects that only need LIA support don't pay the Mathlib build
cost. Importing `ProofBrokerMathlib` is the opt-in.

Scope: `Real` only, with `LE.le` / `LT.lt` / `GE.ge` / `GT.gt` /
`Eq` comparisons, `HAdd` / `HSub` / `HMul` / `Neg.neg` arithmetic,
`OfNat.ofNat` and `OfScientific.ofScientific` literals. Tier 2
case-split: arity-2 disjunctive hypothesis (`A \/ B`) only;
higher arity is mechanical.
-/

import Lean
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import ProofBroker.Tactic
import ProofBrokerMathlib.TermMode

namespace ProofBrokerMathlib.Tactic

open Lean Lean.Elab.Tactic Lean.Meta ProofBroker.IR

/-- Decode an LRA-eligible type. Today: `Real`. Add `Rat`,
    `Mathlib`'s `EReal`, etc. here when a use case appears. -/
private def reifyTypeMathlib (ty : Expr) : MetaM (Option ProofBroker.IR.TypeRef) := do
  if ty.isConstOf ``Real then return some "Real"
  return none

/-- Same recognition as `reifyTypeMathlib` but invoked from the
    `buildIR` LCtx walk, which classifies non-Prop locals as IR
    `freeVars`. Identical for our scope. -/
private def freeVarTypeMathlib (ty : Expr) : MetaM (Option ProofBroker.IR.TypeRef) := do
  reifyTypeMathlib ty

/-- Extract a Real-typed numeric literal as a value-string + type
    tag. Handles `OfNat.ofNat` over `Real` (e.g. `(5 : ℝ)`) and
    `OfScientific.ofScientific` over `Real` (e.g. `(0.5 : ℝ)`,
    which Lean elaborates as `OfScientific.ofScientific 5 true 1`
    meaning `5 * 10^(-1)`).

    For scientific literals we render the value as `m/10^e` when
    the exponent is negative, or `m*10^e` flattened to a plain
    integer when non-negative. The OCaml side's
    `Linear_arith.rat_of_string` accepts both decimals and
    explicit `n/d`, so the rendered string round-trips through
    Farkas verification. -/
private def matchRealLiteral? (e : Expr) : MetaM (Option (String × ProofBroker.IR.TypeRef)) := do
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[α, n, _inst]) =>
    if α.isConstOf ``Real then
      match n.rawNatLit? with
      | some k => return some (toString k, "Real")
      | none => return none
    else return none
  | (``OfScientific.ofScientific, #[α, _inst, mantissa, signE, exp]) =>
    if α.isConstOf ``Real then
      let m? := mantissa.rawNatLit?
      let e? := exp.rawNatLit?
      let neg? :=
        match signE with
        | .const ``Bool.true _ => some true
        | .const ``Bool.false _ => some false
        | _ => none
      match m?, e?, neg? with
      | some m, some ex, some isNeg =>
        if isNeg then
          let denom := 10 ^ ex
          return some (s!"{m}/{denom}", "Real")
        else
          let scaled := m * 10 ^ ex
          return some (toString scaled, "Real")
      | _, _, _ => return none
    else return none
  | _ => return none

/-- Tactic that closes an LRA goal via Mathlib's `linarith`.
    Invoked from `closeOrFail` only when cert verification
    already succeeded, so the call is guaranteed to find a
    closure. -/
private def lraCloseWithLinarith : TacticM Unit := do
  evalTactic (← `(tactic| linarith))

/- ============================================================
   Tier 2 case-split term-mode closer (LRA)

   Parses the cert's `payload.lemmas_used` and
   `payload.structural_hint.disjunctive_hypothesis`. Destructs the
   named disjunctive hypothesis in the Lean LCtx and applies the
   matching lemma's Tier 1 Farkas witness per branch via
   `rFarkasContradict`. Each branch's per-branch closer is
   conceptually the LRA analog of core's `closeViaTermModeFalse`,
   but doesn't need to be exposed externally — it's defined
   privately here for the case-split path.
   ============================================================ -/

/-- Look up a hypothesis by user-name in the LCtx, returning the
    `(FVar Expr, type Expr)` pair. Throws if not found or shadowed.

    Accepts either an exact match or a hygienic-suffix match
    (`name._@.<module>._hyg.<N>`) — Lean's syntax quotations
    (`(tactic| ... with hCase | ...)`) macro-hygienize the introduced
    binder name, so [rcases]-introduced hypotheses don't compare
    equal to the bare string. Prefix match keeps the witness's
    name lookup ("case") robust to the destruct path. -/
private def fvarOfName (name : String) : MetaM (Expr × Expr) := do
  let lctx ← getLCtx
  let hits := lctx.foldl (init := #[]) fun acc decl =>
    if decl.isImplementationDetail then acc
    else
      let userName := decl.userName.toString
      if userName == name || userName.startsWith (name ++ "._@.") then
        acc.push decl
      else acc
  match hits.toList with
  | [decl] => return (Expr.fvar decl.fvarId, decl.type)
  | [] => throwError "proof_broker_term: hypothesis '{name}' not in scope"
  | _ => throwError "proof_broker_term: hypothesis '{name}' is ambiguous (shadowed)"

/-- Recognize a `Real` `≤` / `≥` shape in a hypothesis type.
    Returns `(direction, lhs, rhs)` where `direction = true` for
    `≤` (use `rLeToLe0`), `false` for `≥` (use `rGeToLe0`).
    Lean's `≥` desugars to `LE.le b a`, so we only see `LE.le`
    here in practice — the explicit `GE.ge` branch is for
    robustness. -/
private def matchRealBound? (ty : Expr) : Option (Bool × Expr × Expr) :=
  match ty.getAppFnArgs with
  | (``LE.le, #[α, _, a, b]) =>
    if α.isConstOf ``Real then some (true, a, b) else none
  | (``GE.ge, #[α, _, a, b]) =>
    if α.isConstOf ``Real then some (false, a, b) else none
  | _ => none

/-- Real-typed `normalizeHypothesis`: from `(h : a ≤ b : Real)` or
    `(h : a ≥ b : Real)` build the pair `((a - b, b - a respectively),
    proof : <that> ≤ 0)` via `rLeToLe0` / `rGeToLe0`. Both shapes
    arise in practice — destruct of `Or { LE.le x 0; LE.le 10 x }`
    leaves the second branch's `hCase` typed at the original
    disjunct shape `LE.le 10 x`, fine; the un-destructed
    hypotheses `h_low : x ≥ 1` and `h_high : x ≤ 9` carry the
    user-written `GE.ge` head. -/
private def normalizeHypothesisReal (hypFV : Expr) (hypTy : Expr)
    : MetaM (Expr × Expr) := do
  match matchRealBound? hypTy with
  | some (true, a, b) =>
    let normExpr ← Lean.Meta.mkAppM ``HSub.hSub #[a, b]
    let proof ← Lean.Meta.mkAppM
                  ``ProofBrokerMathlib.TermMode.rLeToLe0 #[hypFV]
    return (normExpr, proof)
  | some (false, a, b) =>
    let normExpr ← Lean.Meta.mkAppM ``HSub.hSub #[b, a]
    let proof ← Lean.Meta.mkAppM
                  ``ProofBrokerMathlib.TermMode.rGeToLe0 #[hypFV]
    return (normExpr, proof)
  | _ =>
    throwError "proof_broker_term: hypothesis shape outside Real ≤/≥ \
                 (got type {hypTy})"

/-- Build a Real literal Expr from a nonnegative Int via
    `OfNat.ofNat` over `Real`. The resulting Expr matches what
    Lean elaborates from a Nat-typed literal written at Real
    type, so the rest of the term builder's `mkAppM` calls
    pick up the Real arithmetic instances cleanly. -/
private def realLitExpr (c : Int) : MetaM Expr := do
  if c < 0 then
    throwError "proof_broker_term: negative Real coefficient {c}"
  let realTy := mkConst ``Real
  let natExpr : Expr := mkNatLit c.toNat
  Lean.Meta.mkAppOptM ``OfNat.ofNat #[some realTy, some natExpr, none]

/-- Build a proof of `(0 ≤ c : Real)` for a nonnegative literal c
    via Mathlib's `Nat.cast_nonneg`-style positivity, surfaced
    through `norm_num` since literal nonnegativity is exactly
    what `norm_num` discharges trivially. Axiom-free at literal
    arguments. -/
private def buildNonnegProofReal (cExpr : Expr) : TacticM Expr := do
  let realTy := mkConst ``Real
  let zero ← Lean.Meta.mkAppOptM ``OfNat.ofNat
                #[some realTy, some (mkNatLit 0), none]
  let goalTy ← Lean.Meta.mkAppM ``LE.le #[zero, cExpr]
  let mv ← Lean.Meta.mkFreshExprMVar goalTy
  let prevGoals ← getGoals
  setGoals [mv.mvarId!]
  evalTactic (← `(tactic| norm_num))
  setGoals prevGoals
  Lean.instantiateMVars mv

/-- Discharge a `linarith` subgoal in isolation. Restores the
    caller's goal list afterward. Used to close the narrow
    strict-positivity polynomial identity left as an evar inside
    the per-branch Farkas application. -/
private def closeLinarithSubgoal (mv : MVarId) : TacticM Unit := do
  let prevGoals ← getGoals
  setGoals [mv]
  evalTactic (← `(tactic| linarith))
  setGoals prevGoals

/-- Real-typed per-branch closer. Given the current goal (which
    must be `False`), an arity-2 entry list `[(name1, c1),
    (name2, c2)]`, and an optional name-override map (used to
    redirect the witness's "case" name to the destruct-bound
    hypothesis), build the `rFarkasContradict` proof term.

    The narrow `0 < c1*a1 + c2*a2` subgoal goes through
    `linarith`. linarith here is solving a literal-coefficient
    polynomial identity over symbolic differences, not the
    original LRA goal — the same narrow role `omega` plays in
    core's Int closer. -/
private def closeViaTermModeFalseReal
    (goal : MVarId)
    (entries : List (String × Int))
    (overrides : List (String × Expr × Expr) := [])
    : TacticM Unit := do
  let [(name1, c1), (name2, c2)] := entries
    | throwError "proof_broker_term: per-branch witness arity {entries.length} ≠ 2"
  goal.withContext do
    let resolve (name : String) : MetaM (Expr × Expr) := do
      match overrides.find? (fun (n, _, _) => n == name) with
      | some (_, fv, ty) => return (fv, ty)
      | none => fvarOfName name
    let (fv1, ty1) ← resolve name1
    let (fv2, ty2) ← resolve name2
    let (a1, h1') ← normalizeHypothesisReal fv1 ty1
    let (a2, h2') ← normalizeHypothesisReal fv2 ty2
    let c1Expr ← realLitExpr c1
    let c2Expr ← realLitExpr c2
    let hc1 ← buildNonnegProofReal c1Expr
    let hc2 ← buildNonnegProofReal c2Expr
    let zero ← realLitExpr 0
    let prod1 ← Lean.Meta.mkAppM ``HMul.hMul #[c1Expr, a1]
    let prod2 ← Lean.Meta.mkAppM ``HMul.hMul #[c2Expr, a2]
    let sum ← Lean.Meta.mkAppM ``HAdd.hAdd #[prod1, prod2]
    let hposTy ← Lean.Meta.mkAppM ``LT.lt #[zero, sum]
    let hposMV ← Lean.Meta.mkFreshExprMVar hposTy
    let term ← Lean.Meta.mkAppM
                 ``ProofBrokerMathlib.TermMode.rFarkasContradict
                 #[h1', h2', hc1, hc2, hposMV]
    closeLinarithSubgoal hposMV.mvarId!
    goal.assign term

/-- Parse the cert's `payload.structural_hint.disjunctive_hypothesis`
    into the IR hypothesis name string. -/
private def parseDisjunctiveHypName (cert : Json) : TacticM String := do
  match cert.getObjVal? "payload" >>= (·.getObjVal? "structural_hint")
        >>= (·.getObjValAs? String "disjunctive_hypothesis") with
  | .ok s => pure s
  | .error e =>
    throwError "proof_broker_term: cert payload missing \
                 structural_hint.disjunctive_hypothesis: {e}"

/-- Parse the cert's `payload.lemmas_used` into a list of
    `(case_shell, witness_json)` pairs. Decodes each `case` field
    through the existing `IR.Codec` so we get a `ShellTerm` we can
    compare structurally against the disjunctive hypothesis's
    disjuncts. -/
private def parseTier2LemmasUsed (cert : Json)
    : TacticM (List (ShellTerm × Json)) := do
  let payload ← match cert.getObjVal? "payload" with
    | .ok j => pure j
    | .error e => throwError "proof_broker_term: cert missing payload: {e}"
  let arr ← match payload.getObjVal? "lemmas_used" >>= (·.getArr?) with
    | .ok a => pure a
    | .error e => throwError "proof_broker_term: payload.lemmas_used not array: {e}"
  arr.toList.mapM fun entry => do
    let caseJ ← match entry.getObjVal? "case" with
      | .ok j => pure j
      | .error e => throwError "proof_broker_term: lemma missing 'case': {e}"
    let witnessJ ← match entry.getObjVal? "witness" with
      | .ok j => pure j
      | .error e => throwError "proof_broker_term: lemma missing 'witness': {e}"
    let caseShell ← match ProofBroker.IR.ShellTerm.fromJson? caseJ with
      | .ok s => pure s
      | .error e => throwError "proof_broker_term: lemma case shell parse error: {e}"
    return (caseShell, witnessJ)

/-- Parse a Farkas witness JSON into a coefficient list. Mirror
    of core's `parseFarkasCoefficients` but takes the witness
    directly (already pulled out of the Tier 2 lemma). -/
private def parseWitnessCoefficients (witness : Json)
    : TacticM (List (String × Int)) := do
  let arr ← match witness.getObjVal? "coefficients" >>= (·.getArr?) with
    | .ok a => pure a
    | .error e => throwError "proof_broker_term: witness coefficients not array: {e}"
  arr.toList.mapM fun entry => do
    let name := (entry.getObjValAs? String "hypothesis").toOption.getD ""
    let coefStr := (entry.getObjValAs? String "coefficient").toOption.getD ""
    if name == "" then throwError "proof_broker_term: witness entry missing hypothesis"
    match coefStr.toInt? with
    | some n => pure (name, n)
    | none =>
      throwError "proof_broker_term: non-integer coefficient '{coefStr}' \
                   (rationals not yet wired)"

/-- Tier 2 case-split closer entry point (LRA). Wired into
    `ProofBroker.Tactic.ReifierExt.tier2CaseSplitCloser` via the
    initialize block below. -/
private def closeViaCaseSplitReal (cert : Json) (ir : IR) : TacticM Unit := do
  let hypName ← parseDisjunctiveHypName cert
  let lemmasParsed ← parseTier2LemmasUsed cert
  -- Find the disjunctive hypothesis in the IR.
  let disjHyp := ir.context.hypotheses.find? (fun h => h.name == hypName)
  let disjHyp ← match disjHyp with
    | some h => pure h
    | none =>
      throwError "proof_broker_term: disjunctive hypothesis '{hypName}' \
                   not in IR context"
  -- Today: arity-2 only (binary `Or`). Higher arity is mechanical.
  let (leftDisj, rightDisj) ← match disjHyp.shell with
    | .or_ l r => pure (l, r)
    | _ =>
      throwError "proof_broker_term: hypothesis '{hypName}' is not Or-shaped"
  -- Shape-match each disjunct to a lemma. Structural BEq on
  -- ShellTerm — the cert's case shells come from the same SDK that
  -- emitted the IR's disjuncts, so they should match exactly.
  let findLemma (d : ShellTerm) : TacticM (List (String × Int)) := do
    match lemmasParsed.find? (fun (cs, _) => cs == d) with
    | some (_, w) => parseWitnessCoefficients w
    | none =>
      throwError "proof_broker_term: no Tier 2 lemma matches one of the \
                   disjuncts (BEq lookup failed — adapter / disjunct \
                   shape divergence?)"
  let leftEntries ← findLemma leftDisj
  let rightEntries ← findLemma rightDisj
  -- Destruct the disjunctive hypothesis. We use `rcases` so each
  -- branch's introduced hypothesis carries a stable user-name
  -- ("hCase") we can then redirect the witness's `"case"` lookups
  -- to via the closer's overrides map.
  let mainGoal ← getMainGoal
  mainGoal.withContext do
    let hypFV ← match (← getLCtx).findFromUserName? hypName.toName with
      | some d => pure (Expr.fvar d.fvarId)
      | none =>
        throwError "proof_broker_term: disjunctive hypothesis '{hypName}' \
                     not in Lean LCtx (IR vs Lean context drift?)"
    let hypIdent := mkIdent hypName.toName
    evalTactic (← `(tactic| rcases $hypIdent:term with hCase | hCase))
    let _ := hypFV
  -- Two subgoals now; dispatch each to closeViaTermModeFalseReal
  -- with the "case" name overridden to the destruct-bound hCase.
  let subgoals ← getGoals
  match subgoals with
  | [g1, g2] =>
    let runBranch (g : MVarId) (entries : List (String × Int)) : TacticM Unit := do
      setGoals [g]
      g.withContext do
        let (hCaseFV, hCaseTy) ← fvarOfName "hCase"
        closeViaTermModeFalseReal g entries [("case", hCaseFV, hCaseTy)]
    runBranch g1 leftEntries
    runBranch g2 rightEntries
    setGoals []
  | _ =>
    throwError "proof_broker_term: rcases produced {subgoals.length} \
                 subgoals (expected 2 for arity-2 case-split)"

initialize do
  ProofBroker.Tactic.reifierExt.set (some {
    reifyType := reifyTypeMathlib,
    freeVarType := freeVarTypeMathlib,
    matchLiteralExt := matchRealLiteral?,
    lraCloser := lraCloseWithLinarith,
    tier2CaseSplitCloser := closeViaCaseSplitReal,
    irFragment := "LRA",
  })

end ProofBrokerMathlib.Tactic
