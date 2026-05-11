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

/-- The four hypothesis-shape kinds the LRA term-mode closer
    normalizes. Mirror of core's `HypKind` but Real-typed. -/
private inductive HypKindReal
  | le | ge | lt | gt
deriving Repr

/-- Recognize a `Real` comparison shape in a hypothesis type. Returns
    `(kind, lhs, rhs)` where the kind picks the normalization helper
    and the strictness flag for the fold. -/
private def matchRealBound? (ty : Expr) : Option (HypKindReal × Expr × Expr) :=
  match ty.getAppFnArgs with
  | (``LE.le, #[α, _, a, b]) =>
    if α.isConstOf ``Real then some (.le, a, b) else none
  | (``GE.ge, #[α, _, a, b]) =>
    if α.isConstOf ``Real then some (.ge, a, b) else none
  | (``LT.lt, #[α, _, a, b]) =>
    if α.isConstOf ``Real then some (.lt, a, b) else none
  | (``GT.gt, #[α, _, a, b]) =>
    if α.isConstOf ``Real then some (.gt, a, b) else none
  | _ => none

/-- Normalized hypothesis output: linear-form LHS, proof of
    `(expr ≤ 0)` or `(expr < 0)`, and a `strict` flag distinguishing
    Le-shape from Lt-shape. Strict shapes arise from `Real` `<` / `>`
    hypotheses; the Le-shape helpers `rLeToLe0` / `rGeToLe0` keep
    `strict=false`, the Lt-shape helpers `rLtToLt0` / `rGtToLt0`
    set `strict=true`. -/
private structure NormalizedHypReal where
  expr : Expr
  proof : Expr
  strict : Bool

/-- Real-typed `normalizeHypothesis`: from `(h : a ≤ b : Real)` /
    `(h : a ≥ b : Real)` / `(h : a < b : Real)` / `(h : a > b : Real)`
    build a `NormalizedHypReal`. Strict shapes go through
    `rLtToLt0` / `rGtToLt0` (no LIA +1 trick over R — the strict-aware
    fold path consumes the `a < 0` proof directly). -/
private def normalizeHypothesisReal (hypFV : Expr) (hypTy : Expr)
    : MetaM NormalizedHypReal := do
  match matchRealBound? hypTy with
  | some (.le, a, b) =>
    let expr ← Lean.Meta.mkAppM ``HSub.hSub #[a, b]
    let proof ← Lean.Meta.mkAppM
                  ``ProofBrokerMathlib.TermMode.rLeToLe0 #[hypFV]
    return ⟨expr, proof, false⟩
  | some (.ge, a, b) =>
    let expr ← Lean.Meta.mkAppM ``HSub.hSub #[b, a]
    let proof ← Lean.Meta.mkAppM
                  ``ProofBrokerMathlib.TermMode.rGeToLe0 #[hypFV]
    return ⟨expr, proof, false⟩
  | some (.lt, a, b) =>
    let expr ← Lean.Meta.mkAppM ``HSub.hSub #[a, b]
    let proof ← Lean.Meta.mkAppM
                  ``ProofBrokerMathlib.TermMode.rLtToLt0 #[hypFV]
    return ⟨expr, proof, true⟩
  | some (.gt, a, b) =>
    let expr ← Lean.Meta.mkAppM ``HSub.hSub #[b, a]
    let proof ← Lean.Meta.mkAppM
                  ``ProofBrokerMathlib.TermMode.rGtToLt0 #[hypFV]
    return ⟨expr, proof, true⟩
  | _ =>
    throwError "proof_broker_term: hypothesis shape outside Real ≤/≥/</> \
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

/-- Strict counterpart of `buildNonnegProofReal`: build a proof of
    `(0 < c : Real)` for a strictly-positive literal c. Used when
    the strict-aware fold encounters a Lt premise — the coefficient
    side of the product needs `0 < c` strict (not just `0 ≤ c`) for
    the product to be strict via `rMulPosNeg`. norm_num discharges
    literal-positivity trivially. -/
private def buildPosProofReal (cExpr : Expr) : TacticM Expr := do
  let realTy := mkConst ``Real
  let zero ← Lean.Meta.mkAppOptM ``OfNat.ofNat
                #[some realTy, some (mkNatLit 0), none]
  let goalTy ← Lean.Meta.mkAppM ``LT.lt #[zero, cExpr]
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

/-- Real-typed per-branch / False-goal closer. Strict-aware fold:
    each entry's strictness flag (from `NormalizedHypReal.strict`)
    threads through the mul/add steps. With at least one strict
    premise (Lt-compiled, positive coef), the sum is strictly
    negative and `rFarkasContradictNStrict` closes against `0 ≤ sum`
    (linarith). All-Le premises take the standard
    `rFarkasContradictN` path against `0 < sum` (linarith again).
    Mirror of Rocq's `close_term_false` with strict tracking. -/
private def closeViaTermModeFalseReal
    (goal : MVarId)
    (entries : List (String × Int))
    (overrides : List (String × Expr × Expr) := [])
    : TacticM Unit := do
  if entries.isEmpty then
    throwError "proof_broker_term: empty witness — arity ≥ 1 required"
  goal.withContext do
    let resolve (name : String) : MetaM (Expr × Expr) := do
      match overrides.find? (fun (n, _, _) => n == name) with
      | some (_, fv, ty) => return (fv, ty)
      | none => fvarOfName name
    -- Normalize each entry. Builds (cExpr, hc_proof, expr, h_proof, strict)
    -- per entry — hc is strict (0 < c) if the premise is strict (Lt),
    -- non-strict (0 ≤ c) otherwise. Strict premise + strict coef →
    -- product is strict via rMulPosNeg.
    let normalized ← entries.mapM fun (name, c) => do
      let (fv, ty) ← resolve name
      let normHyp ← normalizeHypothesisReal fv ty
      let cExpr ← realLitExpr c
      let hc ← if normHyp.strict then buildPosProofReal cExpr
               else buildNonnegProofReal cExpr
      return (cExpr, hc, normHyp.expr, normHyp.proof, normHyp.strict)
    -- Build (c_i * a_i, proof, prod_strict). Strict premise picks
    -- rMulPosNeg (gives Lt); non-strict picks mul_nonpos_of_nonneg_of_nonpos
    -- (gives Le).
    let products ← normalized.mapM fun (cExpr, hc, a, ha, strict) => do
      let prod ← Lean.Meta.mkAppM ``HMul.hMul #[cExpr, a]
      let proof ←
        if strict then
          Lean.Meta.mkAppM ``ProofBrokerMathlib.TermMode.rMulPosNeg #[hc, ha]
        else
          Lean.Meta.mkAppM ``mul_nonpos_of_nonneg_of_nonpos #[hc, ha]
      return (prod, proof, strict)
    -- Left-associative fold tracking strictness. Picks the right
    -- add_* combinator from the 4-way cross product:
    --   Le+Le → Le (add_nonpos); Le+Lt → Lt (rAddLeLt);
    --   Lt+Le → Lt (rAddLtLe); Lt+Lt → Lt (rAddNeg).
    let pickAdd (accStrict prodStrict : Bool) : Name :=
      match accStrict, prodStrict with
      | false, false => ``add_nonpos
      | false, true  => ``ProofBrokerMathlib.TermMode.rAddLeLt
      | true,  false => ``ProofBrokerMathlib.TermMode.rAddLtLe
      | true,  true  => ``ProofBrokerMathlib.TermMode.rAddNeg
    let (sum, sumProof, sumStrict) ← match products with
      | [] => throwError "proof_broker_term: empty fold (internal)"
      | (p0, h0, s0) :: rest =>
        rest.foldlM (fun (accE, accH, accS) (p, h, ps) => do
          let newSum ← Lean.Meta.mkAppM ``HAdd.hAdd #[accE, p]
          let newProof ← Lean.Meta.mkAppM (pickAdd accS ps) #[accH, h]
          return (newSum, newProof, accS || ps)) (p0, h0, s0)
    -- Dispatch on final strictness. Strict path uses
    -- rFarkasContradictNStrict (s < 0 ∧ 0 ≤ s → False); standard path
    -- uses rFarkasContradictN (s ≤ 0 ∧ 0 < s → False). Both close the
    -- residual positivity / non-negativity claim via linarith.
    let zero ← realLitExpr 0
    let (residualTy, contradictName) :=
      if sumStrict then
        (``LE.le, ``ProofBrokerMathlib.TermMode.rFarkasContradictNStrict)
      else
        (``LT.lt, ``ProofBrokerMathlib.TermMode.rFarkasContradictN)
    let residualGoalTy ← Lean.Meta.mkAppM residualTy #[zero, sum]
    let residualMV ← Lean.Meta.mkFreshExprMVar residualGoalTy
    let term ← Lean.Meta.mkAppM contradictName
                 #[sum, sumProof, residualMV]
    closeLinarithSubgoal residualMV.mvarId!
    goal.assign term

/-- LRA comparison-goal kinds. Mirror of core's `GoalKind` but
    Real-typed; `≥` and `>` reduce to swapped `≤` and `<` by Lean's
    instance setup for Real, so the matcher swaps operands and feeds
    into the Le / Lt helpers. -/
private inductive RealGoalKind
  | le | lt
deriving Repr

/-- Match a Real comparison goal. Returns `(b, c, kind)` where the
    helper takes `(b, c)` as named args. For `≥` / `>`, the SDK has
    already swapped operands at IR-build time, and Real's instance
    reduction lets `b ≤ a` proof unify with `a ≥ b` goal definitionally
    (same trick the core Int side uses). Eq is not matched here — the
    outer dispatcher handles it via `apply le_antisymm` split. -/
private def matchRealGoal? (goalType : Expr)
    : Option (Expr × Expr × RealGoalKind) :=
  match goalType.getAppFnArgs with
  | (``LE.le, #[α, _, b, c]) =>
    if α.isConstOf ``Real then some (b, c, .le) else none
  | (``LT.lt, #[α, _, b, c]) =>
    if α.isConstOf ``Real then some (b, c, .lt) else none
  | (``GE.ge, #[α, _, a, b]) =>
    -- a ≥ b ≡ b ≤ a
    if α.isConstOf ``Real then some (b, a, .le) else none
  | (``GT.gt, #[α, _, a, b]) =>
    -- a > b ≡ b < a
    if α.isConstOf ``Real then some (b, a, .lt) else none
  | _ => none

/-- Real-typed comparison-goal closer. Mirror of the Rocq
    `close_term_goal` for LRA, with branching on hypothesis
    strictness:
      * Le-goal × Le a1: use `rFarkasGoalLe2` (strict-aware on cng).
      * Le-goal × strict a1: weaken a1 via `rStrictNegToNonpos`,
        then same as above.
      * Lt-goal × Le a1: `rFarkasGoalLt2` (standard, requires hpos
        strict-positive).
      * Lt-goal × strict a1: `rFarkasGoalLt2StrictA1` (strict-aware
        on c1; hpos non-strict-nonneg).
    The `hpos` premise is the polynomial-positivity / non-negativity
    claim closed by linarith on the witness's linear combination. -/
private def closeViaTermModeRealGoal
    (goal : MVarId) (goalType : Expr)
    (realEntry : String × Int) (cng : Int) : TacticM Unit := do
  let (realName, c1) := realEntry
  let (b, c, kind) ← match matchRealGoal? goalType with
    | some t => pure t
    | none =>
      throwError "proof_broker_term: non-False Real goal must have \
                   shape (_ ≤ _) / (_ < _) / (_ ≥ _) / (_ > _); \
                   got {goalType}"
  goal.withContext do
    let (fv, ty) ← fvarOfName realName
    let normHyp ← normalizeHypothesisReal fv ty
    let h1Strict := normHyp.strict
    let a1 := normHyp.expr
    let c1Expr ← realLitExpr c1
    let cngExpr ← realLitExpr cng
    let negGoalNorm ← Lean.Meta.mkAppM ``HSub.hSub #[c, b]
    let prod1 ← Lean.Meta.mkAppM ``HMul.hMul #[c1Expr, a1]
    let prod2 ← Lean.Meta.mkAppM ``HMul.hMul #[cngExpr, negGoalNorm]
    let sum ← Lean.Meta.mkAppM ``HAdd.hAdd #[prod1, prod2]
    let zero ← realLitExpr 0
    -- Dispatch table on (kind, h1Strict):
    -- * (.le, false / true): rFarkasGoalLe2 with (h1, hc1=nonneg,
    --   hcng=pos, hpos=nonneg). h1 weakened from Lt to Le if needed
    --   (information-preserving: strictness in Le-goal comes from
    --   neg_goal's Lt-shape, not a1).
    -- * (.lt, false): rFarkasGoalLt2 with (h1=Le, hc1=nonneg,
    --   hcng=nonneg, hpos=pos).
    -- * (.lt, true): rFarkasGoalLt2StrictA1 with (h1=Lt, hc1=pos,
    --   hcng=nonneg, hpos=nonneg).
    let (helperName, h1, hc1, hcng, hposTyHead) :=
      match kind, h1Strict with
      | .le, false =>
        (``ProofBrokerMathlib.TermMode.rFarkasGoalLe2,
         normHyp.proof,
         (false, c1Expr),   -- 0 ≤ c1
         (true,  cngExpr),  -- 0 < cng
         ``LE.le)            -- 0 ≤ hpos
      | .le, true =>
        -- Weaken h1 from Lt to Le via rStrictNegToNonpos
        let h1' := Expr.app (Expr.app (mkConst ``ProofBrokerMathlib.TermMode.rStrictNegToNonpos)
                                       a1) normHyp.proof
        (``ProofBrokerMathlib.TermMode.rFarkasGoalLe2,
         h1',
         (false, c1Expr),
         (true,  cngExpr),
         ``LE.le)
      | .lt, false =>
        (``ProofBrokerMathlib.TermMode.rFarkasGoalLt2,
         normHyp.proof,
         (false, c1Expr),
         (false, cngExpr),
         ``LT.lt)            -- 0 < hpos
      | .lt, true =>
        (``ProofBrokerMathlib.TermMode.rFarkasGoalLt2StrictA1,
         normHyp.proof,
         (true,  c1Expr),    -- 0 < c1
         (false, cngExpr),
         ``LE.le)            -- 0 ≤ hpos
    let buildCoefProof (s : Bool × Expr) : TacticM Expr :=
      if s.1 then buildPosProofReal s.2 else buildNonnegProofReal s.2
    let hc1Proof ← buildCoefProof hc1
    let hcngProof ← buildCoefProof hcng
    let hposGoalTy ← Lean.Meta.mkAppM hposTyHead #[zero, sum]
    let hposMV ← Lean.Meta.mkFreshExprMVar hposGoalTy
    let term ← Lean.Meta.mkAppM helperName
                 #[h1, hc1Proof, hcngProof, hposMV]
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

/- ============================================================
   Tier 1 LRA closer (top-level dispatcher)

   Called from core's `runTermModeOnGoal` when the cert is a verified
   Tier 1 Farkas witness and the IR's fragment is LRA. Handles both
   False-goal and comparison-goal cases — equality goals are
   pre-split via `apply le_antisymm` in core's `evalProofBrokerTerm`,
   so the closer only sees False / Le / Lt / Ge / Gt shapes here.
   ============================================================ -/

/-- Parse a Tier 1 Farkas cert's `payload.witness_data.coefficients`
    into `(name, coef)` pairs. Mirror of core's `parseFarkasCoefficients`;
    duplicated here because core's version is `private`. -/
private def parseFarkasCoefficientsReal (cert : Json)
    : TacticM (List (String × Int)) := do
  let payload ← match cert.getObjVal? "payload" with
    | .ok j => pure j
    | .error e => throwError "proof_broker_term: cert missing payload: {e}"
  let witnessKind := (payload.getObjValAs? String "witness_kind").toOption.getD ""
  unless witnessKind == "farkas" do
    throwError "proof_broker_term: cert is not a Farkas witness (kind={witnessKind})"
  let witnessData ← match payload.getObjVal? "witness_data" with
    | .ok j => pure j
    | .error e => throwError "proof_broker_term: cert missing witness_data: {e}"
  parseWitnessCoefficients witnessData

/-- Tier 1 LRA closer entry point. Wired into
    `ProofBroker.Tactic.ReifierExt.tier1FarkasCloser` via the
    initialize block below. Dispatches by goal shape:
    * `False`: `closeViaTermModeFalseReal` (strict-aware fold).
    * `_ ≤ _` / `_ < _` / `_ ≥ _` / `_ > _` over `Real`:
      `closeViaTermModeRealGoal` with strict-aware h1 handling.
    * Anything else surfaces a clear error. -/
private def closeViaTermModeReal (cert : Json) (_ir : IR) : TacticM Unit := do
  let entries ← parseFarkasCoefficientsReal cert
  if entries.isEmpty then
    throwError "proof_broker_term: empty witness — arity ≥ 1 required"
  let negEntry := entries.find? (fun e => e.1 == "neg_goal")
  let goal ← getMainGoal
  -- Instantiate mvars: post-`apply le_antisymm`, the subgoal's type
  -- carries the unification mvar for the LE typeclass instance, and
  -- `matchRealGoal?`'s `α.isConstOf ``Real` check fails against the
  -- mvar. The instantiation pins it to `Real`.
  let goalType ← Lean.instantiateMVars (← goal.getType)
  match negEntry with
  | none =>
    unless goalType.isConstOf ``False do
      throwError "proof_broker_term: witness lacks neg_goal but goal is \
                   not False ({goalType}); cert/goal mismatch"
    closeViaTermModeFalseReal goal entries
  | some (_, cng) =>
    if goalType.isConstOf ``False then
      throwError "proof_broker_term: witness names neg_goal but goal is \
                   False; cert/goal mismatch"
    -- Comparison-goal: arity-2 only (one real hypothesis + neg_goal).
    -- Higher arity on non-False goals would need farkasGoalLeN helpers
    -- — out of scope for this iteration (matches the Int side's scope).
    unless entries.length == 2 do
      throwError "proof_broker_term: arity {entries.length} non-False \
                   LRA witness — only arity 2 wired for comparison goals"
    let real := entries.find? (fun e => e.1 != "neg_goal")
    let realEntry ← match real with
      | some e => pure e
      | none =>
        throwError "proof_broker_term: witness has neg_goal but no \
                     real-hypothesis companion (arity-2 expected)"
    closeViaTermModeRealGoal goal goalType realEntry cng

/-- Equality-goal antisym split tactic for LRA. Wired into core's
    `evalProofBrokerTerm` via the `tier1EqSplit` slot. Applies
    Mathlib's generic `le_antisymm`, leaving two `≤` subgoals that
    core dispatches via fresh solver runs. -/
private def lraEqSplit : TacticM Unit := do
  evalTactic (← `(tactic| apply le_antisymm))

initialize do
  ProofBroker.Tactic.reifierExt.set (some {
    reifyType := reifyTypeMathlib,
    freeVarType := freeVarTypeMathlib,
    matchLiteralExt := matchRealLiteral?,
    lraCloser := lraCloseWithLinarith,
    tier2CaseSplitCloser := closeViaCaseSplitReal,
    tier1FarkasCloser := closeViaTermModeReal,
    tier1EqSplit := lraEqSplit,
    irFragment := "LRA",
  })

end ProofBrokerMathlib.Tactic
