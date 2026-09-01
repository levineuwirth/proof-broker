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
import Aesop
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic
import ProofBroker.Tactic
import ProofBrokerMathlib.TermMode
import ProofBrokerMathlib.TermModePoly

namespace ProofBrokerMathlib.Tactic

open Lean Lean.Elab.Tactic Lean.Meta ProofBroker.IR

/- ============================================================
   R3-M2: polymorphic type-variable recognition

   A local `α : Type u` qualifies as the extraction's type variable
   when the three instances the α lift family
   (`ProofBrokerMathlib.TermModePoly`) is stated over are
   synthesizable: `CommRing α`, `LinearOrder α`,
   `IsStrictOrderedRing α` — the modern Mathlib spelling of the
   removed `LinearOrderedCommRing` (delta.md §5). Qualification is
   what justifies the `embeds_into:Int_for_universal_LIA` tag: the
   solver works on the Int image, and the term-mode closer replays
   the cert's coefficients AT α through that family, which is the
   inversion of the recorded α→Int specialization.
   ============================================================ -/

/-- The classes the α lift family requires, in reporting order. -/
private def polyClasses : List Name :=
  [``CommRing, ``LinearOrder, ``IsStrictOrderedRing]

/-- The lift-family lemmas named in the `embedding_witness:` tags —
    the M1 discipline: the witness names exactly what the lift
    applies, each backed by a `library_provenance` entry with a real
    content hash. -/
private def polyLiftWitnessLemmas : List Name :=
  [``ProofBrokerMathlib.TermModePoly.pLeViaLt,
   ``ProofBrokerMathlib.TermModePoly.pLtViaLe,
   ``ProofBrokerMathlib.TermModePoly.pFarkasContradictN,
   ``ProofBrokerMathlib.TermModePoly.pFarkasContradictNStrict]

/-- Try to synthesize `c α`; `none` on elaboration or synthesis
    failure (e.g. `IsStrictOrderedRing α`'s own instance-implicit
    `Semiring`/`PartialOrder` arguments missing). The application is
    SATURATED to the class's full arity (`mkAppOptM` with `none` for
    every trailing argument, so mixin classes' own instance args are
    synthesized too — `mkAppM` would leave them un-applied and hand
    `synthInstance?` a Pi type). -/
private def polySynthClass? (c : Name) (α : Expr) : MetaM (Option Expr) := do
  try
    let cinfo ← Lean.getConstInfo c
    let arity ← Lean.Meta.forallTelescopeReducing cinfo.type
      fun xs _ => pure xs.size
    if arity == 0 then return none
    let args := #[some α] ++ Array.replicate (arity - 1) none
    let clsTy ← Lean.Meta.mkAppOptM c args
    Lean.Meta.synthInstance? clsTy
  catch _ => return none

/-- Is `ty` a local type variable qualified for the α lift? -/
private def polyQualifiedFVar (ty : Expr) : MetaM Bool := do
  unless ty.isFVar do return false
  let sortTy ← Lean.Meta.whnf (← Lean.Meta.inferType ty)
  unless sortTy.isSort && !sortTy.isProp do return false
  for c in polyClasses do
    if (← polySynthClass? c ty).isNone then return false
  return true

/-- Build the `type_variable`-kind metadata + provenance for a
    qualified `α` (see `ProofBroker.Tactic.TypeVarInfo`). One
    `Instance` entry per required class, each with a real content
    hash of the class's type signature; the embed +
    `embedding_witness:` tags ride on the last (ordered-ring) entry
    and name the `TermModePoly` lift family. -/
private def typeVarInfoMathlib (α : Expr)
    : MetaM (Option ProofBroker.Tactic.TypeVarInfo) := do
  unless ← polyQualifiedFVar α do return none
  let env ← Lean.getEnv
  let classHash (c : Name) : MetaM String := do
    let some info := env.find? c
      | throwError "proof_broker: class {c} not found"
    let stmt ← Lean.Meta.ppExpr info.type
    match ProofBroker.runContentHash (toString stmt) with
    | .ok h => pure h
    | .error e =>
      throwError "proof_broker: content_hash FFI failed: {repr e}"
  let tags : Array Json :=
    #[Json.str "embeds_into:Int_for_universal_LIA"]
    ++ polyLiftWitnessLemmas.toArray.map
         (fun n => Json.str s!"embedding_witness:{n}")
  let mut instances : Array Json := #[]
  for c in polyClasses do
    let base := [
      ("instance_name", Json.str s!"inst_{c.toString}_alpha"),
      ("class", Json.mkObj [
        ("name", Json.str c.toString),
        ("library", Json.str "mathlib"),
        ("library_version", Json.str Lean.versionString),
        ("content_hash", Json.str (← classHash c))])]
    let entry :=
      if c == polyClasses.getLast! then
        Json.mkObj (base ++ [("theory_classification_tags", Json.arr tags)])
      else Json.mkObj base
    instances := instances.push entry
  let metadata := Json.mkObj [
    ("kind", "type_variable"),
    ("name", Json.str ProofBroker.Tactic.Reify.polyTypeVarName),
    ("kind_class", "Type"),
    ("instances", Json.arr instances)]
  let provenance ← polyLiftWitnessLemmas.mapM
    (ProofBroker.Tactic.Reify.witnessProvenance "proof-broker-bridge")
  return some { metadata, provenance }

/-- Decode an LRA-eligible type — `Real` — or (R3-M2) a qualified
    polymorphic type variable, reified at the canonical tag
    `"alpha"`. -/
private def reifyTypeMathlib (ty : Expr) : MetaM (Option ProofBroker.IR.TypeRef) := do
  if ty.isConstOf ``Real then return some "Real"
  if ← polyQualifiedFVar ty then
    return some ProofBroker.Tactic.Reify.polyTypeVarName
  return none

/-- The `buildIR` LCtx-walk recognizer for extension-typed DATA
    locals. `Real` only: α-typed locals are claimed by core's
    poly-mode branch (which runs first), so claiming them here too
    would only mislabel the fragment. -/
private def freeVarTypeMathlib (ty : Expr) : MetaM (Option ProofBroker.IR.TypeRef) := do
  if ty.isConstOf ``Real then return some "Real"
  return none

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
    -- R3-M2: an `OfNat` literal at a qualified type variable
    -- (`(10 : α)`) reifies at the canonical "alpha" tag; the SDK
    -- refinement substitutes it to Int with the rest.
    else if ← polyQualifiedFVar α then
      match n.rawNatLit? with
      | some k =>
        return some (toString k, ProofBroker.Tactic.Reify.polyTypeVarName)
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

/-- Detect a Real Eq hypothesis: `h : a = b` with `a b : Real`.
    Used by the closer to permit signed coefficients on Eq while
    keeping the positive-coefficient invariant on inequalities. -/
private def matchRealEqHyp? (ty : Expr) : Option (Expr × Expr) :=
  match ty.getAppFnArgs with
  | (``Eq, #[α, a, b]) =>
    if α.isConstOf ``Real then some (a, b) else none
  | _ => none

/-- Detect a Real Not-hypothesis: `h : ¬(a <op> b)` for
    `<op> ∈ {≤, ≥, <, >}`. Returns the inner kind + operands. -/
private def matchRealNotBound? (ty : Expr) : Option (HypKindReal × Expr × Expr) :=
  match ty.getAppFnArgs with
  | (``Not, #[inner]) =>
    match inner.getAppFnArgs with
    | (``LE.le, #[α, _, a, b]) =>
      if α.isConstOf ``Real then some (.le, a, b) else none
    | (``GE.ge, #[α, _, a, b]) =>
      if α.isConstOf ``Real then some (.ge, a, b) else none
    | (``LT.lt, #[α, _, a, b]) =>
      if α.isConstOf ``Real then some (.lt, a, b) else none
    | (``GT.gt, #[α, _, a, b]) =>
      if α.isConstOf ``Real then some (.gt, a, b) else none
    | _ => none
  | _ => none

/-- Real-typed `normalizeHypothesis`: from `(h : a ≤ b : Real)` /
    `(h : a ≥ b : Real)` / `(h : a < b : Real)` / `(h : a > b : Real)` /
    `(h : a = b : Real)` build a `NormalizedHypReal`. Strict shapes
    go through `rLtToLt0` / `rGtToLt0` (no LIA +1 trick over R — the
    strict-aware fold path consumes the `a < 0` proof directly).
    Eq hypotheses normalize via `rEqToLe0` (or `rEqToLe0Flipped`
    for negative coefficients) — `strict = false` since `a = b →
    a - b = 0 ≤ 0`. -/
private def normalizeHypothesisReal (hypFV : Expr) (hypTy : Expr)
    (flipped : Bool) : MetaM NormalizedHypReal := do
  match matchRealEqHyp? hypTy with
  | some (a, b) =>
    if flipped then
      let expr ← Lean.Meta.mkAppM ``HSub.hSub #[b, a]
      let proof ← Lean.Meta.mkAppM
                    ``ProofBrokerMathlib.TermMode.rEqToLe0Flipped #[hypFV]
      return ⟨expr, proof, false⟩
    else
      let expr ← Lean.Meta.mkAppM ``HSub.hSub #[a, b]
      let proof ← Lean.Meta.mkAppM
                    ``ProofBrokerMathlib.TermMode.rEqToLe0 #[hypFV]
      return ⟨expr, proof, false⟩
  | none =>
  match matchRealNotBound? hypTy with
  | some (.le, a, b) =>
    -- ¬(a ≤ b) → b < a → b - a < 0 (strict over R; no +1 trick).
    let expr ← Lean.Meta.mkAppM ``HSub.hSub #[b, a]
    let proof ← Lean.Meta.mkAppM
                  ``ProofBrokerMathlib.TermMode.rNotLeToLt0 #[hypFV]
    return ⟨expr, proof, true⟩
  | some (.ge, a, b) =>
    -- ¬(a ≥ b) → a < b → a - b < 0 (strict).
    let expr ← Lean.Meta.mkAppM ``HSub.hSub #[a, b]
    let proof ← Lean.Meta.mkAppM
                  ``ProofBrokerMathlib.TermMode.rNotGeToLt0 #[hypFV]
    return ⟨expr, proof, true⟩
  | some (.lt, a, b) =>
    -- ¬(a < b) → b ≤ a → b - a ≤ 0 (loose).
    let expr ← Lean.Meta.mkAppM ``HSub.hSub #[b, a]
    let proof ← Lean.Meta.mkAppM
                  ``ProofBrokerMathlib.TermMode.rNotLtToLe0 #[hypFV]
    return ⟨expr, proof, false⟩
  | some (.gt, a, b) =>
    -- ¬(a > b) → a ≤ b → a - b ≤ 0 (loose).
    let expr ← Lean.Meta.mkAppM ``HSub.hSub #[a, b]
    let proof ← Lean.Meta.mkAppM
                  ``ProofBrokerMathlib.TermMode.rNotGtToLe0 #[hypFV]
    return ⟨expr, proof, false⟩
  | none =>
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
    throwError "proof_broker_term: hypothesis shape outside Real ≤/≥/</>/= \
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
    -- Pre-process: drop zero-coefficient entries, split signed
    -- coefficients into (|c|, flipped). [flipped=true] is sound only
    -- on Eq hypotheses (Real Eq accepts signed coefs in the Farkas
    -- sum because [c * 0 = 0] regardless of sign); inequality
    -- hypotheses with c < 0 surface a clear error.
    let stepped ← entries.mapM fun (name, c) => do
      if c == 0 then return none
      let (fv, ty) ← resolve name
      let isEq := (matchRealEqHyp? ty).isSome
      let flipped : Bool := decide (c < 0)
      if flipped && !isEq then
        throwError "proof_broker_term: negative coefficient {c} on \
                     non-Eq Real hypothesis '{name}' — SDK verifier \
                     should have rejected this cert"
      let cAbs := if flipped then -c else c
      return some (name, fv, ty, cAbs, flipped)
    let processed := stepped.filterMap id
    if processed.isEmpty then
      throwError "proof_broker_term: all coefficients are zero — \
                   need at least one nonzero entry"
    -- Normalize each entry. Builds (cExpr, hc_proof, expr, h_proof, strict)
    -- per entry — hc is strict (0 < c) if the premise is strict (Lt),
    -- non-strict (0 ≤ c) otherwise. Strict premise + strict coef →
    -- product is strict via rMulPosNeg.
    let normalized ← processed.mapM fun (_name, fv, ty, c, flipped) => do
      let normHyp ← normalizeHypothesisReal fv ty flipped
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

/-- Parse a coefficient string into `(numerator, denominator)`.
    Mirror of core's `parseRatString` — duplicated because both are
    `private` to their namespaces. -/
private def parseRatStringReal (s : String) : Option (Int × Int) :=
  match s.splitOn "/" with
  | [n] =>
    match n.toInt? with
    | some i => some (i, 1)
    | none => none
  | [n, d] =>
    match n.toInt?, d.toInt? with
    | some i, some j =>
      if j == 0 then none
      else if j < 0 then some (-i, -j)
      else some (i, j)
    | _, _ => none
  | _ => none

/-- Clear denominators across a list of `(label, num, den)` entries.
    Mirror of core's `clearDenominators`. The scaled coefficients
    flow into the strict-aware fold's product / sum chain and into
    `linarith`-discharged residual subgoal — `linarith` over `Real`
    handles integer-scaled rationals identically to the original
    rational form, so the trust footprint is unchanged. -/
private def clearDenominatorsReal
    (entries : List (String × Int × Int)) : List (String × Int) :=
  let lcdNat : Nat :=
    entries.foldl (fun acc (_, _, d) => Nat.lcm acc d.natAbs) 1
  let lcd : Int := lcdNat
  entries.map fun (name, n, d) => (name, n * (lcd / d))

/-- Parse a Farkas witness JSON into a coefficient list. Mirror
    of core's `parseFarkasCoefficients` but takes the witness
    directly (already pulled out of the Tier 2 lemma). Solver-
    emitted rational coefficients (cvc5/z3 routinely emit `1/2`-
    style coefficients over LRA) are normalized to integers via
    LCM-of-denominators scaling, preserving the contradiction
    structure of the Farkas combination. -/
private def parseWitnessCoefficients (witness : Json)
    : TacticM (List (String × Int)) := do
  let arr ← match witness.getObjVal? "coefficients" >>= (·.getArr?) with
    | .ok a => pure a
    | .error e => throwError "proof_broker_term: witness coefficients not array: {e}"
  let rats ← arr.toList.mapM fun entry => do
    let name := (entry.getObjValAs? String "hypothesis").toOption.getD ""
    let coefStr := (entry.getObjValAs? String "coefficient").toOption.getD ""
    if name == "" then throwError "proof_broker_term: witness entry missing hypothesis"
    match parseRatStringReal coefStr with
    | some (n, d) => pure (name, n, d)
    | none =>
      throwError "proof_broker_term: malformed coefficient '{coefStr}' \
                   (expected integer or n/d)"
  pure (clearDenominatorsReal rats)

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
  -- Flatten nested binary `Or` into a flat disjunct list. Mirror
  -- of the SDK's [Alethe_farkas.disjuncts_of]. Right-associated
  -- nesting `A ∨ (B ∨ C)` flattens to `[A; B; C]`.
  let rec flattenDisjuncts (s : ShellTerm) : List ShellTerm :=
    match s with
    | .or_ l r => flattenDisjuncts l ++ flattenDisjuncts r
    | _ => [s]
  let disjuncts := flattenDisjuncts disjHyp.shell
  let nDisjuncts := disjuncts.length
  if nDisjuncts < 2 then
    throwError "proof_broker_term: disjunctive hypothesis '{hypName}' \
                 has {nDisjuncts} disjuncts (expected ≥ 2)"
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
  let perDisjunctEntries ← disjuncts.mapM findLemma
  -- Build an arity-N rcases tactic dynamically. Each leaf disjunct
  -- gets the same name `hCase` (rcases binds it per-branch in the
  -- corresponding subgoal); rcases handles the right-associated `Or`
  -- nesting via its `|`-separated pattern from `Init/RCases.lean`'s
  -- `rcasesPatMed := sepBy1(rcasesPat, " | ")` grammar. The
  -- `$[$pats]|*` splice form is the direct way to feed a runtime-
  -- sized array of patterns into the `|`-separated sepBy1 without
  -- a string + parser round-trip.
  let pats : Array (TSyntax `rcasesPat) ←
    (List.replicate nDisjuncts ()).toArray.mapM (fun _ =>
      `(rcasesPat| hCase))
  let hypIdent := mkIdent hypName.toName
  let stx ← `(tactic| rcases $hypIdent:term with $[$pats]|*)
  let mainGoal ← getMainGoal
  mainGoal.withContext do
    let _ ← match (← getLCtx).findFromUserName? hypName.toName with
      | some d => pure (Expr.fvar d.fvarId)
      | none =>
        throwError "proof_broker_term: disjunctive hypothesis '{hypName}' \
                     not in Lean LCtx (IR vs Lean context drift?)"
    evalTactic stx
  -- N subgoals now; dispatch each to closeViaTermModeFalseReal with
  -- the "case" name overridden to the destruct-bound hCase. Subgoal
  -- ordering follows rcases's left-to-right traversal, which matches
  -- the disjunct order produced by `flattenDisjuncts`.
  let subgoals ← getGoals
  if subgoals.length != nDisjuncts then
    throwError "proof_broker_term: rcases produced {subgoals.length} \
                 subgoals (expected {nDisjuncts} for arity-{nDisjuncts} \
                 case-split)"
  let runBranch (g : MVarId) (entries : List (String × Int)) : TacticM Unit := do
    setGoals [g]
    g.withContext do
      let (hCaseFV, hCaseTy) ← fvarOfName "hCase"
      closeViaTermModeFalseReal g entries [("case", hCaseFV, hCaseTy)]
  for (g, entries) in subgoals.zip perDisjunctEntries do
    runBranch g entries
  setGoals []

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

/-- Unified arity-N comparison-goal closer (LRA). Converts `b ≤ c` /
    `b < c` (and their `≥` / `>` swapped forms) over `Real` to
    `False` by applying a wrapper of shape
    `(c <(=) b → False) → b <(=) c`, introducing `neg_goal` as a
    regular hypothesis, and delegating to `closeViaTermModeFalseReal`.
    The arity-N strict-aware fold handles all premises — including
    `neg_goal` whose strict (Le-goal) or non-strict (Lt-goal)
    normalization threads through naturally. -/
private def closeViaTermModeRealComparison
    (goal : MVarId) (goalType : Expr)
    (entries : List (String × Int)) : TacticM Unit := do
  let (b, c, kind) ← match matchRealGoal? goalType with
    | some t => pure t
    | none =>
      throwError "proof_broker_term: non-False Real goal must have \
                   shape (_ ≤ _) / (_ < _) / (_ ≥ _) / (_ > _); \
                   got {goalType}"
  let (wrapperName, negHead) := match kind with
    | .le => (``ProofBrokerMathlib.TermMode.rLeViaLt, ``LT.lt)
    | .lt => (``ProofBrokerMathlib.TermMode.rLtViaLe, ``LE.le)
  let bodyMV ← goal.withContext do
    let negTy ← Lean.Meta.mkAppM negHead #[c, b]
    let bodyTy ← mkArrow negTy (mkConst ``False)
    let bodyMV ← Lean.Meta.mkFreshExprMVar bodyTy
    let term ← Lean.Meta.mkAppOptM wrapperName
                 #[some b, some c, some bodyMV]
    goal.assign term
    return bodyMV
  let (_, newGoal) ← bodyMV.mvarId!.intro `neg_goal
  closeViaTermModeFalseReal newGoal entries

/-- Tier 1 LRA closer entry point. Wired into
    `ProofBroker.Tactic.ReifierExt.tier1FarkasCloser` via the
    initialize block below. Dispatches by goal shape:
    * `False`: `closeViaTermModeFalseReal` (strict-aware fold).
    * `_ ≤ _` / `_ < _` / `_ ≥ _` / `_ > _` over `Real`:
      `closeViaTermModeRealComparison` (unified arity-N path).
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
  | some _ =>
    if goalType.isConstOf ``False then
      throwError "proof_broker_term: witness names neg_goal but goal is \
                   False; cert/goal mismatch"
    closeViaTermModeRealComparison goal goalType entries

/-- Equality-goal antisym split tactic for LRA. Wired into core's
    `evalProofBrokerTerm` via the `tier1EqSplit` slot. Applies
    Mathlib's generic `le_antisymm`, leaving two `≤` subgoals that
    core dispatches via fresh solver runs. R3-M2: also serves the
    polymorphic-α equality split (`le_antisymm` is the `PartialOrder`
    generic, so it applies at any qualified α). -/
private def lraEqSplit : TacticM Unit := do
  evalTactic (← `(tactic| apply le_antisymm))

/- ============================================================
   R3-M2: Tier 1 α term-mode closer — the α lift.

   Mirror of the LRA closer above, over a qualified type variable
   instead of `Real`. The cert's Farkas coefficients (found by the
   solver on the Int image of the goal) are replayed AT α through
   `ProofBrokerMathlib.TermModePoly` — this replay is what makes the
   cert's recorded α→Int `type_specialization` invertible. Like the
   Real fold (and unlike the Int one), the α fold is
   strictness-preserving and never applies the LIA +1 trick: α may
   be dense, so a witness whose contradiction needs integrality
   fails the replay's residual check — a tactic failure, never an
   unsound closure. The residual (`0 < s` / `0 ≤ s` for the
   literal-coefficient combination `s`, a ring identity when the
   witness is α-valid) is discharged by `ring_nf` + `norm_num`.
   ============================================================ -/

/-- Recognize an α comparison shape (α = a qualified type-variable
    fvar) in a hypothesis type. -/
private def matchPolyBound? (ty : Expr)
    : MetaM (Option (HypKindReal × Expr × Expr)) := do
  match ty.getAppFnArgs with
  | (``LE.le, #[α, _, a, b]) =>
    if ← polyQualifiedFVar α then return some (.le, a, b) else return none
  | (``GE.ge, #[α, _, a, b]) =>
    if ← polyQualifiedFVar α then return some (.ge, a, b) else return none
  | (``LT.lt, #[α, _, a, b]) =>
    if ← polyQualifiedFVar α then return some (.lt, a, b) else return none
  | (``GT.gt, #[α, _, a, b]) =>
    if ← polyQualifiedFVar α then return some (.gt, a, b) else return none
  | _ => return none

/-- Detect an α Eq hypothesis (signed coefficients permitted). -/
private def matchPolyEqHyp? (ty : Expr) : MetaM (Option (Expr × Expr)) := do
  match ty.getAppFnArgs with
  | (``Eq, #[α, a, b]) =>
    if ← polyQualifiedFVar α then return some (a, b) else return none
  | _ => return none

/-- Detect an α Not-hypothesis `¬(a <op> b)`. -/
private def matchPolyNotBound? (ty : Expr)
    : MetaM (Option (HypKindReal × Expr × Expr)) := do
  match ty.getAppFnArgs with
  | (``Not, #[inner]) => matchPolyBound? inner
  | _ => return none

/-- α-typed `normalizeHypothesis`: strict shapes stay strict (no +1
    trick — see the section note), Eq flips on negative coefficients.
    Mirrors `normalizeHypothesisReal` with the `TermModePoly` family. -/
private def normalizeHypothesisPoly (hypFV : Expr) (hypTy : Expr)
    (flipped : Bool) : MetaM NormalizedHypReal := do
  match ← matchPolyEqHyp? hypTy with
  | some (a, b) =>
    if flipped then
      let expr ← Lean.Meta.mkAppM ``HSub.hSub #[b, a]
      let proof ← Lean.Meta.mkAppM
                    ``ProofBrokerMathlib.TermModePoly.pEqToLe0Flipped #[hypFV]
      return ⟨expr, proof, false⟩
    else
      let expr ← Lean.Meta.mkAppM ``HSub.hSub #[a, b]
      let proof ← Lean.Meta.mkAppM
                    ``ProofBrokerMathlib.TermModePoly.pEqToLe0 #[hypFV]
      return ⟨expr, proof, false⟩
  | none =>
  match ← matchPolyNotBound? hypTy with
  | some (.le, a, b) =>
    let expr ← Lean.Meta.mkAppM ``HSub.hSub #[b, a]
    let proof ← Lean.Meta.mkAppM
                  ``ProofBrokerMathlib.TermModePoly.pNotLeToLt0 #[hypFV]
    return ⟨expr, proof, true⟩
  | some (.ge, a, b) =>
    let expr ← Lean.Meta.mkAppM ``HSub.hSub #[a, b]
    let proof ← Lean.Meta.mkAppM
                  ``ProofBrokerMathlib.TermModePoly.pNotGeToLt0 #[hypFV]
    return ⟨expr, proof, true⟩
  | some (.lt, a, b) =>
    let expr ← Lean.Meta.mkAppM ``HSub.hSub #[b, a]
    let proof ← Lean.Meta.mkAppM
                  ``ProofBrokerMathlib.TermModePoly.pNotLtToLe0 #[hypFV]
    return ⟨expr, proof, false⟩
  | some (.gt, a, b) =>
    let expr ← Lean.Meta.mkAppM ``HSub.hSub #[a, b]
    let proof ← Lean.Meta.mkAppM
                  ``ProofBrokerMathlib.TermModePoly.pNotGtToLe0 #[hypFV]
    return ⟨expr, proof, false⟩
  | none =>
  match ← matchPolyBound? hypTy with
  | some (.le, a, b) =>
    let expr ← Lean.Meta.mkAppM ``HSub.hSub #[a, b]
    let proof ← Lean.Meta.mkAppM
                  ``ProofBrokerMathlib.TermModePoly.pLeToLe0 #[hypFV]
    return ⟨expr, proof, false⟩
  | some (.ge, a, b) =>
    let expr ← Lean.Meta.mkAppM ``HSub.hSub #[b, a]
    let proof ← Lean.Meta.mkAppM
                  ``ProofBrokerMathlib.TermModePoly.pGeToLe0 #[hypFV]
    return ⟨expr, proof, false⟩
  | some (.lt, a, b) =>
    let expr ← Lean.Meta.mkAppM ``HSub.hSub #[a, b]
    let proof ← Lean.Meta.mkAppM
                  ``ProofBrokerMathlib.TermModePoly.pLtToLt0 #[hypFV]
    return ⟨expr, proof, true⟩
  | some (.gt, a, b) =>
    let expr ← Lean.Meta.mkAppM ``HSub.hSub #[b, a]
    let proof ← Lean.Meta.mkAppM
                  ``ProofBrokerMathlib.TermModePoly.pGtToLt0 #[hypFV]
    return ⟨expr, proof, true⟩
  | _ =>
    throwError "proof_broker_term: hypothesis shape outside α ≤/≥/</>/= \
                 (got type {hypTy})"

/-- Build an α literal Expr for a nonnegative Int via `OfNat.ofNat`
    with instance synthesis at the extraction's α. -/
private def polyLitExpr (αE : Expr) (c : Int) : MetaM Expr := do
  if c < 0 then
    throwError "proof_broker_term: negative α coefficient {c}"
  Lean.Meta.mkAppOptM ``OfNat.ofNat #[some αE, some (mkNatLit c.toNat), none]

/-- Discharge a residual subgoal (`0 ≤ c` / `0 < c` for a literal, or
    the fold's ring-identity positivity claim) in isolation:
    `ring_nf` normalizes the literal-coefficient combination, then
    `norm_num` decides the numeral (in)equality; `done` makes an
    undischarged residual a hard failure — this is exactly where an
    Int-only (integrality-dependent) witness fails the α replay. -/
private def closePolyResidual (mv : MVarId) : TacticM Unit := do
  let prevGoals ← getGoals
  setGoals [mv]
  evalTactic (← `(tactic| ((try ring_nf) <;> norm_num) <;> done))
  setGoals prevGoals

/-- Proof of `(0 : α) ≤ c` for a literal `c`. -/
private def buildNonnegProofPoly (αE cExpr : Expr) : TacticM Expr := do
  let zero ← polyLitExpr αE 0
  let goalTy ← Lean.Meta.mkAppM ``LE.le #[zero, cExpr]
  let mv ← Lean.Meta.mkFreshExprMVar goalTy
  closePolyResidual mv.mvarId!
  Lean.instantiateMVars mv

/-- Proof of `(0 : α) < c` for a strictly-positive literal `c`. -/
private def buildPosProofPoly (αE cExpr : Expr) : TacticM Expr := do
  let zero ← polyLitExpr αE 0
  let goalTy ← Lean.Meta.mkAppM ``LT.lt #[zero, cExpr]
  let mv ← Lean.Meta.mkFreshExprMVar goalTy
  closePolyResidual mv.mvarId!
  Lean.instantiateMVars mv

/-- α-typed False-goal closer: the strict-aware arity-N fold over
    the witness entries, mirror of `closeViaTermModeFalseReal` with
    the `TermModePoly` combinators. -/
private def closeViaTermModeFalsePoly
    (goal : MVarId) (entries : List (String × Int)) : TacticM Unit := do
  if entries.isEmpty then
    throwError "proof_broker_term: empty witness — arity ≥ 1 required"
  goal.withContext do
    let stepped ← entries.mapM fun (name, c) => do
      if c == 0 then return none
      let (fv, ty) ← fvarOfName name
      let isEq := (← matchPolyEqHyp? ty).isSome
      let flipped : Bool := decide (c < 0)
      if flipped && !isEq then
        throwError "proof_broker_term: negative coefficient {c} on \
                     non-Eq α hypothesis '{name}' — SDK verifier \
                     should have rejected this cert"
      let cAbs := if flipped then -c else c
      return some (name, fv, ty, cAbs, flipped)
    let processed := stepped.filterMap id
    if processed.isEmpty then
      throwError "proof_broker_term: all coefficients are zero — \
                   need at least one nonzero entry"
    let normalized ← processed.mapM fun (_name, fv, ty, c, flipped) => do
      let normHyp ← normalizeHypothesisPoly fv ty flipped
      return (c, normHyp)
    -- The carrier: every normalized form is α-typed.
    let αE ← match normalized with
      | [] => throwError "proof_broker_term: empty fold (internal)"
      | (_, h0) :: _ => Lean.Meta.inferType h0.expr
    let products ← normalized.mapM fun (c, normHyp) => do
      let cExpr ← polyLitExpr αE c
      let hc ← if normHyp.strict then buildPosProofPoly αE cExpr
               else buildNonnegProofPoly αE cExpr
      let prod ← Lean.Meta.mkAppM ``HMul.hMul #[cExpr, normHyp.expr]
      let proof ←
        if normHyp.strict then
          Lean.Meta.mkAppM
            ``ProofBrokerMathlib.TermModePoly.pMulPosNeg #[hc, normHyp.proof]
        else
          Lean.Meta.mkAppM ``mul_nonpos_of_nonneg_of_nonpos
            #[hc, normHyp.proof]
      return (prod, proof, normHyp.strict)
    let pickAdd (accStrict prodStrict : Bool) : Name :=
      match accStrict, prodStrict with
      | false, false => ``add_nonpos
      | false, true  => ``ProofBrokerMathlib.TermModePoly.pAddLeLt
      | true,  false => ``ProofBrokerMathlib.TermModePoly.pAddLtLe
      | true,  true  => ``ProofBrokerMathlib.TermModePoly.pAddNeg
    let (sum, sumProof, sumStrict) ← match products with
      | [] => throwError "proof_broker_term: empty fold (internal)"
      | (p0, h0, s0) :: rest =>
        rest.foldlM (fun (accE, accH, accS) (p, h, ps) => do
          let newSum ← Lean.Meta.mkAppM ``HAdd.hAdd #[accE, p]
          let newProof ← Lean.Meta.mkAppM (pickAdd accS ps) #[accH, h]
          return (newSum, newProof, accS || ps)) (p0, h0, s0)
    let zero ← polyLitExpr αE 0
    let (residualTy, contradictName) :=
      if sumStrict then
        (``LE.le,
         ``ProofBrokerMathlib.TermModePoly.pFarkasContradictNStrict)
      else
        (``LT.lt, ``ProofBrokerMathlib.TermModePoly.pFarkasContradictN)
    let residualGoalTy ← Lean.Meta.mkAppM residualTy #[zero, sum]
    let residualMV ← Lean.Meta.mkFreshExprMVar residualGoalTy
    let term ← Lean.Meta.mkAppM contradictName
                 #[sum, sumProof, residualMV]
    closePolyResidual residualMV.mvarId!
    goal.assign term

/-- Match an α comparison goal (`≥`/`>` reduce to swapped `≤`/`<` by
    instance reduction, as on the Real path). -/
private def matchPolyGoal? (goalType : Expr)
    : MetaM (Option (Expr × Expr × RealGoalKind)) := do
  match goalType.getAppFnArgs with
  | (``LE.le, #[α, _, b, c]) =>
    if ← polyQualifiedFVar α then return some (b, c, .le) else return none
  | (``LT.lt, #[α, _, b, c]) =>
    if ← polyQualifiedFVar α then return some (b, c, .lt) else return none
  | (``GE.ge, #[α, _, a, b]) =>
    if ← polyQualifiedFVar α then return some (b, a, .le) else return none
  | (``GT.gt, #[α, _, a, b]) =>
    if ← polyQualifiedFVar α then return some (b, a, .lt) else return none
  | _ => return none

/-- α comparison-goal closer: `pLeViaLt`/`pLtViaLe` (decidable at α),
    introduce `neg_goal`, delegate to the strict-aware False-fold. -/
private def closeViaTermModePolyComparison
    (goal : MVarId) (goalType : Expr)
    (entries : List (String × Int)) : TacticM Unit := do
  let (b, c, kind) ← match ← matchPolyGoal? goalType with
    | some t => pure t
    | none =>
      throwError "proof_broker_term: non-False α goal must have \
                   shape (_ ≤ _) / (_ < _) / (_ ≥ _) / (_ > _); \
                   got {goalType}"
  let (wrapperName, negHead) := match kind with
    | .le => (``ProofBrokerMathlib.TermModePoly.pLeViaLt, ``LT.lt)
    | .lt => (``ProofBrokerMathlib.TermModePoly.pLtViaLe, ``LE.le)
  let bodyMV ← goal.withContext do
    let negTy ← Lean.Meta.mkAppM negHead #[c, b]
    let bodyTy ← mkArrow negTy (mkConst ``False)
    let bodyMV ← Lean.Meta.mkFreshExprMVar bodyTy
    let term ← Lean.Meta.mkAppM wrapperName #[bodyMV]
    goal.assign term
    return bodyMV
  let (_, newGoal) ← bodyMV.mvarId!.intro `neg_goal
  closeViaTermModeFalsePoly newGoal entries

/-- Tier 1 α closer entry point. Wired into
    `ProofBroker.Tactic.ReifierExt.polyFarkasCloser`. Dispatches by
    goal shape; equality goals were pre-split by core via
    `tier1EqSplit` (`le_antisymm` applies at α). -/
private def closeViaTermModePoly (cert : Json) (_ir : IR) : TacticM Unit := do
  let entries ← parseFarkasCoefficientsReal cert
  if entries.isEmpty then
    throwError "proof_broker_term: empty witness — arity ≥ 1 required"
  let negEntry := entries.find? (fun e => e.1 == "neg_goal")
  let goal ← getMainGoal
  let goalType ← Lean.instantiateMVars (← goal.getType)
  match negEntry with
  | none =>
    unless goalType.isConstOf ``False do
      throwError "proof_broker_term: witness lacks neg_goal but goal is \
                   not False ({goalType}); cert/goal mismatch"
    closeViaTermModeFalsePoly goal entries
  | some _ =>
    if goalType.isConstOf ``False then
      throwError "proof_broker_term: witness names neg_goal but goal is \
                   False; cert/goal mismatch"
    closeViaTermModePolyComparison goal goalType entries

/-- Higher-order / FOL closer for a Vampire-certified goal
    (`verifiedTier3Provenance` Tier-3 TSTP, or Tier-0 oracle). The
    OCaml `Tier3_tptp` provenance gate (or Vampire's SZS Theorem)
    has already established the goal is provable from its
    hypotheses; `aesop` re-derives a Lean kernel proof term —
    introducing equations, applying hypotheses, unfolding
    `Function.comp` etc. — so closure is axiom-free (the cert
    never enters the trust footprint; audit H1). `aesop` itself
    only ever pulls the documented core axioms (`propext`,
    `Classical.choice`, `Quot.sound`), already in the allowlist.
    If `aesop` cannot discharge the certified goal it `throwError`s
    (it does not admit) — propagated as a tactic failure, never an
    axiom. -/
private def holCloseWithAesop : TacticM Unit := do
  evalTactic (← `(tactic|
    first
    | aesop
    | (subst_eqs; aesop)
    | (simp only [Function.comp]; aesop)
    | simp_all [Function.comp]))

/-- TEST-ONLY tactic pinning the α replay's fail-closed behavior on
    Int-only witnesses, independent of live solver output (which
    cannot be committed: a goal whose only witness is
    integrality-dependent is unprovable at a generic α, so a live
    negative test could never close its goal honestly). The string
    is a Farkas `witness_data` JSON; the tactic wraps it as a
    synthetic Tier-1 cert payload and drives the REAL α closer
    (`closeViaTermModePoly`) against the current goal. A witness
    whose strictness-preserving α residual is false makes the closer
    fail — the M2 soundness contract. -/
syntax (name := polyReplayTest) "poly_replay_test" str : tactic

@[tactic polyReplayTest]
def evalPolyReplayTest : Tactic := fun stx => do
  match stx with
  | `(tactic| poly_replay_test $s:str) =>
    let witness ← match Json.parse s.getString with
      | .ok j => pure j
      | .error e => throwError "poly_replay_test: witness parse error: {e}"
    let cert := Json.mkObj [
      ("payload", Json.mkObj [
        ("witness_kind", "farkas"),
        ("witness_data", witness)])]
    let dummyIr : IR := {
      irVersion := "1.0",
      sourceSystem := { name := "lean", version := "0.0" },
      tier := "structural",
      logicClassification := {
        order := "first_order", featuresUsed := [],
        firstOrderFragment := "none", decidableTheory := none },
      goal := { shell := .const "False", payloads := none },
      context := { typeVars := [ProofBroker.Tactic.Reify.polyTypeVarName],
                   freeVars := [], hypotheses := [], librarySlice := none },
      typeMetadata := [], definitionalMetadata := [],
      libraryProvenance := [], userDirectives := none }
    closeViaTermModePoly cert dummyIr
  | _ => throwError "poly_replay_test: malformed invocation"

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
    typeVarInfo? := typeVarInfoMathlib,
    polyFarkasCloser := closeViaTermModePoly,
    holCloser := holCloseWithAesop,
  })

end ProofBrokerMathlib.Tactic
