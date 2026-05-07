/-
Mathlib-flavored extension to `ProofBroker.Tactic`.

Importing `ProofBrokerMathlib` activates LRA support for the
`proof_broker` tactic without changing its name or surface
syntax: at module init we register a `ProofBroker.Tactic.ReifierExt`
that recognizes `Real` types/literals and discharges
`verifiedFarkas`/`verifiedCaseSplit`/`verifiedTier3` certs over
LRA via Mathlib's `linarith`. With the cert verification gating
the call (the OCaml-side verifier has already accepted the
proof), `linarith` produces an axiom-free proof term — same
contract as `omega` for LIA.

`ProofBroker` (the core lib) is Mathlib-free and stays so:
projects that only need LIA support don't pay the Mathlib build
cost. Importing `ProofBrokerMathlib` is the opt-in.

Scope: `Real` only, with `LE.le` / `LT.lt` / `GE.ge` / `GT.gt` /
`Eq` comparisons, `HAdd` / `HSub` / `HMul` / `Neg.neg` arithmetic,
`OfNat.ofNat` and `OfScientific.ofScientific` literals. `Rat` and
other ordered fields would be additional opt-ins.
-/

import Lean
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import ProofBroker.Tactic

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
          -- m * 10^(-ex) = m / 10^ex (rendered as decimal n/d)
          let denom := 10 ^ ex
          return some (s!"{m}/{denom}", "Real")
        else
          -- m * 10^ex (a plain integer)
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

initialize do
  ProofBroker.Tactic.reifierExt.set (some {
    reifyType := reifyTypeMathlib,
    freeVarType := freeVarTypeMathlib,
    matchLiteralExt := matchRealLiteral?,
    lraCloser := lraCloseWithLinarith,
    irFragment := "LRA",
  })

end ProofBrokerMathlib.Tactic
