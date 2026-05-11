/-
Real-typed (LRA) Tier 1 Farkas reconstruction helpers, Mathlib-side
mirror of `ProofBroker.TermMode` (which covers `Int`).

These power the Tier 2 case-split term-mode closer: each branch's
proof term is `rFarkasContradict` applied to the matching lemma's
Farkas coefficients, with the case hypothesis introduced by Lean's
`Or.elim` / `rcases` flowing through as the second `≤ 0` premise.

Direct Mathlib order lemmas only — no `linarith` invocation inside
the helper proofs themselves, so the trust footprint stays narrow
(the same way the Int helpers use `Int.mul_nonpos_of_nonneg_of_nonpos`
etc. directly rather than `omega`). `linarith` elsewhere (the
existing `proof_broker` decide-procedure LRA closer registered by
`ProofBrokerMathlib.Tactic`) is unaffected.

Arity scope: arity 2 only today, matching the smallest non-trivial
Farkas cert. Arities 3..N are mechanical copies — write them when
a cert in practice exceeds arity 2. Goal-shape scope: `False` only;
non-`False` LRA goals would mirror `farkasGoalLe2` / `farkasGoalLt2`
from the Int side but aren't needed for the Tier 2 case-split path
(per-branch goal stays `False`).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic

namespace ProofBrokerMathlib.TermMode

/-- Direction-normalization helper: convert `a ≤ b` over `Real` to `a - b ≤ 0`. -/
theorem rLeToLe0 {a b : Real} (h : a ≤ b) : a - b ≤ 0 :=
  sub_nonpos_of_le h

/-- Direction-normalization helper: convert `a ≥ b` over `Real` to `b - a ≤ 0`. -/
theorem rGeToLe0 {a b : Real} (h : a ≥ b) : b - a ≤ 0 :=
  sub_nonpos_of_le h

/-- Farkas contradiction, arity 2, Real-typed. Hypotheses are
    pre-normalized to `a ≤ 0` form by the OCaml side via `rLeToLe0`
    / `rGeToLe0`. The `hpos` premise is discharged by `linarith`
    (or by direct polynomial-identity construction) at closer-build
    time — same narrow role as the Int version's `omega` call.
    Coefficients `c1`, `c2` are visible in the proof term as Real
    literal arguments. -/
theorem rFarkasContradict
    {a1 a2 : Real} (h1 : a1 ≤ 0) (h2 : a2 ≤ 0)
    {c1 c2 : Real} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hpos : 0 < c1 * a1 + c2 * a2) : False :=
  let s1 : c1 * a1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc1 h1
  let s2 : c2 * a2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc2 h2
  let ssum : c1 * a1 + c2 * a2 ≤ 0 := add_nonpos s1 s2
  absurd hpos (not_lt.mpr ssum)

#print axioms rFarkasContradict
#print axioms rLeToLe0
#print axioms rGeToLe0

end ProofBrokerMathlib.TermMode
