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

/-- General-arity contradiction step over Real. Mirrors
    `ProofBroker.TermMode.farkasContradictN`. The OCaml-side closer
    builds `s = c1*a1 + ... + cN*aN` and proves `s ≤ 0` by folding
    `mul_nonpos_of_nonneg_of_nonpos` + `add_nonpos` over the
    witness; this lemma turns that into `False` from `0 < s`. -/
theorem rFarkasContradictN
    (s : Real) (hsum : s ≤ 0) (hpos : 0 < s) : False :=
  absurd hpos (not_lt.mpr hsum)

/-- Strict-[<] hypothesis normalization for `Real`: produces `a - b < 0`
    (strict) rather than the weakened `≤ 0` form. Mirror of Rocq's
    `r_lt_to_lt0`. The LRA strict-aware fold path consumes this directly
    (no LIA +1 trick over R). -/
theorem rLtToLt0 {a b : Real} (h : a < b) : a - b < 0 :=
  sub_neg_of_lt h

/-- Mirror of `rLtToLt0` for `>`. Lean's `GT.gt a b` reduces to
    `LT.lt b a` by instance; the explicit form is here for parity
    with `rGeToLe0` (and because the dispatcher matches `GT.gt` /
    `LT.lt` heads separately). -/
theorem rGtToLt0 {a b : Real} (h : a > b) : b - a < 0 :=
  sub_neg_of_lt h

/-- Strict-aware product step: with `0 < c` strict and `a < 0` strict,
    the product `c * a < 0` is strict. Mirror of Rocq's
    `r_mul_pos_neg`. Used when the witness has a Lt-compiled premise
    with a positive coefficient — strictness flows into the fold. -/
theorem rMulPosNeg {c a : Real} (hc : 0 < c) (ha : a < 0) : c * a < 0 :=
  mul_neg_of_pos_of_neg hc ha

/-- Strict-aware sum step: Le + Lt → Lt. Used by the fold when the
    accumulator is non-strict (`acc ≤ 0`) and the next product is
    strict (`prod < 0`). Mirror of Rocq's `r_add_le_lt`. -/
theorem rAddLeLt {x y : Real} (hx : x ≤ 0) (hy : y < 0) : x + y < 0 := by
  have := add_lt_add_of_le_of_lt hx hy
  simpa using this

/-- Strict-aware sum step: Lt + Le → Lt. Mirror of Rocq's
    `r_add_lt_le`. -/
theorem rAddLtLe {x y : Real} (hx : x < 0) (hy : y ≤ 0) : x + y < 0 := by
  have := add_lt_add_of_lt_of_le hx hy
  simpa using this

/-- Strict-aware sum step: Lt + Lt → Lt. Mirror of Rocq's
    `r_add_neg`. -/
theorem rAddNeg {x y : Real} (hx : x < 0) (hy : y < 0) : x + y < 0 := by
  have := add_lt_add hx hy
  simpa using this

/-- Strict-aware general-arity contradiction step. Mirror of Rocq's
    `r_farkas_contradict_n_strict`. Triggered when at least one
    premise in the Farkas combination is strict (Lt-compiled) with
    positive coefficient — the sum is strictly negative, so the
    residual `K` only needs to be non-negative for the contradiction
    (in particular, `K = 0` is permitted when strictness alone
    carries the contradiction, eg `5 < x ∧ x < 5 ⊢ False`). -/
theorem rFarkasContradictNStrict
    (s : Real) (hsum : s < 0) (hpos : 0 ≤ s) : False :=
  absurd hsum (not_lt.mpr hpos)

/-- Real-typed `0 ≤ 0` witness. Mirror of Rocq's `r_zero_nonneg`.
    Needed when the strict-aware path produces `K = 0` (eg the
    trivial-equality case in the Le-goal post-`le_antisymm` split,
    or the strict-only False-goal). -/
theorem rZeroNonneg : (0 : Real) ≤ 0 := le_refl 0

/-- Weakening helper for the comparison-goal Le-path: convert
    strict `a < 0` to non-strict `a ≤ 0`. Sound here because the
    Le-goal closer derives its contradiction from the neg_goal's
    Lt-shape over R, not from `a1`'s strictness; weakening loses
    no information for that path. Mirror of Rocq's
    `r_strict_neg_to_nonpos`. -/
theorem rStrictNegToNonpos {a : Real} (h : a < 0) : a ≤ 0 :=
  le_of_lt h

/-- Real-typed Farkas reconstruction for a non-`False` goal of shape
    `b ≤ c`. Strict-aware on `cng` (the neg_goal coefficient): with
    `hcng : 0 < cng` strict and the negated goal compiled as `Lt(c-b)`
    (since `¬(b ≤ c) ≡ c < b` over R), the combination
    `cng * (c - b) < 0` is strict, and combined with `c1 * a1 ≤ 0`
    we get a strict sum — contradicting `0 ≤ c1*a1 + cng*(c-b)`.
    Collapsed K+Heq form (matches `rFarkasContradict` convention):
    the closer builds `hpos` as an evar and discharges via `linarith`,
    instead of splitting into separate K-positivity + ring-identity
    steps the way Rocq's `r_farkas_le_goal_2` does. Mirror of Rocq's
    `r_farkas_le_goal_2`. -/
theorem rFarkasGoalLe2
    {b c : Real} {a1 : Real} (h1 : a1 ≤ 0)
    {c1 cng : Real} (hc1 : 0 ≤ c1) (hcng : 0 < cng)
    (hpos : 0 ≤ c1 * a1 + cng * (c - b))
    : b ≤ c := by
  by_contra hngt
  have hngt : c < b := lt_of_not_ge hngt
  have hcb : c - b < 0 := sub_neg_of_lt hngt
  have s1 : c1 * a1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc1 h1
  have s2 : cng * (c - b) < 0 := mul_neg_of_pos_of_neg hcng hcb
  have ssum : c1 * a1 + cng * (c - b) < 0 := rAddLeLt s1 s2
  exact absurd ssum (not_lt.mpr hpos)

/-- Real-typed Farkas reconstruction for a strict goal `b < c`.
    Standard (non-strict-aware) shape: `0 ≤ cng`, `0 < hpos`. The
    negated goal `¬(b < c) ≡ c ≤ b` compiles as `Le(c-b)`, so the
    Farkas sum is non-strict and requires the witness's linear
    combination to be strictly positive. With strict `a1` (R Lt
    hypothesis), routing instead picks `rFarkasGoalLt2StrictA1`
    below. Mirror of Rocq's `r_farkas_lt_goal_2`. -/
theorem rFarkasGoalLt2
    {b c : Real} {a1 : Real} (h1 : a1 ≤ 0)
    {c1 cng : Real} (hc1 : 0 ≤ c1) (hcng : 0 ≤ cng)
    (hpos : 0 < c1 * a1 + cng * (c - b))
    : b < c := by
  by_contra hnlt
  have hnlt : c ≤ b := not_lt.mp hnlt
  have hcb : c - b ≤ 0 := sub_nonpos_of_le hnlt
  have s1 : c1 * a1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc1 h1
  have s2 : cng * (c - b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcng hcb
  have ssum : c1 * a1 + cng * (c - b) ≤ 0 := add_nonpos s1 s2
  exact absurd hpos (not_lt.mpr ssum)

/-- Real-typed Farkas reconstruction for strict goal `b < c` with
    strict-`<` real hypothesis (`h1 : a1 < 0`). The standard
    `rFarkasGoalLt2` requires the combination to be strictly positive;
    with strict `a1` the trivial-K=0 case (eg `(h : 0 < x) ⊢ 0 < x`)
    needs the strictness to flow through the sum: strict `c1 * a1 < 0`
    via `rMulPosNeg`, then `Lt + Le → Lt` via `rAddLtLe`, yielding
    the strict-aware contradiction with `0 ≤ c1*a1 + cng*(c-b)`.
    Mirror of Rocq's `r_farkas_lt_goal_2_strict_a1`. -/
theorem rFarkasGoalLt2StrictA1
    {b c : Real} {a1 : Real} (h1 : a1 < 0)
    {c1 cng : Real} (hc1 : 0 < c1) (hcng : 0 ≤ cng)
    (hpos : 0 ≤ c1 * a1 + cng * (c - b))
    : b < c := by
  by_contra hnlt
  have hnlt : c ≤ b := not_lt.mp hnlt
  have hcb : c - b ≤ 0 := sub_nonpos_of_le hnlt
  have s1 : c1 * a1 < 0 := mul_neg_of_pos_of_neg hc1 h1
  have s2 : cng * (c - b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcng hcb
  have ssum : c1 * a1 + cng * (c - b) < 0 := rAddLtLe s1 s2
  exact absurd ssum (not_lt.mpr hpos)

/-- Eq-hypothesis normalization (Real). Mirror of core's `eqToLe0`
    for `Int`. Folds `h : a = b` into the existing strict-aware
    Le-only fold via `a - b ≤ 0`. Solver-emitted certs apply
    signed coefficients on Eq hypotheses to capture both directions;
    the closer applies this to `h.symm` for negative coefficients
    while keeping the positive-coefficient invariant on inequality
    premises. -/
theorem rEqToLe0 {a b : Real} (h : a = b) : a - b ≤ 0 :=
  sub_nonpos_of_le (le_of_eq h)

/-- Flipped variant for negative coefficients on Eq hypotheses
    over Real. Same as `rEqToLe0` applied to `h.symm`. -/
theorem rEqToLe0Flipped {a b : Real} (h : a = b) : b - a ≤ 0 :=
  sub_nonpos_of_le (le_of_eq h.symm)

/-- Not-hypothesis normalization (LRA). Mirror of core's `notLeToLe0`
    family but strictness-preserving over Real (no +1 trick).
    `¬(a ≤ b)` over Real means `b < a`; with no discrete domain to
    shift into, the normalized form is the strict `b - a < 0`. The
    strict-aware fold in the closer threads this strictness through
    via `rMulPosNeg` / `rAddLeLt` etc. -/
theorem rNotLeToLt0 {a b : Real} (h : ¬(a ≤ b)) : b - a < 0 :=
  sub_neg_of_lt (not_le.mp h)

theorem rNotGeToLt0 {a b : Real} (h : ¬(a ≥ b)) : a - b < 0 :=
  sub_neg_of_lt (not_le.mp h)

theorem rNotLtToLe0 {a b : Real} (h : ¬(a < b)) : b - a ≤ 0 :=
  sub_nonpos_of_le (not_lt.mp h)

theorem rNotGtToLe0 {a b : Real} (h : ¬(a > b)) : a - b ≤ 0 :=
  sub_nonpos_of_le (not_lt.mp h)

/-- Arity-N comparison-goal wrappers (Real). Convert a comparison
    goal into a `(neg_form → False)` shape so the closer can
    introduce the negated goal as a regular hypothesis and delegate
    to the existing arity-N strict-aware False-fold. Mirror of Rocq's
    `r_le_via_lt` / `r_lt_via_le`. The arity-2-specific helpers
    `rFarkasGoalLe2` / `rFarkasGoalLt2` / `rFarkasGoalLt2StrictA1`
    above are sound but specialized; the unified path subsumes all
    three via the strict-aware fold (strictness from neg_goal's
    Lt-shape on the Le-goal path; from a1's Lt-shape on the strict-a1
    Lt-goal path; from neither on the standard Lt-goal path). -/
theorem rLeViaLt {b c : Real} (h : c < b → False) : b ≤ c := by
  by_contra hng
  have hng : c < b := lt_of_not_ge hng
  exact h hng

theorem rLtViaLe {b c : Real} (h : c ≤ b → False) : b < c := by
  by_contra hng
  have hng : c ≤ b := not_lt.mp hng
  exact h hng

#print axioms rFarkasContradict
#print axioms rFarkasContradictN
#print axioms rLeToLe0
#print axioms rGeToLe0
#print axioms rLtToLt0
#print axioms rGtToLt0
#print axioms rMulPosNeg
#print axioms rAddLeLt
#print axioms rAddLtLe
#print axioms rAddNeg
#print axioms rFarkasContradictNStrict
#print axioms rZeroNonneg
#print axioms rStrictNegToNonpos
#print axioms rFarkasGoalLe2
#print axioms rFarkasGoalLt2
#print axioms rFarkasGoalLt2StrictA1
#print axioms rLeViaLt
#print axioms rLtViaLe
#print axioms rEqToLe0
#print axioms rEqToLe0Flipped
#print axioms rNotLeToLt0
#print axioms rNotGeToLt0
#print axioms rNotLtToLe0
#print axioms rNotGtToLe0

end ProofBrokerMathlib.TermMode
