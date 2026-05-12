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

Arity scope: arity-2 `rFarkasContradict` anchors the binary fixture;
arities 3..N are handled by `rFarkasContradictN` /
`rFarkasContradictNStrict` over a left-associative sum the OCaml-side
closer builds. Comparison goals (`≤`, `<`, `≥`, `>`, `=`) reach the
same fold via the wrapper helpers (`rLeViaLt` / `rLtViaLe`) which
convert each goal shape to an implication-False whose body the closer
recurses into.
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
    goal into a `(neg_form → False)` shape so the closer can introduce
    the negated goal as a regular hypothesis and delegate to the
    existing arity-N strict-aware False-fold. Mirror of Rocq's
    `r_le_via_lt` / `r_lt_via_le`. The strict-aware fold subsumes all
    three previous arity-2 paths in one go: strictness flows in from
    neg_goal's Lt-shape on the Le-goal path, from a1's Lt-shape on the
    strict-a1 Lt-goal path, and from neither on the standard Lt-goal
    path. -/
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
#print axioms rLeViaLt
#print axioms rLtViaLe
#print axioms rEqToLe0
#print axioms rEqToLe0Flipped
#print axioms rNotLeToLt0
#print axioms rNotGeToLt0
#print axioms rNotLtToLe0
#print axioms rNotGtToLe0

end ProofBrokerMathlib.TermMode
