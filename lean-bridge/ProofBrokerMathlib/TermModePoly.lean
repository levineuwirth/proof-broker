/-
Class-polymorphic (α-typed) Tier 1 Farkas reconstruction helpers —
the R3-M2 lift family. Mirror of `ProofBrokerMathlib.TermMode`
(which covers `Real`) over an arbitrary linearly ordered commutative
ring: `{α : Type*} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]`.

The roadmap names this family "`farkasContradictN` over
`[LinearOrderedCommRing α]`"; Mathlib's 2025 ordered-algebra refactor
removed that bundled class (it is absent from the pinned Mathlib
v4.32.0), and its modern spelling is exactly the three instances
above. Recorded in delta.md §5.

These lemmas are what makes the α→Int type specialization
INVERTIBLE: the solver found the certificate on the Int image, and
the closer replays the cert's Farkas coefficients AT α through this
family. Because α is an arbitrary (possibly dense) ordered ring, the
family is strictness-preserving like the Real one — the LIA +1 trick
is never applied at α. A witness whose contradiction depends on
integrality (valid at Int, invalid at a dense α) therefore fails the
replay: the fold's residual subgoal is false and the tactic fails —
never an unsound closure. The names of the load-bearing lemmas here
flow into the reifier's `embedding_witness:` tags and the cert's
`soundness_witness`.

Arity scope: arities 1..N via `pFarkasContradictN` /
`pFarkasContradictNStrict` over a left-associative sum the closer
builds. Comparison goals reach the fold via `pLeViaLt` / `pLtViaLe`
(`Decidable.byContradiction` over `LinearOrder.decidableLE` — no
classical byContradiction needed at the wrapper).
-/

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Order.Basic

namespace ProofBrokerMathlib.TermModePoly

set_option linter.unusedSectionVars false

variable {α : Type*} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

/-- Direction-normalization helper: `a ≤ b` at α to `a - b ≤ 0`. -/
theorem pLeToLe0 {a b : α} (h : a ≤ b) : a - b ≤ 0 :=
  sub_nonpos_of_le h

/-- Direction-normalization helper: `a ≥ b` at α to `b - a ≤ 0`. -/
theorem pGeToLe0 {a b : α} (h : a ≥ b) : b - a ≤ 0 :=
  sub_nonpos_of_le h

/-- Strict-`<` normalization at α: `a - b < 0` (strict). No +1 trick —
    α may be dense; strictness threads through the fold instead. -/
theorem pLtToLt0 {a b : α} (h : a < b) : a - b < 0 :=
  sub_neg_of_lt h

/-- Mirror of `pLtToLt0` for `>`. -/
theorem pGtToLt0 {a b : α} (h : a > b) : b - a < 0 :=
  sub_neg_of_lt h

/-- Eq-hypothesis normalization at α: `a = b` to `a - b ≤ 0`. -/
theorem pEqToLe0 {a b : α} (h : a = b) : a - b ≤ 0 :=
  sub_nonpos_of_le (le_of_eq h)

/-- Flipped variant for negative coefficients on Eq hypotheses. -/
theorem pEqToLe0Flipped {a b : α} (h : a = b) : b - a ≤ 0 :=
  sub_nonpos_of_le (le_of_eq h.symm)

/-- Not-hypothesis normalization at α, strictness-preserving:
    `¬(a ≤ b)` means `b < a`, normalized to the strict `b - a < 0`. -/
theorem pNotLeToLt0 {a b : α} (h : ¬(a ≤ b)) : b - a < 0 :=
  sub_neg_of_lt (not_le.mp h)

theorem pNotGeToLt0 {a b : α} (h : ¬(a ≥ b)) : a - b < 0 :=
  sub_neg_of_lt (not_le.mp h)

theorem pNotLtToLe0 {a b : α} (h : ¬(a < b)) : b - a ≤ 0 :=
  sub_nonpos_of_le (not_lt.mp h)

theorem pNotGtToLe0 {a b : α} (h : ¬(a > b)) : a - b ≤ 0 :=
  sub_nonpos_of_le (not_lt.mp h)

/-- Strict-aware product step: strict coefficient × strict-negative
    premise stays strict. -/
theorem pMulPosNeg {c a : α} (hc : 0 < c) (ha : a < 0) : c * a < 0 :=
  mul_neg_of_pos_of_neg hc ha

/-- Strict-aware sum step: Le + Lt → Lt. -/
theorem pAddLeLt {x y : α} (hx : x ≤ 0) (hy : y < 0) : x + y < 0 := by
  have := add_lt_add_of_le_of_lt hx hy
  simpa using this

/-- Strict-aware sum step: Lt + Le → Lt. -/
theorem pAddLtLe {x y : α} (hx : x < 0) (hy : y ≤ 0) : x + y < 0 := by
  have := add_lt_add_of_lt_of_le hx hy
  simpa using this

/-- Strict-aware sum step: Lt + Lt → Lt. -/
theorem pAddNeg {x y : α} (hx : x < 0) (hy : y < 0) : x + y < 0 := by
  have := add_lt_add hx hy
  simpa using this

/-- General-arity contradiction step at α: the closer builds
    `s = c1*a1 + ... + cN*aN` with `s ≤ 0` from the fold; the
    residual `0 < s` (a ring identity on the cert's literal
    coefficients) yields `False`. -/
theorem pFarkasContradictN (s : α) (hsum : s ≤ 0) (hpos : 0 < s) : False :=
  absurd hpos (not_lt.mpr hsum)

/-- Strict-aware general-arity contradiction step: with at least one
    strict premise the sum is strictly negative, so `0 ≤ s` (K = 0
    permitted) closes. -/
theorem pFarkasContradictNStrict (s : α) (hsum : s < 0) (hpos : 0 ≤ s) : False :=
  absurd hsum (not_lt.mpr hpos)

/-- `0 ≤ 0` at α, for the trivial-residual case. -/
theorem pZeroNonneg : (0 : α) ≤ 0 := le_refl 0

/-- Arity-N comparison-goal wrapper at α: converts a `≤` goal into a
    `(neg_form → False)` shape. Decidable at α — `LinearOrder α`
    carries `decidableLE` — so no classical byContradiction is needed
    here (the fold's residual tactics may still pull the classical
    baseline). -/
theorem pLeViaLt {b c : α} (h : c < b → False) : b ≤ c :=
  Decidable.byContradiction fun hng => h (lt_of_not_ge hng)

theorem pLtViaLe {b c : α} (h : c ≤ b → False) : b < c :=
  Decidable.byContradiction fun hng => h (not_lt.mp hng)

#print axioms pLeToLe0
#print axioms pGeToLe0
#print axioms pLtToLt0
#print axioms pGtToLt0
#print axioms pEqToLe0
#print axioms pEqToLe0Flipped
#print axioms pNotLeToLt0
#print axioms pNotGeToLt0
#print axioms pNotLtToLe0
#print axioms pNotGtToLe0
#print axioms pMulPosNeg
#print axioms pAddLeLt
#print axioms pAddLtLe
#print axioms pAddNeg
#print axioms pFarkasContradictN
#print axioms pFarkasContradictNStrict
#print axioms pZeroNonneg
#print axioms pLeViaLt
#print axioms pLtViaLe

end ProofBrokerMathlib.TermModePoly
