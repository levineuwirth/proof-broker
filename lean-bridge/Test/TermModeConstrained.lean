/-
R6-015 synthetic tests for the constrained term-mode route
(`experiments/r6/R6-015-PROPOSAL.md`, step 2). Every goal here is
synthetic, written from the specification; no retained R6 certificate
is replayed. Witnesses are injected with `term_closer_test`, bypassing
dispatch and the certificate checker, so no solver runs.

Build success is the test. `#guard_msgs` pins each selection and each
failure's message.
-/

import ProofBroker

set_option linter.unusedVariables false

namespace R6015Synthetic

/-! ## The required mixed-carrier case

An `Int` goal over ℕ casts, with `Int` and ℕ hypotheses and an opaque
`Int` atom (`z / 3`): the shape the pinned ℕ closer refuses with
`nat_closer_int_goal`. -/

/-- info: term_closer_test: constrained term_mode_int -/
#guard_msgs in
example (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) :
    z / 3 + ↑n ≤ 5 := by
  term_closer_test constrained "hn:1,hz:1,neg_goal:1"

/-! Validity-preserving mutations: scaled, reordered, a zero entry. -/

/-- info: term_closer_test: constrained term_mode_int -/
#guard_msgs in
example (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) :
    z / 3 + ↑n ≤ 5 := by
  term_closer_test constrained "hn:2,hz:2,neg_goal:2"

/-- info: term_closer_test: constrained term_mode_int -/
#guard_msgs in
example (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) :
    z / 3 + ↑n ≤ 5 := by
  term_closer_test constrained "hn:3,hz:3,neg_goal:3"

/-- info: term_closer_test: constrained term_mode_int -/
#guard_msgs in
example (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) :
    z / 3 + ↑n ≤ 5 := by
  term_closer_test constrained "neg_goal:1,hz:1,hn:1"

/-- info: term_closer_test: constrained term_mode_int -/
#guard_msgs in
example (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) (hu : z ≤ 7) :
    z / 3 + ↑n ≤ 5 := by
  term_closer_test constrained "hn:1,hz:1,hu:0,neg_goal:1"

/-! Invalid mutations: each must fail under the constrained route. -/

/--
error: proof_broker_term (constrained): the weighted sum does not cancel; its normal form is -1 * (↑n^1) + -1 * (z / 3^1) + 7
-/
#guard_msgs in
example (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) :
    z / 3 + ↑n ≤ 5 := by
  term_closer_test constrained "hn:1,hz:1,neg_goal:2"

/--
error: proof_broker_term (constrained): the weighted sum does not cancel; its normal form is 1 * (↑n^1) + -1 * (↑m^1) + 1
-/
#guard_msgs in
example (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) :
    z / 3 + ↑n ≤ 5 := by
  term_closer_test constrained "hn:2,hz:1,neg_goal:1"

/--
error: proof_broker_term (constrained): the weighted sum does not cancel; its normal form is -1 * (↑m^1) + -1 * (z / 3^1) + 6
-/
#guard_msgs in
example (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) :
    z / 3 + ↑n ≤ 5 := by
  term_closer_test constrained "hn:1,neg_goal:1"

/--
error: proof_broker_term (constrained): the weighted sum does not cancel; its normal form is 1 * (z^1) + -6
-/
#guard_msgs in
example (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) (hu : z ≤ 7) :
    z / 3 + ↑n ≤ 5 := by
  term_closer_test constrained "hn:1,hz:1,hu:1,neg_goal:1"

/-! ## The required cast/product case

One product appears as a cast of a product and as a product of casts. -/

/-- info: term_closer_test: constrained term_mode_int -/
#guard_msgs in
example (x y : Nat) (z : Int) (h : (x : Int) * (y : Int) ≤ z) :
    ((x * y : Nat) : Int) ≤ z := by
  term_closer_test constrained "h:1,neg_goal:1"

/-- info: term_closer_test: constrained term_mode_int -/
#guard_msgs in
example (x y k : Nat) (h : x * y ≤ k) :
    (x : Int) * (y : Int) ≤ (k : Int) := by
  term_closer_test constrained "h:1,neg_goal:1"

/-! ## The review's probe

`h : x ≤ y ⊢ x ≤ y` with (`h` 1, `neg_goal` 2): the combination does
not cancel. It must fail under the constrained route; the pinned fold
closes it through contextual `omega`. -/

/--
error: proof_broker_term (constrained): the weighted sum does not cancel; its normal form is -1 * (x^1) + 1 * (y^1) + 2
-/
#guard_msgs in
example (x y : Int) (h : x ≤ y) : x ≤ y := by
  term_closer_test constrained "h:1,neg_goal:2"

/-- info: term_closer_test: pinned term_mode_int -/
#guard_msgs in
example (x y : Int) (h : x ≤ y) : x ≤ y := by
  term_closer_test pinned "h:1,neg_goal:2"

/-- info: term_closer_test: constrained term_mode_int -/
#guard_msgs in
example (x y : Int) (h : x ≤ y) : x ≤ y := by
  term_closer_test constrained "h:1,neg_goal:1"

/-! ## ℕ nonnegativity is not used

`m < m + n + 1` with `neg_goal` alone: the sum is `↑n + 1`. The
pinned fold's contextual `omega` closes it from `n`'s nonnegativity;
the constrained step does not. With the IR fact `_pb_nonneg_n` in the
witness, the sum cancels. -/

/--
error: proof_broker_term (constrained): the weighted sum does not cancel; its normal form is 1 * (↑n^1) + 1
-/
#guard_msgs in
example (m n : Nat) : m < m + n + 1 := by
  term_closer_test constrained "neg_goal:1"

/-- info: term_closer_test: pinned term_mode_nat -/
#guard_msgs in
example (m n : Nat) : m < m + n + 1 := by
  term_closer_test pinned "neg_goal:1"

/-- info: term_closer_test: constrained term_mode_nat -/
#guard_msgs in
example (m n : Nat) : m < m + n + 1 := by
  term_closer_test constrained "neg_goal:1,_pb_nonneg_n:1"

/-! The ℕ closer, constrained, with an `Int` hypothesis as it stands in
a `False` goal. -/

/-- info: term_closer_test: constrained term_mode_nat -/
#guard_msgs in
example (n : Nat) (z : Int) (h : z + ↑n ≤ 0) (hz : 0 < z) : False := by
  term_closer_test constrained "h:1,hz:1,_pb_nonneg_n:1"

/--
error: proof_broker_term (constrained): the weighted sum does not cancel; its normal form is 1 * (↑n^1) + 1
-/
#guard_msgs in
example (n : Nat) (z : Int) (h : z + ↑n ≤ 0) (hz : 0 < z) : False := by
  term_closer_test constrained "h:1,hz:1"

/-! ## Not positive -/

/--
error: proof_broker_term (constrained): the weighted sum normalizes to 0, which is not positive
-/
#guard_msgs in
example (x y : Int) (h : x ≤ y) (h2 : y ≤ x) (h3 : x ≠ y) : False := by
  term_closer_test constrained "h:1,h2:1"

/-! ## Selection guard (control 6)

A `Nat` comparison in a mixed context keeps the ℕ closer; an `Int`
comparison with no ℕ variables takes the ℤ closer. -/

/-- info: term_closer_test: constrained term_mode_nat -/
#guard_msgs in
example (n m : Nat) (z : Int) (h : n ≤ m) (hz : z ≤ 0) : n ≤ m + 1 := by
  term_closer_test constrained "h:1,neg_goal:1"

/-- info: term_closer_test: constrained term_mode_int -/
#guard_msgs in
example (x y : Int) (h : x + 1 ≤ y) : x < y := by
  term_closer_test constrained "h:1,neg_goal:1"

/-! ## Fail closed -/

/--
error: proof_broker_term: witness names hypothesis 'nope' which is not in scope
-/
#guard_msgs in
example (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) :
    z / 3 + ↑n ≤ 5 := by
  term_closer_test constrained "hn:1,hz:1,nope:1,neg_goal:1"

/-! ## A hypothesis reached through the sum (build review, finding 1)

A cast instance that takes a hypothesis: the reifier canonicalizes the
cast, but the positivity proof's type annotation carries the sum, and
with it `tag`. The gates check the returned term, so the step fails
closed. -/

@[reducible] def castViaHyp (_h : True) : NatCast Int := instNatCastInt

/--
error: proof_broker_term (constrained): the positivity proof reaches hypotheses [tag]
-/
#guard_msgs in
example (tag : True) (n m : Nat) (h : n ≤ m) :
    (@NatCast.natCast Int (castViaHyp tag) n) ≤ @NatCast.natCast Int (castViaHyp tag) m := by
  term_closer_test constrained "h:1,neg_goal:1"

/-- info: term_closer_test: constrained term_mode_int -/
#guard_msgs in
example (n m : Nat) (h : n ≤ m) : (n : Int) ≤ (m : Int) := by
  term_closer_test constrained "h:1,neg_goal:1"

/-! ## Axioms (acceptance 4)

The constrained route's proofs depend on `propext`, `Classical.choice`
and `Quot.sound`, through the ring normalizer's soundness proof
(`TermMode.posOfNormNum`); the pinned fold's, through `omega`, on
`propext` and `Quot.sound`. Both are within acceptance 4. -/

theorem axioms_mixed (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) :
    z / 3 + ↑n ≤ 5 := by
  term_closer_test constrained "hn:1,hz:1,neg_goal:1"

/-- info: 'R6015Synthetic.axioms_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms axioms_mixed

theorem axioms_pinned (x y : Int) (h : x ≤ y) : x ≤ y := by
  term_closer_test pinned "h:1,neg_goal:1"

/-- info: 'R6015Synthetic.axioms_pinned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms axioms_pinned

end R6015Synthetic
