/-
Synthetic tests for the constrained term-mode route: R6-015's
(`experiments/r6/R6-015-PROPOSAL.md`, step 2), revised for R6-016's
axiom-preserving final step (`experiments/r6/R6-016-PROPOSAL.md`; the
control-9 cases are at the end). Every goal here is
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
error: proof_broker_term (constrained): the weighted sum does not cancel; its normal form is -1 * (z / 3) + -1 * (↑n) + 7
-/
#guard_msgs in
example (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) :
    z / 3 + ↑n ≤ 5 := by
  term_closer_test constrained "hn:1,hz:1,neg_goal:2"

/--
error: proof_broker_term (constrained): the weighted sum does not cancel; its normal form is -1 * (↑m) + 1 * (↑n) + 1
-/
#guard_msgs in
example (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) :
    z / 3 + ↑n ≤ 5 := by
  term_closer_test constrained "hn:2,hz:1,neg_goal:1"

/--
error: proof_broker_term (constrained): the weighted sum does not cancel; its normal form is -1 * (z / 3) + -1 * (↑m) + 6
-/
#guard_msgs in
example (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) :
    z / 3 + ↑n ≤ 5 := by
  term_closer_test constrained "hn:1,neg_goal:1"

/--
error: proof_broker_term (constrained): the weighted sum does not cancel; its normal form is 1 * (z) + -6
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
error: proof_broker_term (constrained): the weighted sum does not cancel; its normal form is 1 * (y) + -1 * (x) + 2
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
error: proof_broker_term (constrained): the weighted sum does not cancel; its normal form is 1 * (↑n) + 1
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
error: proof_broker_term (constrained): the weighted sum does not cancel; its normal form is 1 * (↑n) + 1
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

R6-016: the constrained route's proofs depend on `propext` and
`Quot.sound` only (`TermMode.posOfLinearNum`), as the pinned fold's do
through `omega`. R6-015's ring normalizer added `Classical.choice`. -/

theorem axioms_mixed (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) :
    z / 3 + ↑n ≤ 5 := by
  term_closer_test constrained "hn:1,hz:1,neg_goal:1"

/-- info: 'R6015Synthetic.axioms_mixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms axioms_mixed

theorem axioms_pinned (x y : Int) (h : x ≤ y) : x ≤ y := by
  term_closer_test pinned "h:1,neg_goal:1"

/-- info: 'R6015Synthetic.axioms_pinned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms axioms_pinned

/-! ## R6-016, control 9: the linear normalizer

9a. The axiom gate: the final step's theorem, and the route's lemmas,
depend on nothing beyond `propext` and `Quot.sound`; a constrained proof
adds nothing to what an `omega` proof of the same goal uses. -/

/- The route inventory (proposal section 2): every `TermMode` lemma, and the core lemmas the
   route's proof terms use. Each depends on at most `propext` and `Quot.sound`. -/

/-- info: 'ProofBroker.TermMode.leToLe0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.leToLe0

/-- info: 'ProofBroker.TermMode.geToLe0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.geToLe0

/-- info: 'ProofBroker.TermMode.ltToLe0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.ltToLe0

/-- info: 'ProofBroker.TermMode.gtToLe0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.gtToLe0

/-- info: 'ProofBroker.TermMode.farkasContradict' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.farkasContradict

/-- info: 'ProofBroker.TermMode.farkasContradictN' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.farkasContradictN

/-- info: 'ProofBroker.TermMode.eqToLe0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.eqToLe0

/-- info: 'ProofBroker.TermMode.eqToLe0Flipped' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.eqToLe0Flipped

/-- info: 'ProofBroker.TermMode.notLeToLe0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.notLeToLe0

/-- info: 'ProofBroker.TermMode.notGeToLe0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.notGeToLe0

/-- info: 'ProofBroker.TermMode.notLtToLe0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.notLtToLe0

/-- info: 'ProofBroker.TermMode.notGtToLe0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.notGtToLe0

/-- info: 'ProofBroker.TermMode.intLeViaLt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.intLeViaLt

/-- info: 'ProofBroker.TermMode.intLtViaLe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.intLtViaLe

/-- info: 'ProofBroker.TermMode.natLeViaLt' does not depend on any axioms -/
#guard_msgs in
#print axioms ProofBroker.TermMode.natLeViaLt

/-- info: 'ProofBroker.TermMode.natLtViaLe' does not depend on any axioms -/
#guard_msgs in
#print axioms ProofBroker.TermMode.natLtViaLe

/-- info: 'ProofBroker.TermMode.natCastLe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.natCastLe

/-- info: 'ProofBroker.TermMode.natCastLt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.natCastLt

/-- info: 'ProofBroker.TermMode.natCastGe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.natCastGe

/-- info: 'ProofBroker.TermMode.natCastGt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.natCastGt

/-- info: 'ProofBroker.TermMode.natCastEq' does not depend on any axioms -/
#guard_msgs in
#print axioms ProofBroker.TermMode.natCastEq

/-- info: 'ProofBroker.TermMode.natCastNotLe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.natCastNotLe

/-- info: 'ProofBroker.TermMode.natCastNotLt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.natCastNotLt

/-- info: 'ProofBroker.TermMode.natCastNotGe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.natCastNotGe

/-- info: 'ProofBroker.TermMode.natCastNotGt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.natCastNotGt

/-- info: 'ProofBroker.TermMode.natCastNotEq' does not depend on any axioms -/
#guard_msgs in
#print axioms ProofBroker.TermMode.natCastNotEq

/-- info: 'ProofBroker.TermMode.natCastNonneg' does not depend on any axioms -/
#guard_msgs in
#print axioms ProofBroker.TermMode.natCastNonneg

/-- info: 'ProofBroker.TermMode.posOfLinearNum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ProofBroker.TermMode.posOfLinearNum

/-- info: 'Int.ofNat_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Int.ofNat_le

/-- info: 'Int.ofNat_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Int.ofNat_lt

/-- info: 'Int.ofNat_inj' does not depend on any axioms -/
#guard_msgs in
#print axioms Int.ofNat_inj

/-- info: 'Int.natCast_nonneg' does not depend on any axioms -/
#guard_msgs in
#print axioms Int.natCast_nonneg

/-- info: 'Int.lt_of_not_ge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Int.lt_of_not_ge

/-- info: 'Int.not_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Int.not_lt

/-- info: 'Int.not_lt_of_ge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Int.not_lt_of_ge

/-- info: 'Int.mul_nonpos_of_nonneg_of_nonpos' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Int.mul_nonpos_of_nonneg_of_nonpos

/-- info: 'Int.add_nonpos' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Int.add_nonpos

/-- info: 'Int.sub_nonpos_of_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Int.sub_nonpos_of_le

/-- info: 'Int.add_one_le_of_lt' does not depend on any axioms -/
#guard_msgs in
#print axioms Int.add_one_le_of_lt

/-- info: 'Int.le_of_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Int.le_of_eq

/-- info: 'Decidable.byContradiction' does not depend on any axioms -/
#guard_msgs in
#print axioms Decidable.byContradiction

/-- info: 'of_decide_eq_true' does not depend on any axioms -/
#guard_msgs in
#print axioms of_decide_eq_true

/-- info: 'Int.Linear.Expr.denote_norm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Int.Linear.Expr.denote_norm

theorem axioms_omega (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) :
    z / 3 + ↑n ≤ 5 := by
  omega

/-- info: 'R6015Synthetic.axioms_omega' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms axioms_omega

/-! 9b. No commutativity: a certificate whose cancellation needs
`x * y = y * x` fails, the two products being distinct atoms. -/

/--
error: proof_broker_term (constrained): the weighted sum does not cancel; its normal form is -1 * (y * x) + 1 * (x * y) + 1
-/
#guard_msgs in
example (x y : Int) (h : x * y ≤ 5) : y * x ≤ 5 := by
  term_closer_test constrained "h:1,neg_goal:1"

/-! 9c. Product identity: the same product in the same order cancels;
so do a cast of a product against a product of casts (above), and a
nested one. -/

/-- info: term_closer_test: constrained term_mode_int -/
#guard_msgs in
example (x y : Int) (h : x * y ≤ 5) : x * y ≤ 5 := by
  term_closer_test constrained "h:1,neg_goal:1"

/-- info: term_closer_test: constrained term_mode_int -/
#guard_msgs in
example (a b c : Nat) (z : Int) (h : (a : Int) * (b : Int) * (c : Int) ≤ z) :
    ((a * b * c : Nat) : Int) ≤ z := by
  term_closer_test constrained "h:1,neg_goal:1"

/-! 9d. Numeral products are linear: `3 * (a - b)`, `a * 0`, and a ℕ
`Zmax * 2 ^ 16` under a cast. -/

/-- info: term_closer_test: constrained term_mode_int -/
#guard_msgs in
example (a b : Int) (h : 3 * (a - b) ≤ 6) : a ≤ b + 2 := by
  term_closer_test constrained "h:1,neg_goal:3"

/-- info: term_closer_test: constrained term_mode_int -/
#guard_msgs in
example (a b : Int) (h : a * 0 + b ≤ 0) : b ≤ 0 := by
  term_closer_test constrained "h:1,neg_goal:1"

/-- info: term_closer_test: constrained term_mode_int -/
#guard_msgs in
example (Zmax : Nat) (v : Int) (h : ((Zmax * 2 ^ 16 : Nat) : Int) ≤ v) :
    (65536 : Int) * Zmax ≤ v := by
  term_closer_test constrained "h:1,neg_goal:1"

/-! 9d, the numeral budget. A closed numeral is evaluated only within a
512-bit budget; a term past it stays an atom, and nothing past it is
computed, however powers are nested. -/

/-- info: term_closer_test: constrained term_mode_int -/
#guard_msgs in
example (x y : Int) (h : 2 ^ 511 * x ≤ y) : 2 ^ 510 * x + 2 ^ 510 * x ≤ y := by
  term_closer_test constrained "h:1,neg_goal:1"

example (x y : Int) (h : 2 ^ 512 * x ≤ y) : 2 ^ 511 * x + 2 ^ 511 * x ≤ y := by
  fail_if_success term_closer_test constrained "h:1,neg_goal:1"
  omega

example (x y : Int) (h : (2 ^ 256) ^ 2 * x ≤ y) : 2 ^ 511 * x + 2 ^ 511 * x ≤ y := by
  fail_if_success term_closer_test constrained "h:1,neg_goal:1"
  omega

/-- info: term_closer_test: constrained term_mode_int -/
#guard_msgs in
example (x y : Int) (h : x * ((2 ^ 1024) ^ 1024) ^ 1024 ≤ y) : x * ((2 ^ 1024) ^ 1024) ^ 1024 ≤ y := by
  term_closer_test constrained "h:1,neg_goal:1"

/-! 9e (ℕ nonnegativity not used) and 9f (a hypothesis reached through
the sum) are the sections above, unchanged. -/

end R6015Synthetic
