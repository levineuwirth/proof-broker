import ProofBroker

/-! R6-015 step 2: synthetic proofs for the audit program's `--synthetic` mode (control 8, exercised before the lock).
    Every goal is synthetic, written from the specification; no retained R6 certificate is replayed. Each `sN_local` is closed
    by an injected witness (`term_closer_test`); each `sN_whole` refers to it once, at full arity, as R6's whole targets
    refer to their local ones. `c*` pairs use the constrained route; `p*` pairs use the pinned fold, as contrast. -/

set_option linter.unusedVariables false

namespace R6015Audit

-- the mixed-carrier case: an `Int` goal over ℕ casts, `Int` and ℕ hypotheses, an opaque `Int` atom
theorem c1_local (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) : z / 3 + ↑n ≤ 5 := by
  term_closer_test constrained "hn:1,hz:1,neg_goal:1"
theorem c1_whole (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) : z / 3 + ↑n ≤ 5 :=
  c1_local n m z hn hz

-- the same, scaled by 2
theorem c2_local (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) : z / 3 + ↑n ≤ 5 := by
  term_closer_test constrained "hn:2,hz:2,neg_goal:2"
theorem c2_whole (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z / 3 + ↑m ≤ 5) : z / 3 + ↑n ≤ 5 :=
  c2_local n m z hn hz

-- cast/product: a product of casts in the hypothesis, a cast of the product in the goal
theorem c3_local (x y : Nat) (z : Int) (h : (x : Int) * (y : Int) ≤ z) : ((x * y : Nat) : Int) ≤ z := by
  term_closer_test constrained "h:1,neg_goal:1"
theorem c3_whole (x y : Nat) (z : Int) (h : (x : Int) * (y : Int) ≤ z) : ((x * y : Nat) : Int) ≤ z :=
  c3_local x y z h

-- cast/product, the other way: a ℕ product hypothesis, an `Int` product-of-casts goal
theorem c4_local (x y k : Nat) (h : x * y ≤ k) : (x : Int) * (y : Int) ≤ (k : Int) := by
  term_closer_test constrained "h:1,neg_goal:1"
theorem c4_whole (x y k : Nat) (h : x * y ≤ k) : (x : Int) * (y : Int) ≤ (k : Int) :=
  c4_local x y k h

-- the ℕ closer, constrained, with an IR nonnegativity fact
theorem c5_local (m n : Nat) : m < m + n + 1 := by
  term_closer_test constrained "neg_goal:1,_pb_nonneg_n:1"
theorem c5_whole (m n : Nat) : m < m + n + 1 :=
  c5_local m n

-- the ℕ closer, constrained, with an `Int` hypothesis as it stands
theorem c6_local (n : Nat) (z : Int) (h : z + ↑n ≤ 0) (hz : 0 < z) : False := by
  term_closer_test constrained "h:1,hz:1,_pb_nonneg_n:1"
theorem c6_whole (n : Nat) (z : Int) (h : z + ↑n ≤ 0) (hz : 0 < z) : False :=
  c6_local n z h hz

-- the ℤ closer, constrained, with unused hypotheses in scope
theorem c7_local (x y : Int) (hu1 : 0 ≤ x) (h : x ≤ y) (hu2 : y ≤ 9) : x ≤ y := by
  term_closer_test constrained "h:1,neg_goal:1"
theorem c7_whole (x y : Int) (hu1 : 0 ≤ x) (h : x ≤ y) (hu2 : y ≤ 9) : x ≤ y :=
  c7_local x y hu1 h hu2

-- contrast: the review's probe under the pinned fold (closes through contextual `omega`)
theorem p1_local (x y : Int) (h : x ≤ y) : x ≤ y := by
  term_closer_test pinned "h:1,neg_goal:2"
theorem p1_whole (x y : Int) (h : x ≤ y) : x ≤ y :=
  p1_local x y h

-- contrast: ℕ nonnegativity under the pinned fold
theorem p2_local (m n : Nat) : m < m + n + 1 := by
  term_closer_test pinned "neg_goal:1"
theorem p2_whole (m n : Nat) : m < m + n + 1 :=
  p2_local m n

end R6015Audit
