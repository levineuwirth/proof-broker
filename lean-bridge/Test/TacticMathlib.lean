/-
End-to-end tactic-elaboration tests for `proof_broker` over LRA.

Importing `ProofBrokerMathlib` registers the Real reifier +
linarith closer. With that registration, `proof_broker` accepts
LRA goals (Real-typed inequalities), reifies them, dispatches to
the broker (cvc5/z3 with their LRA-capable adapters), re-verifies
the cert, and closes with `linarith` — axiom-free under
cert-gating, same contract as `omega` for LIA.

Build success of this lib is the test.

Pre-condition: cwd = `lean-bridge/` (manifest loader points at
`../examples/`); `opam exec -- dune build` (run from repo root)
populated the FFI .so.
-/

import ProofBrokerMathlib

set_option linter.unusedVariables false

namespace ProofBroker.TestMathlib

/-- Two-hypothesis LRA Farkas: `x ≥ 5 ∧ x ≤ 3 ⊢ False`. The
    broker mints a Tier 1 farkas cert (z3 native, or cvc5-Tier 3,
    depending on which adapter wins under preferHigherTier);
    `linarith` discharges. -/
example (x : Real) (h1 : x ≥ 5) (h2 : x ≤ 3) : False := by
  proof_broker

/-- Bound transfer over Real. -/
example (x : Real) (h : x ≤ 3) : x ≤ 5 := by
  proof_broker

/-- Sum-bound: x + y ≤ 10, y ≥ 0 ⊢ x ≤ 10. -/
example (x y : Real) (h1 : x + y ≤ 10) (h2 : y ≥ 0) : x ≤ 10 := by
  proof_broker

/-- Named LRA goal so `#print axioms` can confirm
    `proofBrokerCertSound` is absent — the linarith closer is
    axiom-free same as omega's. -/
theorem lra_axiom_free
    (x : Real) (h1 : x ≥ 5) (h2 : x ≤ 3) : False := by
  proof_broker

#print axioms lra_axiom_free

/-- Term-mode Tier 2 case-split over LRA: a goal with a
    disjunctive hypothesis `(x ≤ 0) ∨ (x ≥ 10)` under
    `1 ≤ x ≤ 9` closes by destruct + per-branch Farkas. cvc5
    mints a Tier 2 `case_split_farkas` cert (adapter priority
    prefers case-split over Tier 3 alethe when the IR has a
    disjunctive hypothesis). The bridge closer destructs the
    disjunction in the Lean LCtx and applies the matching
    lemma's Tier 1 Farkas witness per branch via
    `rFarkasContradict`. No `linarith` call on the per-branch
    arithmetic — only on the narrow strict-positivity
    polynomial-identity subgoal, same role `omega` plays in
    the Int term-mode closer. Trust footprint matches the
    existing `lra_axiom_free`: `[propext, Classical.choice,
    Quot.sound]` (the Mathlib LRA baseline). Mirror of Rocq's
    `pb_term_case_split_axiom_free`. -/
theorem pb_term_case_split_axiom_free
    (x : Real) (h_disj : x ≤ 0 ∨ x ≥ 10) (h_low : x ≥ 1) (h_high : x ≤ 9)
    : False := by
  proof_broker_term [cvc5]

#print axioms pb_term_case_split_axiom_free

/- ============================================================
   Tier 1 LRA term-mode test suite. Mirrors Rocq's `pb_lra_term_*`
   suite end-to-end on the Lean Mathlib side. Each test pins through
   `[z3]` (z3 mints native Tier 1 Farkas for LRA; cvc5 prefers Tier 3
   alethe-2024 which the term builder doesn't consume).

   Trust footprint for all of these is the standard Mathlib LRA
   baseline `[propext, Classical.choice, Quot.sound]` — same as the
   `linarith`-based closer in `lra_axiom_free` and the Tier 2
   case-split closer above.
   ============================================================ -/

/-- LRA Tier 1 Farkas False-goal, arity-2: `5 ≤ x ∧ x ≤ 3 ⊢ False`.
    Mirror of Rocq's `pb_lra_axiom_free` but via the new Mathlib
    term-mode dispatcher (routed via `tier1FarkasCloser` instead of
    the `linarith` fallback). -/
theorem pb_lra_term_axiom_free
    (x : Real) (h1 : 5 ≤ x) (h2 : x ≤ 3) : False := by
  proof_broker_term [z3]

#print axioms pb_lra_term_axiom_free

/-- LRA Tier 1 Farkas False-goal, arity-3: transitive chain. -/
theorem pb_lra_term_arity3_axiom_free
    (x y : Real) (h1 : 5 ≤ x) (h2 : x ≤ y) (h3 : y ≤ 3) : False := by
  proof_broker_term [z3]

#print axioms pb_lra_term_arity3_axiom_free

/-- Strict-only False-goal: `5 < x ∧ x < 5 ⊢ False`. Linear sum
    collapses to zero; strictness from both premises carries the
    contradiction via `rFarkasContradictNStrict`. -/
theorem pb_lra_term_lt_hyp_axiom_free
    (x : Real) (h1 : 5 < x) (h2 : x < 5) : False := by
  proof_broker_term [z3]

#print axioms pb_lra_term_lt_hyp_axiom_free

/-- Mixed strict + non-strict, arity-3: `1 ≤ x ∧ x ≤ y ∧ y < 1 ⊢ False`.
    Fold sees (Le, Le, Lt) — strictness from the final Lt premise
    threads through via `rAddLeLt` after the Le-Le accumulation. -/
theorem pb_lra_term_lt_mixed_axiom_free
    (x y : Real) (h1 : 1 ≤ x) (h2 : x ≤ y) (h3 : y < 1) : False := by
  proof_broker_term [z3]

#print axioms pb_lra_term_lt_mixed_axiom_free

/-- LRA comparison goal `(≤)`: `(h : n ≤ 5) ⊢ n ≤ 6`. The closer
    routes through `rFarkasGoalLe2` (strict-aware on cng — the
    neg_goal's Lt-shape over R is what produces the strict sum). -/
theorem pb_lra_term_goal_axiom_free
    (n : Real) (h : n ≤ 5) : n ≤ 6 := by
  proof_broker_term [z3]

#print axioms pb_lra_term_goal_axiom_free

/-- LRA comparison goal `(<)`: `(h : n ≤ 4) ⊢ n < 5`. The neg_goal
    `¬(n < 5) ≡ 5 ≤ n` compiles as Le over R, so the closer routes
    through `rFarkasGoalLt2` (standard non-strict path, K > 0). -/
theorem pb_lra_term_lt_axiom_free
    (n : Real) (h : n ≤ 4) : n < 5 := by
  proof_broker_term [z3]

#print axioms pb_lra_term_lt_axiom_free

/-- LRA comparison goal `(≥)`: `(h : 5 ≤ n) ⊢ n ≥ 4`. Lean's
    instance reduction unifies the proof of `4 ≤ n` (built by
    `rFarkasGoalLe2`) with the `n ≥ 4` goal, so no explicit
    `Rle_ge`-style normalization tactic is needed (Rocq does need
    it because Z.ge / R.ge don't reduce). -/
theorem pb_lra_term_ge_axiom_free
    (n : Real) (h : 5 ≤ n) : n ≥ 4 := by
  proof_broker_term [z3]

#print axioms pb_lra_term_ge_axiom_free

/-- LRA comparison goal `(>)`: `(h : 5 ≤ n) ⊢ n > 3`. Same instance
    reduction trick as `≥`, routes through `rFarkasGoalLt2`. -/
theorem pb_lra_term_gt_axiom_free
    (n : Real) (h : 5 ≤ n) : n > 3 := by
  proof_broker_term [z3]

#print axioms pb_lra_term_gt_axiom_free

/-- LRA equality goal: `(h1 : n ≤ 5) (h2 : 5 ≤ n) ⊢ n = 5`. Core's
    `evalProofBrokerTerm` detects the Real-typed Eq via the
    extension's `reifyType`, applies `le_antisymm` (Mathlib's
    generic version, not `Int.le_antisymm`), and recurses on each
    direction. The trivial-K=0 case for each direction routes
    through `rFarkasGoalLe2`'s strict-aware path. Mirror of Rocq's
    `pb_lra_term_eq_axiom_free`. -/
theorem pb_lra_term_eq_axiom_free
    (n : Real) (h1 : n ≤ 5) (h2 : 5 ≤ n) : n = 5 := by
  proof_broker_term [z3]

#print axioms pb_lra_term_eq_axiom_free

/-- Strict-`<` hypothesis on a Le-goal: `(h : 0 < x) ⊢ 0 ≤ x`. The
    closer weakens `h` via `rStrictNegToNonpos` and routes through
    `rFarkasGoalLe2`'s standard path; weakening is information-
    preserving here because the Le-goal's strict-aware contradiction
    comes from the neg_goal's Lt-shape, not from `a1`. -/
theorem pb_lra_term_le_goal_strict_a1_axiom_free
    (x : Real) (h : 0 < x) : 0 ≤ x := by
  proof_broker_term [z3]

#print axioms pb_lra_term_le_goal_strict_a1_axiom_free

/-- Strict-`<` hypothesis on a Lt-goal: `(h : 0 < x) ⊢ 0 < x`. Linear
    sum is exactly zero; strictness must flow through `a1` via the
    dedicated `rFarkasGoalLt2StrictA1` (the standard `rFarkasGoalLt2`
    would require K > 0 strictly and can't close this trivial-K=0
    case). -/
theorem pb_lra_term_lt_goal_strict_a1_axiom_free
    (x : Real) (h : 0 < x) : 0 < x := by
  proof_broker_term [z3]

#print axioms pb_lra_term_lt_goal_strict_a1_axiom_free

/-- Strict-`<` hypothesis on a Ge-goal: `(h : 0 < x) ⊢ x ≥ 0`. Same
    proof shape as the Le-goal variant via Lean's `≥` instance
    reduction. -/
theorem pb_lra_term_ge_goal_strict_a1_axiom_free
    (x : Real) (h : 0 < x) : x ≥ 0 := by
  proof_broker_term [z3]

#print axioms pb_lra_term_ge_goal_strict_a1_axiom_free

/-- Strict-`<` hypothesis on a Gt-goal: `(h : 0 < x) ⊢ x > 0`. Same
    as the Lt-goal variant via instance reduction; routes through
    `rFarkasGoalLt2StrictA1`. -/
theorem pb_lra_term_gt_goal_strict_a1_axiom_free
    (x : Real) (h : 0 < x) : x > 0 := by
  proof_broker_term [z3]

#print axioms pb_lra_term_gt_goal_strict_a1_axiom_free

end ProofBroker.TestMathlib
