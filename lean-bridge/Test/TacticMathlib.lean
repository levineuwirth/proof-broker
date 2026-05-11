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

end ProofBroker.TestMathlib
