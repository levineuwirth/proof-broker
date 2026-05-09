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

end ProofBroker.TestMathlib
