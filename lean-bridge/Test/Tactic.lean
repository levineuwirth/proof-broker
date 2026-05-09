/-
End-to-end tactic-elaboration tests for `ProofBroker.proof_broker`.

Each `example` below is a real Lean goal closed by the broker:
the tactic reifies the goal + Prop hypotheses into a LIA IR, hands
it to `runDispatchBroker` (consulting the cvc4/cvc5/z3 manifests
under `examples/`), re-checks the minted Tier 1 Farkas cert via
`runVerifyCertificate`, and closes the goal — for the LIA Tier 1
case via core Lean's `omega` (axiom-free, gated on cert
verification), for any other tier/fragment via the
`proofBrokerCertSound` trust axiom (removable per-tier).

Build success of this library *is* the test: any failure to
elaborate `by proof_broker` (no available adapter, cert that
fails to re-verify, reified IR shape outside the LIA fragment)
fails the build. The library has no precompile output and is
not imported by anything else; its sole purpose is to exercise
the elaboration-time FFI path.

Pre-condition: the test must be invoked with cwd =
`lean-bridge/`, so that the tactic's manifest loader finds
`../examples/manifest-{cvc4,cvc5,z3}.json`. Override via the
`PROOF_BROKER_EXAMPLES_DIR` env var if needed.
-/

import ProofBroker

-- The broker closes the goal with an axiom keyed on the goal
-- proposition; the resulting proof term doesn't textually mention
-- the hypotheses that were Farkas-combined inside the cert, so
-- Lean's unused-variable linter would otherwise flag every test.
set_option linter.unusedVariables false

namespace ProofBroker.Test

/-- Closed-form Farkas: `n + m = 10` and `0 ≤ m` together force `n ≤ 10`.
    Coefficients (h1=1, h3=1, neg_goal=1) sum to a contradiction. -/
example (n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker

/-- Single-hypothesis bound transfer. -/
example (n : Int) (h : n ≤ 5) : n ≤ 10 := by
  proof_broker

/-- Trivial transitive case. -/
example (a b c : Int) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  proof_broker

/-- Equality propagated through addition. -/
example (x y : Int) (h : x = y) : x + 1 ≤ y + 1 := by
  proof_broker

/-- Adapter-list syntax: restrict dispatch to a single adapter. -/
example (n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker [cvc5]

/-- Adapter-list syntax with order: input order is respected
    (preferHigherTier=false), so cvc4 is tried first even though
    cvc5 has a higher max-tier capability. -/
example (n : Int) (h : n ≤ 5) : n ≤ 10 := by
  proof_broker [cvc4, cvc5]

/-- Verbose form: `proof_broker?` emits a `logInfo` summary of the
    extraction path (IR shape, dispatch attempts + timing, cert
    tier/format, verify outcome) and then closes the goal as
    normal. The build will print one info line per invocation. -/
example (n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker? [cvc4]

/-- Named LIA goal proven via the default `proof_broker` form,
    which `preferHigherTier := true` floats to cvc5's Tier 3
    alethe-2024 path. Even with a Tier 3 cert (no Lean-side
    Alethe walker yet) the closer is `omega` because the goal is
    LIA — cert verification gates the call, omega does the rest.
    omega is axiom-free, so this theorem's transitive axiom set
    must not contain `proofBrokerCertSound`; verified inline by
    `#print axioms` below. -/
theorem lia_axiom_free
    (n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker

#print axioms lia_axiom_free

/-- Same theorem pinned through cvc4 (Tier 1 Farkas) — confirms
    the dispatch-on-fragment closer doesn't regress on the
    original Tier 1 path that motivated the omega-based closure
    in the first place. -/
theorem tier1_lia_axiom_free
    (n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker [cvc4]

#print axioms tier1_lia_axiom_free

/-- BV vertical-slice gate: a closed `BitVec 8` arithmetic
    equality routes through the broker (QF_BV → cvc5/z3 oracle
    → cert-gated `decide`). The broker is overkill for a trivially
    decidable goal — the architectural payoff is showing the BV
    pipeline runs end-to-end (reifier emits `BitVec(8)` / `BV.add`,
    SMT-LIB serializer emits `(_ bv5 8)` / `bvadd`, the cvc5 / z3
    adapter dispatches under QF_BV, the verifier envelope-checks,
    the closer fires `decide`). `decide` is axiom-free, so this
    theorem's transitive axiom set should match the LIA path's
    `[propext, Quot.sound]` (or fewer) — verified by `#print
    axioms` below. -/
theorem bv_axiom_free : (5 : BitVec 8) + 3 = 8 := by
  proof_broker

#print axioms bv_axiom_free

end ProofBroker.Test
