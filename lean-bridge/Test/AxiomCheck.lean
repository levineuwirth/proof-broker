/-
Axiom-dependency check for the LIA Tier 1 closer.

A `verifiedFarkas` cert over LIA closes via core Lean's `omega`
decision procedure (gated on the broker's Farkas verifier
accepting the witness). `omega` is itself axiom-free, so any
goal closed on this path must NOT depend on the
`proofBrokerCertSound` trust axiom.

This file is its own Lean module so it's compiled in its own
elaborator process: a single `proof_broker` invocation followed
by a single `#print axioms` command. Splitting it off from
`Test/Tactic.lean` sidesteps an unrelated OCaml-runtime
lifecycle issue that surfaces when many `proof_broker` calls and
post-tactic kernel-traversing commands (`#print axioms`,
`Lean.collectAxioms`) coexist in one module.

Build success of this library is the test: any future change
that re-introduces `proofBrokerCertSound` into the LIA Tier 1
closer's dependency closure surfaces as a `#print axioms` info
line containing `proofBrokerCertSound`. The expectation is the
emitted line lists only core Lean axioms (typically `propext`,
`Classical.choice`, `Quot.sound` plus omega's decision
machinery).

Pre-condition: same as `Test/Tactic.lean` — must run with cwd
under `lean-bridge/` so manifests resolve at `../examples/`.
-/

import ProofBroker

set_option linter.unusedVariables false

namespace ProofBroker.AxiomCheck

/-- Named LIA Tier 1 goal proven via `proof_broker [cvc4]`. The
    explicit adapter list pins the dispatch to cvc4, which has no
    proof-trace path and so always mints a Tier 1 Farkas cert
    (verified via `Farkas.verify` → `verifiedFarkas`). The
    tactic's closer for that combination is `omega`, axiom-free;
    this theorem's transitive axiom set must not contain
    `proofBrokerCertSound`.

    Pinning to cvc4 matters: the bare `proof_broker` form prefers
    higher-tier adapters and so most LIA goals route through
    cvc5's Tier 3 alethe-2024 walker (`verifiedTier3`), which
    still uses the trust axiom because the Lean side hasn't
    reified the alethe walker yet. -/
theorem tier1_lia_axiom_free
    (n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker [cvc4]

#print axioms tier1_lia_axiom_free

end ProofBroker.AxiomCheck
