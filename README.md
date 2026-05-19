# Proof Broker

Implementation work tracking the Proof Brokerage Architecture spec v1.0
(see `spec/`). v1 brokers proof goals from Lean 4 and Rocq through an
intermediate representation, an IR rewriter, and per-backend adapters
to SMT solvers, ATPs, and LLM provers, then verifies returned
certificates and lifts the resulting proof terms back to the home
system. Roadmap and refcard live in `spec/`; `delta.md` records
post-spec engineering decisions (notably the OCaml language flip).

## Status

Phases 0 (Foundations), 1 (Skeleton), 2 (Core), 4 (Rocq probe), and
5 (term-mode parity) have shipped end-to-end. Phase 3 (Breadth) is
in progress — the Vampire path is complete end-to-end: M1 (ATP
adapter + TPTP-FOF/THF serializer + Tier-0 dispatch), M2 (TSTP
parser + fail-closed Tier-3 *provenance* verifier — no smuggled
axioms, refutes the negated goal, reaches `$false`; inference
steps are not individually re-derived, the home-system closer is
the kernel check), and M3 (Lean higher-order reifier +
verdict-gated `aesop` HOL closer). The roadmap §Phase-3 exit
criterion is met: the worked function-composition goal
(`examples/example2-…`) closes `by proof_broker` through real
Vampire, axiom-free (footprint `[propext]`). The remaining
Phase-3 roadmap items — LLM-as-backend, LLM-assisted
reconstruction, concurrent dispatch — are untouched and tracked
separately.
Phase 6 (cross-platform distribution + polish) carries the displaced
original-Phase-5 scope. See `delta.md §2` for per-phase status and
`RETROSPECTIVES/phase-{0,4,5}.md` for retrospectives.
Term-mode reconstruction (Phase 5 deliverable) covers the full Tier 1
+ Tier 2 Farkas cert vocabulary on both bridges — comparison goals
(≤ / < / ≥ / > / =), all four inequality hypothesis shapes plus
their negations, equality hypotheses with signed coefficients,
rational coefficients, arity-N premises, and arity-N disjunctions in
the Tier 2 case-split path. Trust footprint of the shipped tactics
is gated by `tools/check_axioms.py` against `tools/axiom_allowlist.json`
— every `*_axiom_free` theorem in `lean-bridge/Test/Tactic.lean` and
`rocq-bridge/theories/Test.v` either closes axiom-free or pulls only
the documented Lean / Rocq core axioms (140 entries after the
post-Phase-5 dead-code cleanup; Phase 5 closed at 150).

## Layout

- `spec/` — specification, refcard, roadmap (TeX sources)
- `schemas/v1.0/` — JSON Schemas for IR, certificate, refinement
  record, adapter manifest, rewrite trace
- `registry/` — versioned patterns registry (logic features,
  fragments, theory tags, axiom shapes, concept tags, construction
  kinds)
- `examples/` — hand-written reference IR documents for the spec §12
  worked examples; canonical fixtures for downstream components
- `sdk/` — OCaml shared library: IR rewriter, certificate verifier,
  dispatcher, cvc4/cvc5/z3 adapters, the Vampire ATP adapter
  (Phase 3 M1: TPTP-FOF/THF serializer + Tier-0 dispatch; M2:
  TSTP parser + fail-closed Tier-3 provenance verifier wired into
  the certificate verifier), FFI shim used by Lean
- `lean-bridge/` — Lean 4 plugin: reifier (LIA + the Phase-3
  higher-order/FOL fragment), the `proof_broker` tactic, the
  optional `ProofBrokerMathlib` opt-in (LRA `linarith` closer +
  the HO `aesop` closer for the Vampire path)
- `rocq-bridge/` — Rocq plugin (Phase 4 probe): direct-link to the
  OCaml SDK, `proof_broker` / `proof_broker_term` tactics
- `tools/` — Python validators, schema cross-checks, axiom-trust gate
- `RETROSPECTIVES/` — phase-by-phase post-mortems
