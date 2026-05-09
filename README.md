# Proof Broker

Implementation work tracking the Proof Brokerage Architecture spec v1.0
(see `spec/`). v1 brokers proof goals from Lean 4 and Rocq through an
intermediate representation, an IR rewriter, and per-backend adapters
to SMT solvers, ATPs, and LLM provers, then verifies returned
certificates and lifts the resulting proof terms back to the home
system. Roadmap and refcard live in `spec/`; `delta.md` records
post-spec engineering decisions (notably the OCaml language flip).

## Status

Phases 0 (Foundations), 1 (Skeleton), 2 (Core), and 4 (Rocq probe)
have shipped end-to-end. Phase 3 (Breadth) and Phase 5 (Polish) are
in progress / open. See `delta.md §2` for per-phase status and
`RETROSPECTIVES/phase-{0,4}.md` for retrospectives. Trust footprint
of the shipped tactics is gated by `tools/check_axioms.py` against
`tools/axiom_allowlist.json` — every `*_axiom_free` theorem in
`lean-bridge/Test/Tactic.lean` and `rocq-bridge/theories/Test.v`
either closes axiom-free or pulls only the documented Lean / Rocq
core axioms.

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
  dispatcher, cvc4/cvc5/z3 adapters, FFI shim used by Lean
- `lean-bridge/` — Lean 4 plugin: reifier, the `proof_broker` tactic,
  the optional `ProofBrokerMathlib` LRA opt-in
- `rocq-bridge/` — Rocq plugin (Phase 4 probe): direct-link to the
  OCaml SDK, `proof_broker` / `proof_broker_term` tactics
- `tools/` — Python validators, schema cross-checks, axiom-trust gate
- `RETROSPECTIVES/` — phase-by-phase post-mortems
