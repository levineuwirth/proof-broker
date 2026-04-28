# Proof Broker

Implementation work tracking the Proof Brokerage Architecture spec v1.0
(see `spec/`). v1 brokers proof goals from Lean 4 (and a Rocq probe)
through an intermediate representation, an IR rewriter, and per-backend
adapters to SMT solvers, ATPs, and LLM provers, then verifies returned
certificates and lifts the resulting proof terms back to the home
system. Roadmap and refcard live in `spec/`.

Currently in **Phase 0** (foundations: schemas, registry, reference
IRs).

## Layout

- `spec/` — specification, refcard, roadmap (TeX sources)
- `schemas/v1.0/` — JSON Schemas for IR, certificate, refinement
  record, adapter manifest, rewrite trace
- `registry/` — versioned patterns registry (logic features,
  fragments, theory tags, axiom shapes, concept tags, construction
  kinds)
- `examples/` — hand-written reference IR documents for the spec §12
  worked examples; canonical fixtures for downstream components
