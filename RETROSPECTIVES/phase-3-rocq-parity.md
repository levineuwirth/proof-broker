# Phase 3 Rocq parity retrospective

After Phase 3 closed on the Lean side (PRs #31–#36, May 2026 — Vampire/HOL
path, concurrent dispatch, LLM-as-backend, LLM-assisted reconstruction),
the Rocq plugin lagged behind. Phase 3 Rocq parity (PRs #37/#38/#39)
caught the Rocq bridge up to structural parity in four milestones:

* **M1** — HO reifier (`Prod`→`Forall`/`Implies`, parenthesized arrow
  domains, `Eq` at function type, HOL fragment detection), HOL/FOL
  closer dispatch, an opt-in `ProofBrokerHammer` package backed by
  `coq-hammer-tactics` (mirror of `ProofBrokerMathlib`/`aesop`), and
  the worked-example test `pb_hol_function_composition_axiom_free`.

* **M2** — LLM-replay closer with an audit-H1 axiom-footprint gate
  built on Rocq's kernel `Assumptions` API (the same API `Print
  Assumptions` calls internally), plus a CI-stable `llm_replay_test`
  TACTIC EXTEND.

* **M3** — bridge-aware SDK: `Adapter_llm` and `Llm_reconstruct` pick
  a `dialect` based on `ir.source_system.name` (Lean → Lean syntax +
  `lean-tactic-script`; Rocq → Rocq Stdlib syntax + Ltac +
  `rocq-tactic-script`). Plus the reconstruction-fallback
  `Proofview.tclORELSE` wrap on Rocq's `close_or_fail` (mirror of
  Lean's `closeOrFailPrimary` + `closeOrFail` split from PR #36).

* **M4** — this retrospective, README/delta sync.

## Easier than expected

**Cross-bridge SDK reuse.** Because the SDK (adapters, dispatch
driver, `Tier3_tptp` verifier, `Llm_reconstruct`) was already shared
between bridges, M1/M2/M3 were almost entirely plugin-side wiring.
None of the substantive Phase-3 logic (TSTP parser, dispatch driver's
concurrent runner, the LLM HTTP transport, the reconstruction prompt
builder) needed cross-bridge work — only the rendering layer at the
boundary, and even that consolidated cleanly into a `dialect` record
in `Adapter_llm`. The architectural payoff predicted by `delta.md
§1.1` ("the IR is genuinely cross-system or accidentally
Lean-shaped") materialized empirically: every shared piece worked
on the Rocq side unchanged.

**Rocq's kernel `Assumptions` API as the audit gate.** M2's
biggest unknown going in was how to gate the LLM-replayed proof
term's axiom footprint without a `Lean.collectAxioms` equivalent.
The answer turned out to be cleaner than expected: `Print
Assumptions` itself calls `Assumptions.assumptions` in
`rocq-runtime/vernac`, and that function takes `Constr.t` directly
(not a registered `GlobRef.t`). A sentinel `VarRef` "owner" and a
dummy `indirect_accessor` (safe under `add_opaque:false`) gave us
the same semantic gate Lean's `collectAxioms` provides, in ~60
lines of plugin code. `hauto`'s footprint on the worked example
turned out to be empty — stronger than Lean's mirror, which uses
`[propext, Classical.choice, Quot.sound]`.

**`coq-hammer-tactics` as the `aesop` analogue.** The user-validated
choice in M1 to use `coq-hammer-tactics` rather than the full
`coq-hammer` (no ATP-prediction layer, lighter opam dep) paid off:
the hammer package installed cleanly in CI, `hauto` closed the
worked-example HOL goal on the first try, and the opt-in pattern
(separate `coq.theory` + `Ltac proof_broker_hol_closer ::= hauto.`)
mirrored `ProofBrokerMathlib` exactly.

## Harder than expected

**Drift surface across bridges.** The first M1 PR (#37) needed three
CI rounds before turning green — each round surfacing a Rocq-side
sync point that had drifted behind a Lean-side Phase-3 milestone:
the opam-repo for `coq-hammer-tactics` wasn't in the default opam
repository; the default manifest list lacked Vampire; the
verifier-reason accept arm in `close_or_fail` predated
`Verified_tier3_provenance`. Each was a one-line fix, and after
the third, the trust gate green-lit the new HOL test with an
empty axiom footprint.

The lesson, captured in the project-memory
`project-rocq-parity-sync-points`: four specific sites in the Rocq
plugin (`load_default` / `adapter_registry` / `close_or_fail`'s
verified-reason arm / `render_path`'s `ok` boolean) drift behind
the Lean side every time a new adapter or verifier reason lands.
M2's PR (#38) used this list preemptively and landed clean on the
first CI try; M3's PR (#39) did too.

**Local Rocq toolchain unusable.** A known `rocq-core 9.1.1`
build bug (`failed to locate Coq kernel package in split build
mode: rocq-runtime.kernel`) prevented installing `rocq-stdlib`
on my local opam switch throughout the work, so the Rocq theory
build path (every `.v` file in `rocq-bridge/theories/`,
`rocq-bridge/hammer/`) never compiled locally. The mitigation —
written up as the `feedback-ci-iteration` memory — was to
exercise everything I could locally (SDK build, plugin
OCaml-side build, SDK test suite, Python schema/gate suite, JSON
validity) and accept that CI is the test environment for the
Rocq theories. Substantive commit messages each round kept the
audit trail intelligible.

**Bridge-awareness as a shared-SDK concern.** Going into M3, I'd
been thinking of LLM bridge-awareness as a Rocq-side wiring
problem. It's not — the prompt and trace_format are SDK
concerns: the adapter, not the bridge, decides what syntax to
ask for. The `dialect` record's right home turned out to be
`Adapter_llm`, not the plugin. This also kept `Llm_reconstruct`
trivially bridge-aware (one shared `dialect_of_ir`).

## Carried forward

* **BV / UF reach on Rocq.** Stdlib still doesn't ship a cheap
  `BitVec` library; the Phase-4 retro flagged this as deferred
  pending a third-party dep. Unchanged after Rocq parity.

* **Cross-bridge IR round-trip validation.** The original Phase 4
  exit criterion called for the same reference IRs serialized by
  one bridge to parse cleanly through the other's deserializer.
  Achievable in principle (the SDK is bridge-agnostic, and both
  bridges produce/consume IRs through the shared `Codec`), but
  no end-to-end automated round-trip test exists yet. Tracked.
  *(As of 2026-08-30: still absent; tracked in the roadmap.)*

* **`coq.theory` → `rocq.theory` dune flip.** Per `dune-project`'s
  note, dune 3.22 didn't ship `(using rocq …)`. When it does,
  switching is a one-line change with no semantic consequences.

* **Rocq retrospective coverage for Phases 1–2.** Phase-0/4/5 retros
  exist; Phase-1/2/3 (Lean-side) didn't get their own retros.
  This Phase-3-Rocq-parity retro fills part of the gap; the
  others could land as documentation-only PRs if useful.
