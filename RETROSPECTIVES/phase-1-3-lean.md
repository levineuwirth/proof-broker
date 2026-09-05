# Phases 1–3 (Lean side) — one combined note, reconstructed from the record

Written 2026-09-05 at R5, not at the time. Phases 0, 4, 5 and the Rocq
half of Phase 3 got retrospectives while the work was fresh; the Lean
side of Phases 1–3 never did (`phase-3-rocq-parity.md` carried the gap
forward). This note fills it from what is on record — the commit
history of 2026-04-29 → 2026-05-21, `delta.md §2.2–2.4.1`, and the
audit that followed (`AUDIT.md`) — and says so where it infers rather
than reports. It is short on purpose: anything it cannot source is
left out, and the numbers of the shipped system are the README status
table's, not this note's.

## What the record shows was built

**Phase 1 — skeleton (2026-04-29 → 05-01).** In three days the SDK
grew from the Phase-0 spike into the shape it still has: Lean-side IR
ADTs with a typed round-trip and a typed error surface; the first
three rewriter passes (propositional simplification, definition
unfolding, quotient elimination) composed into a pipeline that emits a
`Trace.Document`; typed metadata ADTs replacing JSON pass-through;
adapter manifests and capability matching; the certificate envelope
and pre-tier verifier; Tier 1 Farkas verification (Int, then LRA with
strict witnesses); the cvc4 and cvc5 oracle adapters; a refinement
pass from typeclass IR to the LIA primitive; the multi-adapter
dispatch driver; and, on the last day, cvc5's `la_generic` extracted
into a Tier 1 Farkas witness and the case-split Tier 2 form from
disjunctive hypotheses. The exit criterion — end-to-end Tier 1
dispatch on the simplest goals — was met inside the phase.

**Phase 2 — core (2026-05-04 → 05-07).** The Tier 3 stack and the
first tactic: the `alethe-2024` passthrough payload and a per-step
re-checker whose rule registry grew commit by commit (equality
cluster, `la_mult_neg` through `Linear_arith` scaling, `hole` /
`rare_rewrite` with a literal-normalization path, the propositional
cluster, `subproof` with scoped local lookups and top-level assume
validation); the cvc5 ladder minting Tier 3 above Tier 2 behind a
fail-closed gate; the internal Farkas closer that rescues a Tier 0
verdict into a Tier 1 witness; the FFI's `verify_certificate` split
into envelope-ok and soundness-ok; Zarith for arbitrary-precision
rationals; the z3 adapter with its proof parser and native Tier 1
extraction; and the `proof_broker` tactic itself, closing LIA goals
through an axiom-free `omega` gated on the verdict, with LRA via an
opt-in Mathlib `linarith` closer. Two commits from this week name
decisions the rest of the project lived with: "Broker prefers
higher-tier capable adapters by default" and "dispatch on fragment,
not tier — LIA always omega".

**Phase 3 — breadth, Lean side (2026-05-19 → 05-21).** After the audit
passes: the Vampire path in three milestones (TPTP serializer and
adapter; the TSTP Tier 3 provenance verifier; the higher-order reifier
and the `aesop` closer under `ProofBrokerMathlib`), concurrent
dispatch on stdlib threads (and the CI regression it caused in
`roundtripTest` — a thread outliving the synchronous call — fixed by
joining, not by retreating), the LLM-as-backend adapter over a `curl`
subprocess, the home-side script replay closer with the axiom-footprint
gate, and LLM-assisted reconstruction of un-replayable Tier 3 traces.
`delta.md §2.4.1` is the contemporaneous record of this phase and
already carries its two scope findings (the Tier 3 verifier is
OCaml-side and large; the reifier was LIA-only).

## What the record shows went well

- **The ladder and the gate, from the first week.** Every adapter
  mints the highest tier whose verifier accepts and falls to the next
  otherwise; the FFI reports envelope and soundness separately. Both
  patterns appear in Phase 1–2 commits and are what later made
  Tier 0's honest disposition (an envelope-verified hint, never a trust
  expansion — `delta.md §7.4(a)`) a description rather than a change.
- **The verdict gates, the kernel proves.** "LIA always omega" made the
  home system re-derive the goal on every path from the start. That is
  the audit-H1 property, and it is why no Phase 1–3 closure ever
  depended on a solver's word; it is also why the certificate was not
  load-bearing until term mode (Phases 4–5) and lifting (R2–R3).
- **One shared SDK.** Phase 3's Rocq parity was "almost entirely
  plugin-side wiring" (`phase-3-rocq-parity.md`), which is the payoff
  of the Phase 1 decision to keep every verifier, adapter and driver
  in the OCaml library.

## What the record shows cost more than planned

- **The Alethe re-checker.** Phase 2's rule registry took most of the
  week and still left the mint gate narrower than what a walker would
  later discharge; the gap (rule names, `hole` reach) was measured in
  the 2026-08-30 review and closed in R1 (`delta.md §5.2, §5.8`). The
  v1.0 risk register had this as the one HIGH item for Phase 2, and it
  was right.
- **The reifier's reach.** Phase 3's higher-order extension was the
  first time the Lean reifier read anything but `Int` LIA; `Nat`, a
  type variable, and definitional constants waited for R3.
- **Fixtures under parallel work.** One commit exists only to
  reconcile z3 proof fixtures produced by parallel agents. The lesson
  the later phases drew — a snapshot test pinned to one solver version,
  regenerated only through a tool — is visible in Phase 6-W's corpus
  discipline. That connection is an inference from the commit
  sequence, not something the commits say.

## Carried forward, as of 2026-09-05

Everything this note could carry forward has already been carried: the
mint-gate reach (R1), metadata and lifting (R3), the Tier 0 / Tier 2 /
TSTP dispositions (`delta.md §7.4`), and the open decide-list in
`spec/roadmap-v1.1.md §4`. Nothing new is added here.
