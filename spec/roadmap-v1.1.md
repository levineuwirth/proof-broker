# Proof Brokerage — roadmap v1.1 (the R-series)

Written 2026-09-05 at R5. This document supersedes the phase sequence
of the v1.0 roadmap (`proof-brokerage-roadmap.tex`, kept unchanged as
the historical plan; its appendix points here). The spec v1.1 delta
that accompanies it is `delta.md §7`; the per-phase decision records
are `delta.md §5`. Nothing here states a count of the shipped system:
counts live in the README status table, which is generated from the
committed sources and gated in CI.

## 1. What the v1.0 phases became

| v1.0 phase | planned outcome | what happened (as recorded) | record |
|---|---|---|---|
| 0 Foundations | repository, schemas, tooling, FFI spike | delivered; OCaml instead of Rust; the spike measured marshaling cost and the language decision held | `delta.md §1–2.1`, `RETROSPECTIVES/phase-0.md` |
| 1 Skeleton | end-to-end Tier 1 dispatch, Lean + cvc5 | delivered; the spec-revision checkpoint at its exit was deferred (`delta.md §4.4`) and is delivered by `delta.md §7` at R5 | `delta.md §2.2`, `§7` |
| 2 Core | Tier 3 with Alethe; full IR rewriter; metadata richness; lifting | the replayer (2.6) was delivered beyond scope as the Alethe walker (`delta.md §7.7`); the passes are three of six; metadata emission, refinement witnesses and lifting (2.1–2.3, 2.7) were NOT delivered in Phase 2 — they are R2–R3. The old README's "Phase 2 shipped end-to-end" was an overstatement | `delta.md §2.3`, `§5.3–5.6` |
| 3 Breadth | Vampire + LLM-as-backend; concurrent dispatch | structurally complete on both bridges; TSTP is provenance + automation, not a replayer (`delta.md §7.4(c)`); concurrent dispatch is Lean-only (Rocq dispatches sequentially — decide-list) | `delta.md §2.4.1`, `RETROSPECTIVES/phase-3-rocq-parity.md` |
| 4 Probe | Rocq architectural probe, Tier 0+1 | the shell calculus survived a second home system and Rocq exceeded the probe scope (Tier 1 term mode, walker, ℕ lifting); the metadata half of the IR was first probed on real goals in R3; exit criterion 4.4 (cross-bridge IR round-trip test) is still open | `delta.md §2.5.1`, `RETROSPECTIVES/phase-4.md` |
| 5 Polish | Tier 2 lemma list, dashboard, build path, cache, docs | re-scoped to term-mode parity (delivered); every original item is demoted (`delta.md §7.4`) or a decide-list row (§4 below) | `delta.md §2.6`, `RETROSPECTIVES/phase-5.md` |
| "6" | (not in the v1.0 roadmap) | two different things — see §2 | — |

## 2. The "Phase 6" double meaning, resolved

The v1.0 roadmap defines Phases 0–5. Two later bodies of work were
both labelled "Phase 6" in this repository:

- **Phase 6-D (distribution).** The cross-platform distribution work
  that `delta.md §2.6` moved out of Phase 5: the `sdk-cross-platform`
  CI matrix, the `dune install` layout, and the macOS code-signing
  scaffold (`sdk/ffi/packaging/macos-sign.sh`). Its first half shipped;
  the prebuilt per-platform bundle is the "distribution bundle" row in
  §4. The comments in `.github/workflows/validate.yml` and
  `sdk/ffi/packaging/` that say "Phase 6" mean this.
- **Phase 6-W (walker scale).** The walker scale profile
  (`RETROSPECTIVES/phase-6-scale.md`, `tools/profile_walker.py`,
  `corpus/profile.json`). It is part of the walker arc (`delta.md
  §7.7`) and its production-path gaps were closed by R1; the README
  phase map records it under R1.
- **"Phase 7"** appears once, in `RETROSPECTIVES/phase-5.md`, as a
  hypothetical anchor for non-arithmetic theory closers. It was never
  a phase; the question (does the universe-polymorphic term-mode idiom
  generalize beyond LIA/LRA) is an open question in §5, not a row.

Rule from here: the v1.0 numbering is frozen as history — cited as
"Phase N" only for what was done under that name — and new work is
R-numbered.

## 3. The R-series

Each phase ends at a checkpoint that a fresh adversarial review session
adjudicates in appended rounds until convergence (at least two rounds
for a phase that touches soundness); a phase is DONE only when its own
gate passed and the review converged. The gate is the contract; the
calendar was a pacing guide and is not reproduced.

| phase | goal | gate (all rows must hold) | delivered |
|---|---|---|---|
| R0 | re-green and re-arm: CI green, local parity, repo hygiene, honest status table | CI green on `main` with the dune pin; SDK, Rocq and Lean legs green locally; branch protection on; stale branches gone; README counts script-derived | 2026-08-31, #84 and #88 |
| R1 | close the walker's production path | the live-strict corpus suite closes on both bridges in CI; the rule-parity tripwire covers three consumers (both walkers and the SDK mint gate); every corpus trace is live-mintable | 2026-09-01, #89 |
| R2 | make the certificate load-bearing | a zero-sentinel `rewrite_trace_hash` is impossible; `verify` consumes the trace; the identity-trace guard gates the term-mode and walker closers; manifest checks in `check.py` | 2026-09-01, #90 |
| R3 | specialization and lifting: ℕ→ℤ (M1), polymorphic α (M2), definitional unfolding inverted (M3) | spec Example 1 as written closes live on Lean through a real `type_specialization` and lifts; ℕ goals close with unchanged footprint; Rocq port of M1 (M2/M3 Rocq: recorded deferrals) | 2026-09-02, #91 and #92 (side PR #93: the Rocq decimal leaf) |
| R4 | external demo: `by proof_broker` on a downstream Lake project's ℕ/ℤ LIA and UFLIA obligations | the D1–D3 obligation sets close from an external Lake project; footprints within the classical ceiling, any widening listed with its closer; write-up delivered | 2026-09-05, #94 |
| R5 | spec v1.1 delta, roadmap v1.1, docs consolidation | delta entries for every R1–R4 decision; D6 demotions recorded; status table and README agree with CI | this document and `delta.md §7`; closes at its review |

After R5 the plan is the decide-list below: nothing is scheduled, every
row has a gate so it can be picked up cold.

## 4. Decide-list (unscheduled; each row has a gate)

| item | gate when picked up | notes |
|---|---|---|
| LRA walker (`Real`, `p/q` literals, `la_mult_pos`, an LRA arm) | ≥ 4 LRA corpus goals replay live on both bridges | the walker is LIA/UF/UFLIA today |
| Faithful arithmetic leaves | the corpus's `la_*` leaves close in term mode from the `:args` coefficients, no `omega`/`lia` at the leaves; `profile.json` gains a `leaves_term_mode` figure | makes the walker fully "cert IS the proof" (`delta.md §7.7`) |
| Corpus growth + in-build timings | ≥ 30 goals (adding ite and nested ∀∃ shapes), a ≥ 3000-step scale point, and a tolerance-gated timing artifact produced by the build | needs `ite` in the IR and `Smtlib.emit`; this is where the v1.0 performance budgets go (§5) |
| Property tests (`qcheck`) for round-trip invariants | serialize→deserialize, rewrite→invert and dispatch→lift properties under shrinking, on both codecs | v1.0 cross-phase item; `tools/fuzz_resolution.py` covers the resolution algebra today |
| Default tier order in parallel dispatch | either the spec text adopts the driver's rule (`tier_preference` first, then highest numeric tier) or the driver adopts the spec's `1 > 3 > 2 > 0` with a behaviour-change record and tests | `delta.md §7.6`; not decided at R5 |
| Example 3 (quotient) live | a Lean or Rocq reifier emits a quotient goal, the `quotient_elimination` pass fires in the trace, and the lifted term inverts it | fixture-only since Phase 1 |
| Cross-bridge IR round-trip test | an IR serialized by one bridge parses through the other's decoder, automated in CI | v1.0 Phase 4 exit criterion 4.4 |
| cvc5-ff uniqueness adapter | the verinf owner's yes; an IR theory tag for prime fields; a uniqueness-query corpus | the demo write-up's decide-list pointer |
| Certificate cache + build path | a design memo per `delta.md §3.2`; invalidation on model identity for LLM certs | spec §8.5, §7.1 |
| Distribution bundle + notarization | a prebuilt `.so` per CI-matrix platform; the signing secrets | `delta.md §7.4(f)`; second half of Phase 6-D |
| Rocq concurrency, cancellation token, per-pass timeout | parity with Lean `run_parallel`; a cancellation token through `Adapter.t`; `timeout_per_pass_ms` enforced | `delta.md §7.1` (§5.5–5.7, §7.5 rows) |
| Rocq ports of the R3-M2/M3 and R4 reifier work | the README's "Rocq lifting deferrals" row empties as each record's deferral marker is lifted | `delta.md §5.5–5.7` |
| `(using rocq …)` migration | a rocq-runtime release with `dune ≥ 3.24` | WATCH marker in `dune-project` and `validate.yml` |
| rocq 9.2 `Assumptions.assumptions` API migration | the Rocq bridge builds on the 9.2 stack with its allowlist unchanged; the audit-H1 gate gets the deferred negative test (a hallucinated `Axiom`/`admit` in an LLM script); then the `< 9.2` pin drops | `rocq-bridge/src/llm_replay.ml`; WATCH marker |
| cvc5 bump | traces regenerated, coverage/profile/snapshots updated in one PR | the playbook in `corpus/README.md` |
| Tier 0 as a trust expansion; ITP-to-ITP dispatch | see `delta.md §7.4(a)`: a new closure path, fail-closed negative test, strict entry point, term-level trust annotation | out of v1 |
| Tier 2 lemma list | see `delta.md §7.4(b)`: a lemma-list-producing backend and a corpus to measure reconstruction on | out of v1 |
| TSTP per-step replay | see `delta.md §7.4(c)`: a corpus FOL goal closed from its derivation alone | out of v1 |
| CBOR wire format | see `delta.md §7.4(e)`: a measured marshaling share of dispatch wall-clock a consumer finds unacceptable | profiling-gated refactor |
| Dashboard; `unknown`/`error` certificate envelopes; rule-based routing; Tier 4 | a consumer who needs them | out of v1 (`delta.md §7.3`) |

## 5. Cross-phase concerns from v1.0, disposed

- **Soundness audit cadence** ("audited at the end of each phase by
  someone other than the implementer"). Replaced by the R-series
  review protocol: every checkpoint is adjudicated by a fresh session
  that runs the full harness, attacks the handoff, and appends numbered
  rounds until convergence; the one-off repository audit
  (`AUDIT.md`, 2026-05-17) and its numbered fix passes are the
  precedent. The trust gate itself is CI (`tools/check_axioms.py`).
- **Performance budgets** (30 s interactive, 5 min build path, sub-second
  serialization/rewriting/lifting). Not adopted as budgets: nothing in
  the build measures against them. What exists is the walker cost
  profile (`corpus/profile.json`, structural predictors, gated) and the
  demo's per-obligation table generated from the `PROOF_BROKER_REPORT`
  line (dispatch, verify and tactic wall per call). Scheduled as the
  "corpus growth + in-build timings" row above; its gate is a
  tolerance-gated timing artifact, which is the form a budget takes
  in this repository.
- **Test coverage strategy.** Unit, integration and regression tests
  exist on every surface; the live-strict corpus suites are the
  regression set for the walker; property tests exist for the
  resolution algebra (`tools/fuzz_resolution.py`, with an independent
  oracle and a negative control) and nowhere else — the `qcheck`
  round-trip suite is a decide-list row.
- **Versioning policy.** Applied as written: v1.1 is additive-optional
  inside `schemas/v1.0/` and the registry stays at `1.0` with
  additions and `v1: false` demotions only (`delta.md §7`,
  "Versioning").
- **Risk register.** The v1.0 risks that materialized are recorded
  where they hit: Alethe replayer scope (HIGH) became the walker arc;
  Rocq schema fit (HIGH) came in LOW; Lean C-ABI churn (`delta.md §5`
  condition 5) tripped once at R0.5 and is the one live
  reconsideration trigger; the Tier 2 rate risk resolved by demotion
  on other grounds (`delta.md §7.4(b)`).

Open question carried without a row: whether the universe-polymorphic
term-mode idiom generalizes beyond LIA/LRA or whether BV/UF need their
own closers (`RETROSPECTIVES/phase-5.md`'s "Phase 7" remark).

## 6. The v1.0 decision points, revisited

- **Phase 1 exit — "has the IR/spec held up?"** Held for the shell; the
  metadata half was unexercised until R3 and then held on real goals
  with two v1.1-bound additive schema changes. The v1.1 delta this
  decision point asked for is `delta.md §7`.
- **Phase 4 exit — "did the Rocq probe validate the architecture?"**
  The shell calculus, yes (Phase 4); the metadata-bearing half, yes on
  Lean and for ℕ→ℤ on Rocq (R3), with the α and def-unfold Rocq ports
  deferred by record. Cross-bridge IR round-trip remains open (§4).
- **Phase 5 exit / pre-release — usability, Tier 2 demotion clause,
  dashboard, CI integration.** Tier 2's lemma-list form is formally
  demoted with documentation (`delta.md §7.4(b)`); the dashboard and
  build-path CI integration were not built (§4). There is no "v1.0
  complete" declaration: the R-series gates are the release criteria,
  phase by phase, and the README status table is the current state.

## 7. Not addressed here

As in v1.0: staffing, funding, community process, productionization.
Additionally: the external demo project and the verinf linkage live
outside this repository (the R4 write-up is delivered there).
