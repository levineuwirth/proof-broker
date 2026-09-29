# Checkpoint 1 — certificate recovery under changing coefficients and context

**Status: CHECKPOINT, for review. Nothing is committed; no production file is
touched.** Campaign directory `experiments/c1-cert-recovery/`, branch
`r6/c1-cert-recovery`, pass `20260906-204453`.

## Outcome, in a paragraph

The refusal reproduces exactly, and the certificate is **lost in extraction, not
in search**. For isolated site 2 the certificate demonstrably exists over the IR
the tactic actually dispatches — `262144·hhi + 1·neg_goal`, found by an
existence probe and accepted by the SDK's own `Farkas.verify` — yet all three
backends mint tier 0. z3 *does* emit a Farkas theory lemma for it, but over a
goal literal it has already **integer-tightened** (`x ≥ ⌈P/2^18⌉`), with the
2^18 divided out and coefficients `1 1`; the SDK's clause parser cannot read
that application at all (it requires every disjunct to be negated, and z3's is
mixed-polarity), and even if it could, the tightened literal is not a positive
rescaling of the IR's negated goal — which is precisely the `unmatched_literal`
cvc5 reports on the same obligation. With extraction gone, everything falls to
`Farkas_search`, whose coefficient enumeration stops at 3: the multiplier sweep
`C1..C8` cuts exactly there — 1, 2, 3 recovered, 4 and above lost. Site 3 and
E4 succeed for a structural reason, not a lucky one: their goals have two
variables, so no single-variable tightening is available, z3 emits the
direct-from-premises shape over the IR's own literals, and the 2^18 survives
into the witness. Across the 24-case corpus, `omega` and `grind` close every
true case, default `proof_broker` closes 20 of 22 (always through
`gated_omega`), and term mode — the only closer that consumes a certificate —
closes 4 of 22. The smallest repair the evidence supports is in
`sdk/lib/farkas_search.ml` alone, and it is **additive**: leave the existing
enumerating search exactly as it is, and *solve* for the multipliers in exact
rational arithmetic — bounded in support, unbounded in magnitude — only where
that search came up empty. Raising the bound is refuted by measurement
(reaching 262144 puts every case 15–107 orders of magnitude over the module's
own budget). Checkpoint 2 (`reports/checkpoint-2.md`) implements it.

## 1. Baseline

Recorded by `tools/baseline.sh` into `baseline/artifacts-before.txt` (and
re-recorded at the end into `baseline/artifacts-after.txt`, so a rebuild that
moved a binary under the campaign would show as a diff). Checkout HEADs do not
identify what the probe loads, so the loaded binaries are recorded by SHA-256:

| what | identity |
|---|---|
| proof-broker HEAD | `ab6fd19` (branch `r6/c1-cert-recovery`, no tracked file modified) |
| `libpbglue.so` | `12363eb0…f61ce` |
| bridge `…ProofBroker.so` | `93a7ec67…d70ca` |
| `sdk/ffi/proof_broker_ffi.so` | `d0fc0447…7f04e` |
| `ProofBroker/Tactic.olean` | `76a54bd3…b5e087` |
| proof-broker-demo HEAD | `f208e97`, Mathlib olean `9c5bf984…8b97e` |
| VerInf case study | `573e168`, worktree clean, **never written to** |
| Lean / elan | v4.32.0 (`8c9756b2`) / elan 4.2.3 |
| solvers | z3 5.1.0, cvc5 1.3.0, cvc4 1.8, Vampire 5.1.0 |

`diff baseline/artifacts-before.txt baseline/artifacts-after.txt` at the end of
the campaign differs in the recorded timestamp and nothing else: every loaded
binary, olean and manifest has the same hash after the campaign as before it,
and the VerInf worktree still reports zero dirty paths.

All four loaded-binary hashes are **identical** to the ones the completed case
study recorded in `lean/RmsNormBracket/logs/loaded_artifacts.txt`, and
`git diff b4fdd77d..HEAD -- sdk lean-bridge examples registry` is empty: the
code under study has not moved since the case study measured it, even though
the two HEADs differ (that branch was squashed into `ab6fd19`).

The campaign's probe (`tools/probe.sh`) is the case study's probe with this
campaign's own `.build` appended to `LEAN_PATH`; the case study's olean
directory is on that path read-only, so `import RmsNormBracket.Model` resolves
to the artifact whose hash is recorded above. The 8 GB memory cap, the
`EXIT`/`WALL` trailer written outside the memory scope, `PEAK_RSS_BYTES` from
inside it, and `PROOF_BROKER_REPORT=1` are unchanged.

Nothing under `sdk/`, `lean-bridge/`, `examples/` or `registry/` is modified;
`_build/default/sdk/ffi/proof_broker_ffi.so` has the same hash before and after
building the campaign's diagnostic executables.

## 2. The corpus

Enumerated explicitly in `tools/corpus.py`, tabulated with its meaning
annotations in `corpus/CORPUS.md`. Truth values are recomputed independently in
`tools/truth_check.py` (arithmetic, per case, not parsed out of the Lean) and
confirmed by `omega` on every case; a prover's failure is never used as evidence
that a statement is false.

* **Originals, in context** — `O1`..`O4`, the four `-- SITE n` obligations of
  `carry_stage_lift_production`, captured *inside the real proof* by
  `ir/CarryLiftDump.lean` (the case study's `CarryLiftPBTerm.lean` with each
  site's closer replaced by `pb_dump_ir` + `omega`). Their IRs carry 9, 12, 15
  and 20 hypotheses — the same counts the case study's report lines show, so
  the reproduction is exact.
* **Originals, standalone** — `O5` (isolated site 2) and `O6` (E4), verbatim
  from the case study's `experiments/`.
* **Coefficient magnitude** (`C1`..`C8`, *changes the obligation*) — site 2's
  statement with the multiplier at 1, 2, 3, 4, 5, 8, 2^10, 2^18. `C8` is
  byte-identical to `O5` and is kept as a determinism check; it reifies to the
  same IR hash.
* **Presentation** (`P1`..`P6`, *meaning-preserving*) — decimal literal for the
  power, operand order, `≤ P - 1`, the prime as a numeral in the goal, a plain
  ℕ variable instead of a `ZMod` `.val`, and the range check as `≤ 2^42 - 1`.
* **Context** (`R1`..`R4`, *meaning-preserving*) — hypothesis reordering; three
  redundant true range facts; the full in-context site-2 assumption set written
  standalone; six unrelated true linear facts.
* **Boundary** (`B1`..`B4`) — `2^21` (true), `2^22` (**false**), the range check
  widened to `2^46` (**false**), and the exactly tight `v ≤ 70368744161280`
  (true, Farkas residual 1).
* **Held out** (`H1`..`H6`) — defined in `heldout/`, **not run**. No broker
  closer touches them and no result from them enters this diagnosis; `omega`
  alone is run once as a well-formedness and truth check.

Two of the variants are worth naming as *checks that landed*:

* `R3_site2_in_context` reifies to a **byte-identical IR** to in-context `O2`
  (same `ir_sha256` and `final_ir_sha256`). The four `ZMod`-equation hypotheses
  of the real proof are dropped by the reifier anyway, so the standalone
  statement is a faithful stand-in for the site, and its result is the site's.
* `P1_decimal_coef` reifies identically to `O5` (the reifier already normalizes
  `2^18` to `262144`), and `P4_prime_literal` differs before the pipeline but is
  identical after it — the definition-unfolding pass is exactly that difference.
  `P2` (operand order), `P5` (plain ℕ) and `R1` (reordering) do change the IR.

## 3. Results

### 3.1 The completed case study, reproduced

`tools/run_carrylift.sh` elaborates the four `CarryLift` copies (copied
byte-for-byte from the case study) here, two warm passes each, against an
imports-only baseline:

| copy | closes | closers / tiers at sites 1–4 (pass 2) | tactic execution, whole file |
|---|---|---|---|
| `CarryLift` (omega) | 4/4 | — | 137 ms, 121 ms |
| `CarryLiftGrind` | 4/4 | — | 118 ms, 128 ms |
| `CarryLiftPB` | 4/4 | `gated_omega` ×4; cvc5 t3 / cvc4 **t0 oracle** / z3 t1 / cvc4 t1 | 853 ms, 866 ms |
| `CarryLiftPBTerm` | **3/4** | `term_mode_nat` at 1, 3, 4 (cvc4, z3, cvc4); **site 2 refused** (tier-0 cert) | 897 ms, 1.65 s |

Identical to the case study's result — same closers, same tiers, same backends,
same site-2 refusal. (The timings are faster than that report's re-run; the
machine is less loaded now. Nothing in the diagnosis rests on them.)

### 3.2 Closure, by case and closer

`closed` = the closer closed the original goal and the file elaborated (probe EXIT=0). Everything else is that run's own named outcome; none of it is a counterexample.

| case | truth | omega | grind | pb | pbterm | pbterm_z3 | pbterm_cvc5 | pbterm_cvc4 |
|---|---|---|---|---|---|---|---|---|
| `O5_site2_isolated` | TRUE | closed | closed | closed | refused(tier0) | refused(tier0) | refused(tier0) | refused(tier0) |
| `O6_E4` | TRUE | closed | closed | closed | closed | closed | refused(tier0) | refused(tier0) |
| `C1_coef_1` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C2_coef_2` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C3_coef_3` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C4_coef_4` | TRUE | closed | closed | closed | refused(tier0) | refused(tier0) | refused(tier0) | refused(tier0) |
| `C5_coef_5` | TRUE | closed | closed | closed | refused(tier0) | refused(tier0) | refused(tier0) | refused(tier0) |
| `C6_coef_8` | TRUE | closed | closed | closed | refused(tier0) | refused(tier0) | refused(tier0) | refused(tier0) |
| `C7_coef_2p10` | TRUE | closed | closed | closed | refused(tier0) | refused(tier0) | refused(tier0) | refused(tier0) |
| `C8_coef_2p18` | TRUE | closed | closed | closed | refused(tier0) | refused(tier0) | refused(tier0) | refused(tier0) |
| `P1_decimal_coef` | TRUE | closed | closed | closed | refused(tier0) | refused(tier0) | refused(tier0) | refused(tier0) |
| `P2_operand_order` | TRUE | closed | closed | closed | refused(tier0) | refused(tier0) | refused(tier0) | refused(tier0) |
| `P3_le_pred` | TRUE | closed | closed | refused(reify) | refused(reify) | refused(reify) | refused(reify) | refused(reify) |
| `P4_prime_literal` | TRUE | closed | closed | closed | refused(tier0) | refused(tier0) | refused(tier0) | refused(tier0) |
| `P5_plain_nat` | TRUE | closed | closed | closed | refused(tier0) | refused(tier0) | refused(tier0) | refused(tier0) |
| `P6_hyp_le` | TRUE | closed | closed | failed | refused(no cert) | refused(no cert) | refused(no cert) | refused(no cert) |
| `R1_reorder` | TRUE | closed | closed | closed | refused(tier0) | refused(tier0) | refused(tier0) | refused(tier0) |
| `R2_redundant3` | TRUE | closed | closed | closed | refused(tier0) | refused(tier0) | refused(tier0) | refused(tier0) |
| `R3_site2_in_context` | TRUE | closed | closed | closed | refused(tier0) | refused(tier0) | refused(tier0) | refused(tier0) |
| `R4_redundant6` | TRUE | closed | closed | closed | refused(tier0) | refused(tier0) | refused(tier0) | refused(tier0) |
| `B1_true_2p21` | TRUE | closed | closed | closed | refused(tier0) | refused(tier0) | refused(tier0) | refused(tier0) |
| `B2_false_2p22` | FALSE | failed | failed | failed | refused(no cert) | refused(no cert) | refused(no cert) | refused(no cert) |
| `B3_false_wide_bound` | FALSE | failed | failed | failed | refused(no cert) | refused(no cert) | refused(no cert) | refused(no cert) |
| `B4_true_exact` | TRUE | closed | closed | closed | refused(tier0) | refused(tier0) | refused(tier0) | refused(tier0) |

Read across: `omega` and `grind` close every true case (22/22) and close
neither false one. Default `proof_broker` closes 20 of 22 — every one of them
through `gated_omega`, i.e. the certificate gated and `omega` proved. Term mode,
the only closer here that actually consumes a certificate, closes **4 of 22**.

### 3.3 What the broker closers actually did

| case | `proof_broker` closer/backend/tier/format | `proof_broker_term` closer/backend/tier/format |
|---|---|---|
| `O5_site2_isolated` | gated_omega / cvc4 / t0 / oracle | (no report line) refused(tier0) |
| `O6_E4` | gated_omega / z3 / t1 / farkas | term_mode_nat / z3 / t1 / farkas |
| `C1_coef_1` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `C2_coef_2` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `C3_coef_3` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `C4_coef_4` | gated_omega / cvc4 / t0 / oracle | (no report line) refused(tier0) |
| `C5_coef_5` | gated_omega / cvc4 / t0 / oracle | (no report line) refused(tier0) |
| `C6_coef_8` | gated_omega / cvc4 / t0 / oracle | (no report line) refused(tier0) |
| `C7_coef_2p10` | gated_omega / cvc4 / t0 / oracle | (no report line) refused(tier0) |
| `C8_coef_2p18` | gated_omega / cvc4 / t0 / oracle | (no report line) refused(tier0) |
| `P1_decimal_coef` | gated_omega / cvc4 / t0 / oracle | (no report line) refused(tier0) |
| `P2_operand_order` | gated_omega / cvc4 / t0 / oracle | (no report line) refused(tier0) |
| `P3_le_pred` | (no report line) refused(reify) | (no report line) refused(reify) |
| `P4_prime_literal` | gated_omega / cvc4 / t0 / oracle | (no report line) refused(tier0) |
| `P5_plain_nat` | gated_omega / cvc4 / t0 / oracle | (no report line) refused(tier0) |
| `P6_hyp_le` | (no report line) failed | (no report line) refused(no cert) |
| `R1_reorder` | gated_omega / cvc4 / t0 / oracle | (no report line) refused(tier0) |
| `R2_redundant3` | gated_omega / cvc4 / t0 / oracle | (no report line) refused(tier0) |
| `R3_site2_in_context` | gated_omega / cvc4 / t0 / oracle | (no report line) refused(tier0) |
| `R4_redundant6` | gated_omega / cvc4 / t0 / oracle | (no report line) refused(tier0) |
| `B1_true_2p21` | gated_omega / cvc4 / t0 / oracle | (no report line) refused(tier0) |
| `B2_false_2p22` | (no report line) failed | (no report line) refused(no cert) |
| `B3_false_wide_bound` | (no report line) failed | (no report line) refused(no cert) |
| `B4_true_exact` | gated_omega / cvc4 / t0 / oracle | (no report line) refused(tier0) |

### 3.4 Certificate recovery, per case (stage tracer)

`need` is the largest multiplier in the smallest witness the existence probe found over the dispatched IR, re-checked by the SDK's own `Farkas.verify`. `route` is where a verified tier-1 witness came from when the tracer replayed that backend's ladder — **extracted** from the backend's own proof, **fallback** from `Farkas_search`, **none** if neither produced one. It is not the same question as `minted tiers`: cvc5 may prefer its own tier-3 trace over a tier-1 witness it could also have produced (`O1`), and the parallel driver then picks among the minted certs.

| case | inputs | witness exists | support | need | z3 route | cvc5 route | cvc4 route | minted tiers | where lost |
|---|---|---|---|---|---|---|---|---|---|
| `O1` | 10 | witness_exists | 1 | 1 | fallback | fallback | fallback | z3=t1 cvc5=t3 cvc4=t1 | —(recovered: z3 via fallback) |
| `O2` | 13 | witness_exists | 2 | 262144 | none | none | none | z3=t0 cvc5=t0 cvc4=t0 | extraction (z3:no_farkas_th_lemma; cvc5:unmatched_literal) then fallback (sparse_search_exhausted) |
| `O3` | 16 | witness_exists | 3 | 262144 | extracted | none | none | z3=t1 cvc5=t0 cvc4=t0 | —(recovered: z3 via extracted) |
| `O4` | 21 | witness_exists | 2 | 1 | fallback | extracted | fallback | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via fallback) |
| `O5_site2_isolated` | 4 | witness_exists | 2 | 262144 | none | none | none | z3=t0 cvc5=t0 cvc4=t0 | extraction (z3:no_farkas_th_lemma; cvc5:unmatched_literal) then fallback (search_exhausted) |
| `O6_E4` | 11 | witness_exists | 6 | 68719214592 | extracted | none | none | z3=t1 cvc5=t0 cvc4=t0 | —(recovered: z3 via extracted) |
| `C1_coef_1` | 4 | witness_exists | 2 | 1 | fallback | extracted | fallback | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via fallback) |
| `C2_coef_2` | 4 | witness_exists | 2 | 2 | fallback | fallback | fallback | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via fallback) |
| `C3_coef_3` | 4 | witness_exists | 2 | 3 | fallback | fallback | fallback | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via fallback) |
| `C4_coef_4` | 4 | witness_exists | 2 | 4 | none | none | none | z3=t0 cvc5=t0 cvc4=t0 | extraction (z3:no_farkas_th_lemma; cvc5:unmatched_literal) then fallback (search_exhausted) |
| `C5_coef_5` | 4 | witness_exists | 2 | 5 | none | none | none | z3=t0 cvc5=t0 cvc4=t0 | extraction (z3:no_farkas_th_lemma; cvc5:unmatched_literal) then fallback (search_exhausted) |
| `C6_coef_8` | 4 | witness_exists | 2 | 8 | none | none | none | z3=t0 cvc5=t0 cvc4=t0 | extraction (z3:no_farkas_th_lemma; cvc5:unmatched_literal) then fallback (search_exhausted) |
| `C7_coef_2p10` | 4 | witness_exists | 2 | 1024 | none | none | none | z3=t0 cvc5=t0 cvc4=t0 | extraction (z3:no_farkas_th_lemma; cvc5:unmatched_literal) then fallback (search_exhausted) |
| `C8_coef_2p18` | 4 | witness_exists | 2 | 262144 | none | none | none | z3=t0 cvc5=t0 cvc4=t0 | extraction (z3:no_farkas_th_lemma; cvc5:unmatched_literal) then fallback (search_exhausted) |
| `P1_decimal_coef` | 4 | witness_exists | 2 | 262144 | none | none | none | z3=t0 cvc5=t0 cvc4=t0 | extraction (z3:no_farkas_th_lemma; cvc5:unmatched_literal) then fallback (search_exhausted) |
| `P2_operand_order` | 4 | witness_exists | 2 | 262144 | none | none | none | z3=t0 cvc5=t0 cvc4=t0 | extraction (z3:no_farkas_th_lemma; cvc5:unmatched_literal) then fallback (search_exhausted) |
| `P3_le_pred` | — | — | — | — | — | — | — | — | reification (no IR captured) |
| `P4_prime_literal` | 4 | witness_exists | 2 | 262144 | none | none | none | z3=t0 cvc5=t0 cvc4=t0 | extraction (z3:no_farkas_th_lemma; cvc5:unmatched_literal) then fallback (search_exhausted) |
| `P5_plain_nat` | 4 | witness_exists | 2 | 262144 | none | none | none | z3=t0 cvc5=t0 cvc4=t0 | extraction (z3:no_farkas_th_lemma; cvc5:unmatched_literal) then fallback (search_exhausted) |
| `P6_hyp_le` | 3 | no_witness_exists | — | — | none | none | none | z3=FAILED cvc5=FAILED cvc4=FAILED | backend search (z3=sat,cvc5=sat,cvc4=sat) |
| `R1_reorder` | 4 | witness_exists | 2 | 262144 | none | none | none | z3=t0 cvc5=t0 cvc4=t0 | extraction (z3:no_farkas_th_lemma; cvc5:unmatched_literal) then fallback (search_exhausted) |
| `R2_redundant3` | 10 | witness_exists | 2 | 262144 | none | none | none | z3=t0 cvc5=t0 cvc4=t0 | extraction (z3:no_farkas_th_lemma; cvc5:unmatched_literal) then fallback (search_exhausted) |
| `R3_site2_in_context` | 13 | witness_exists | 2 | 262144 | none | none | none | z3=t0 cvc5=t0 cvc4=t0 | extraction (z3:no_farkas_th_lemma; cvc5:unmatched_literal) then fallback (sparse_search_exhausted) |
| `R4_redundant6` | 16 | witness_exists | 2 | 262144 | none | none | none | z3=t0 cvc5=t0 cvc4=t0 | extraction (z3:no_farkas_th_lemma; cvc5:unmatched_literal) then fallback (sparse_search_exhausted) |
| `B1_true_2p21` | 4 | witness_exists | 2 | 2097152 | none | none | none | z3=t0 cvc5=t0 cvc4=t0 | extraction (z3:no_farkas_th_lemma; cvc5:unmatched_literal) then fallback (search_exhausted) |
| `B2_false_2p22` | 4 | no_witness_exists | — | — | none | none | none | z3=FAILED cvc5=FAILED cvc4=FAILED | backend search (z3=sat,cvc5=sat,cvc4=sat) |
| `B3_false_wide_bound` | 4 | no_witness_exists | — | — | none | none | none | z3=FAILED cvc5=FAILED cvc4=FAILED | backend search (z3=sat,cvc5=sat,cvc4=sat) |
| `B4_true_exact` | 4 | witness_exists | 2 | 262144 | none | none | none | z3=t0 cvc5=t0 cvc4=t0 | extraction (z3:unmatched_literal; cvc5:no_la_generic) then fallback (search_exhausted) |

### 3.5 Costs, separated where observable

Solver / extraction / fallback-search / Lean-side numbers are from different instruments and are NOT summable: the first three are the stage tracer's own timings of one sequential replay, the last two are the bridge's per-call report and Lean's profiler inside the probe. `n/a` = not measured.

| case | z3 solve ms | z3 extract ms | fallback ms | `pbterm` dispatch ms | `pbterm` verify ms | `pbterm` tactic ms | `omega` tactic ms |
|---|---|---|---|---|---|---|---|
| `O5_site2_isolated` | 9 | 0 | 0 | n/a | n/a | 28.4 | 2.12 |
| `O6_E4` | 8 | 0 | 35 | 99 | 1 | 117.0 | 4.19 |
| `C1_coef_1` | 8 | 0 | 0 | 21 | 1 | 35.5 | 2.13 |
| `C2_coef_2` | 8 | 0 | 0 | 21 | 0 | 37.7 | 2.9 |
| `C3_coef_3` | 8 | 0 | 0 | 21 | 1 | 33.1 | 2.12 |
| `C4_coef_4` | 8 | 0 | 0 | n/a | n/a | 27.6 | 1.81 |
| `C5_coef_5` | 7 | 0 | 0 | n/a | n/a | 30.7 | 1.9 |
| `C6_coef_8` | 8 | 0 | 0 | n/a | n/a | 28.3 | 1.91 |
| `C7_coef_2p10` | 7 | 0 | 0 | n/a | n/a | 27.6 | 2.05 |
| `C8_coef_2p18` | 10 | 0 | 0 | n/a | n/a | 31.2 | 1.82 |
| `P1_decimal_coef` | 8 | 0 | 0 | n/a | n/a | 29.7 | 2.09 |
| `P2_operand_order` | 7 | 0 | 0 | n/a | n/a | 27.5 | 2.01 |
| `P3_le_pred` | n/a | n/a | n/a | n/a | n/a | 0.216 | 2.33 |
| `P4_prime_literal` | 7 | 0 | 0 | n/a | n/a | 30.9 | 1.76 |
| `P5_plain_nat` | 9 | 0 | 0 | n/a | n/a | 27.1 | 2.06 |
| `P6_hyp_le` | 8 | n/a | 0 | n/a | n/a | 40.1 | 1.59 |
| `R1_reorder` | 8 | 0 | 0 | n/a | n/a | 17.7 | 1.96 |
| `R2_redundant3` | 10 | 0 | 1607 | n/a | n/a | 6000.0 | 2.85 |
| `R3_site2_in_context` | 8 | 0 | 60 | n/a | n/a | 227.0 | 3.19 |
| `R4_redundant6` | 10 | 0 | 90 | n/a | n/a | 350.0 | 2.41 |
| `B1_true_2p21` | 8 | 0 | 0 | n/a | n/a | 27.7 | 2.23 |
| `B2_false_2p22` | 7 | n/a | 0 | n/a | n/a | 29.8 | 0.677 |
| `B3_false_wide_bound` | 7 | n/a | 0 | n/a | n/a | 26.7 | 0.788 |
| `B4_true_exact` | 8 | 0 | 0 | n/a | n/a | 28.5 | 1.79 |

`R2_redundant3` is the cost of a *failed* recovery: 10 compiled inputs put the
dense coefficient space at 4^10 ≈ 1.05 M, inside the module's 2 M budget, so the
fallback sweeps all of it — 1.6 s in the tracer, and 6.0 s of tactic time in
Lean — and then fails anyway. Adding three true, unused hypotheses to a goal the
broker could not certify makes the failure two orders of magnitude more
expensive.

## 4. Diagnosis

The certificate is lost in **extraction**, not in solving, and the bounded
fallback that exists to cover extraction failures is then out of reach because
of the multiplier's size. Three gaps compose; each is separately visible in the
preserved artifacts.

### G1 — z3's Farkas clause is mixed-polarity, and the clause parser is not

For the isolated site 2, z3 does return `unsat` and does emit a Farkas-tagged
theory lemma (`raw/<stamp>/O5_site2_isolated.z3.proof`):

    (unit-resolution ((_ th-lemma arith farkas 1 1) (or $x66 (not $x130)))
                     @x179 (mp @x140 …) false)

with `$x66 = (>= _pb_atom_0 4398046511104)` and
`$x130 = (>= _pb_atom_0 70368744161281)`. The stage tracer nonetheless reports
`no_farkas_th_lemma`, i.e. `Z3_proof.find_farkas` found nothing.

Reading the code against that proof: `Z3_proof.parse_farkas_clause_application`
(`sdk/lib/z3_proof.ml`) requires **every** disjunct of the clause to be a
`(not L)` form — it maps `strip_not` over the disjuncts and refuses on a length
mismatch. The clause a Farkas lemma introduces is the negation of the
conjunction of the participating literals, so a participating literal that is
itself a negated atom (here `¬(x ≥ 2^42)`, the range check) appears in the
clause as the **bare** atom `$x66`. One bare disjunct is enough to make the
whole application unrecognized. `parse_farkas_direct_application` then does not
match either (the application's last argument is the clause, not `false`), so
`find_farkas` returns `None`.

This gap is coefficient-independent: across the whole `C1..C8` sweep — the same
statement with multipliers 1, 2, 3, 4, 5, 8, 2^10, 2^18 — z3's native
extraction reports `no_farkas_th_lemma` at *every* multiplier, including 1.

### G2 — the solver has already tightened the goal, so the literal is not the IR's

z3's rewrite step turns `¬(c·x < P)` into `x ≥ ⌈P/c⌉` before the arithmetic
conflict. The sweep shows this exactly:

| multiplier `c` | z3's rewritten literal | `⌈P/c⌉` | th-lemma coefficients |
|---|---|---|---|
| 1 | `x ≥ 18446744069414584321` | 18446744069414584321 | `1 1` |
| 3 | `x ≥ 6148914689804861441` | 6148914689804861441 | `1 1` |
| 4 | `x ≥ 4611686017353646081` | 4611686017353646081 | `1 1` |
| 2^10 | `x ≥ 18014398505287681` | 18014398505287681 | `1 1` |
| 2^18 | `x ≥ 70368744161281` | 70368744161281 | `1 1` |

The multiplier has been divided out of the conflict; the Farkas coefficients
are `1 1` regardless of its size. Because `c ∤ P`, the ceiling changes the
constant, so the tightened literal is **not a positive rescaling** of the IR's
own negated goal `c·x ≥ P` — and both extractors match literals to IR inputs
exactly by positive rescaling (`Alethe_farkas.match_shape`, extended in
`Z3_farkas`).

That is not a code reading only: it is what cvc5 reports on the same
obligation. cvc5's Alethe proof does contain the `la_generic` step, and the
tracer's failure is `unmatched_literal`, naming the literal and its compiled
form:

    no IR input matches clause literal
      (not (<= (* -1 _pb_atom_0) (* -1 70368744161281)))
      (compiled Le(-_pb_atom_0 + 70368744161281))

and 262144 × that constant is 18446744069414846464, not P. z3 exhibits the same
`unmatched_literal` failure directly on `B4_true_exact`, where its clause
happens to parse. So G2 is observed on this obligation, on two backends,
independently of G1.

### G3 — with extraction gone, everything rests on a magnitude-bounded search

`Farkas_search.try_close` is the designed rescue for "the solver closed it by
rewrites we cannot follow". It enumerates integer coefficients in `{0..bound}`
with `bound = 3` (`sdk/lib/farkas_search.ml`). The witness this obligation needs
over the IR's own hypotheses is

    262144 · hhi  +  1 · neg_goal

— the existence probe finds it and the SDK's own `Farkas.verify` accepts it, so
the certificate exists over exactly the dispatched IR. 262144 is 5 orders of
magnitude above the bound. The `C1..C8` sweep is the clean cut: multipliers
1, 2, 3 are recovered by the fallback and reconstruct in term mode; 4 and every
larger multiplier are lost, and the loss is total (tier 0 from all three
backends).

### Why the isolated case fails and the related ones do not

**This is the observed pattern across the corpus, not a verified claim about
the solvers' internals.** It holds on all 20 single-variable cases and both
multi-variable ones here, and the tightened constants match `⌈P/c⌉` exactly at
every multiplier; but nothing in this campaign inspects why z3 chooses one
th-lemma shape over the other, and §9.1 names the experiment that would settle
it. Read what follows as the regularity the evidence shows.

G2's tightening is only available when the arithmetic conflict collapses to a
single variable. That is what separates the cases:

* **one reified variable in the goal** (`O5`, the whole `C`/`P`/`R`/`B1`/`B4`
  families, and in-context `O2`): the solver divides the multiplier out, the
  Farkas step is over literals the IR does not contain, extraction fails on
  every backend, and only the bounded fallback is left — which succeeds exactly
  while the multiplier is ≤ 3.
* **two or more reified variables** (`O3`: `g_lo + 2^18·g_hi`; `O6`/E4:
  `g1l + 2^18·B` under a window): no single-variable tightening is available,
  z3 emits the **direct-from-premises** shape over the IR's own literals, and
  `Z3_farkas` extracts — carrying the 2^18 with it, as `1/262144` at site 3 and
  as `68719476736`/`262144` at E4.

So "coefficient size" and "surrounding context" are not independent knobs.
Context decides whether the solver tightens; tightening is what destroys
extraction; the coefficient's size then decides whether the bounded fallback can
still rescue it. Adding *hypotheses* alone does not help — `R2` (three extra
range facts), `R3` (the full in-context site-2 assumption set, which reifies to
a byte-identical IR to `O2`) and `R4` (six unrelated facts) all still fail.
What helped at site 3 was a second variable in the **goal**.

### Provenance: which certificates came from a backend's proof

The bridge's report line names a backend for every tier-1 cert, but it cannot
say whether the witness came out of that backend's proof or out of the SDK's own
search — and the two are not rare-vs-common here:

| in-context site | route | note |
|---|---|---|
| `O1` | **fallback** | witness `-3·hP + 1·neg_goal`; `hP` compiles to `0 = 0` after unfolding, so the certificate carries a vacuous term |
| `O2` | none | tier 0 |
| `O3` | **extracted** (z3) | `1/262144·hlo + 1/262144·neg_goal + 1·hhi` |
| `O4` | **fallback** (z3, cvc4); cvc5 also extracts | `1·hprodlt + 1·neg_goal` |

Of the three sites the completed case study reconstructs in term mode, exactly
one consumed a witness that a backend's own proof produced. A `backend=cvc4
tier=1 format=farkas` line is *always* an SDK-fallback witness — cvc4 has no
proof-trace path at all (`sdk/lib/adapter_cvc4.ml`) — and `backend=z3 tier=1`
can be either.

## 5. The smallest repair that the evidence supports

**Justified, and it is not "raise the bound".** Raising `Farkas_search`'s
coefficient bound to reach 262144 is refuted by measurement, not by taste. The
module's own budget is `max_candidates = 2_000_000` (a measured ~1.3 s
worst case). At `bound = 262144`:

| case | inputs | dense space | sparse (support ≤ 4) space |
|---|---|---|---|
| `O5` isolated site 2 | 4 | 4.7 × 10²¹ | 4.7 × 10²¹ |
| `O2`/`R3` in context | 13 | 2.8 × 10⁷⁰ | 3.4 × 10²⁴ |
| `O4` | 21 | 6.2 × 10¹¹³ | 2.8 × 10²⁵ |

Every one of those is 15 to 107 orders of magnitude over the budget, dense and
sparse alike. There is no bound that reaches this family.

### Proposed change — CORRECTED after review

The first version of this proposal said "keep the support bound, drop the
magnitude bound", meaning: replace the enumerating search with a support-≤4
exact solve. **That would have lost certificates the SDK finds today**, and the
review produced the counterexample:

    x₀ ≤ x₁ ≤ x₂ ≤ x₃ ≤ 0  ⊢  x₀ ≤ 0

Its witness is coefficient 1 on each of `h1`..`h4` *and* `neg_goal` — support
5. Variable cancellation forces all five equal, so no smaller-support witness
exists. The **dense** enumeration has no support limit at all
(`sdk/lib/farkas_search.ml`, the `size <= max_candidates` branch); `max_support
= 4` governs only the *sparse rescue* that runs when the dense space is over
budget. Five inputs at `bound = 3` is 4⁵ = 1024 candidates, well inside the
budget, so the dense path finds this today and cvc4 mints tier 1 on it —
reproduced here, and now frozen into the corpus as `V1_chain_support5` (with
`V2_chain_support7` to pin coverage further above the bound).

So the change is **strictly additive**: the enumerating search runs first and
unchanged, and exact recovery runs *only* on the paths where it returned an
error. No witness the current code produces can change, by construction.

In `sdk/lib/farkas_search.ml` only: for each candidate support set of the
compiled inputs (size ≤ `max_exact_support`), do not guess the multipliers —
solve for them, in exact rational arithmetic. Clear denominators, emit the
integer witness, and hand it to the existing `Farkas.verify`, which stays the
gate and is not modified. `sdk/lib/adapter_{z3,cvc4,cvc5}.ml` change only in
calling `try_close_then_exact` where they called `try_close`.

Why this is the smallest thing that works:

* it is **backend-agnostic** — G1 and G2 are different failures in different
  extractors (z3 clause polarity, cvc5 literal matching), and cvc4 has no proof
  path to fix at all, so a fix per extractor is three fixes and still leaves
  cvc4;
* fixing G2 properly means accepting a solver literal that is *implied by* an
  IR input rather than a rescaling of it — which the Lean side would then also
  have to justify at reconstruction time. That is a much larger change;
* it costs no new trust: the witness is still checked by `Farkas.verify` and, in
  term mode, rebuilt into a kernel-checked term;
* it is bounded, and the bound is a named refusal rather than a silent
  truncation.

### Validation gate for that repair (the eventual gate, not this checkpoint)

1. All four original carry obligations reconstruct in term mode
   (`CarryLiftPBTerm` 4/4, in file, in context).
2. The held-out variants (`heldout/`, untouched by this checkpoint) behave as
   predicted: `H1`–`H4`, `H6` reconstruct; `H5` is refused with `sat`.
3. False goals still rejected: `B2`, `B3`, `H5` — the adapters return
   `sat_returned` and mint no cert.
4. Corrupted certificates: `diag/negcheck.ml`'s battery still shows the
   shipped verifier agreeing with the independently computed expectation on
   every mutation, in both directions, and both envelope mutations still
   rejected as `hash_mismatch` — and the runner still fails the build when
   they do not (fault-injection self-test in
   `logs/negcheck_gate_selftest.txt`).
5. Costs bounded and measured: the new stage has its own named budget and
   refusal, with the cost per unit of that budget measured rather than
   inherited; and the SDK's existing tests either still pass or are updated as
   a deliberate, reviewed change, called out as such.
6. Preserved coverage: `V1_chain_support5` and `V2_chain_support7` — witnesses
   whose support exceeds the sparse rescue's bound and which the dense search
   finds today — still mint tier 1.
7. Every reconstruction closes the ORIGINAL goal under the existing axiom
   policy (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no
   `native_decide`).

A repair that passes 1–6 is an improvement in checked certificate recovery. It
would not be evidence of any advantage over native Lean automation: `omega`
closes every true case in this corpus in about 2 ms of tactic time,
and the default `proof_broker` closes them too — through `gated_omega`, with the
certificate only gating.

## 6. Negative checks — CORRECTED after review

Run by `tools/run_negchecks.sh` (`diag/negcheck.ml`). Results in
`raw/<stamp>/*.negcheck.json`.

### What the first version got wrong

Two things, both found in review.

**The battery mutated a term that carried no proof content.** Its target
picker called an input "load-bearing" only if its compiled form contained a
**variable**. For a *ground* obligation — `O1` is `(2:ℕ)^18 < P`, which after
definition unfolding has no variables at all — that test classifies the
negated goal, i.e. the entire contradiction, as vacuous. Selection then fell
back to `hP`, whose compiled form is the identically-zero `Eq(0 = 0)`. So the
"five accepted mutations" had changed or deleted a coefficient on `0 = 0`,
leaving the real inequality untouched, and the report's explanation of them —
that a rescaled ground contradiction is still valid — described something the
battery had not done.

**The runner asserted nothing.** It recorded verdicts, and
`cmd && echo ok || echo FAIL` made every failure a successful `echo`; the
script exited 0 with a failing executable, and also with no `logs/STAMP` at
all. Both reproduced here before fixing.

### What it does now

* **Target selection** prefers an entry whose input has a variable; failing
  that, a **non-vacuous** entry (variable-free but with a *nonzero* constant —
  the ground contradiction); failing that, the largest. "Vacuous" now means
  the compiled form is identically zero. The class actually reached is
  reported, never assumed, and the report carries the compiled form of every
  witness entry.
* **The expectation is computed, not assumed.** `expected_verified` is a
  second, small implementation of the Farkas acceptance rule — nonneg
  coefficients on inequalities, the weighted sum a constant, that constant
  positive, or zero with a positively-weighted strict input under LRA. Every
  mutant is classified `invalid_mutation` (a correct verifier must reject) or
  `valid_transformation` (a correct verifier must accept) by that rule, and
  the gate asserts the shipped `Farkas.verify` **agrees** in both directions.
  A count of accepted mutations is not the criterion; agreement is.
* **The gate is enforced and self-tested.** `negcheck.exe` exits nonzero on
  any disagreement; the runner fails on a nonzero exit, a missing result file,
  a result whose own `gate.ok` is false, a case with an expectation but no
  captured IR, and a case declared unreifiable that unexpectedly has one.
  `NEGCHECK_BIN=tools/negcheck_fault_stub.sh tools/run_negchecks.sh` (a stub
  that exits 42) must — and does — exit nonzero;
  `logs/negcheck_gate_selftest.txt` records that, and the missing-`STAMP` case.

### Results

**False goals.** `B2_false_2p22` and `B3_false_wide_bound` get `sat_returned`
from all three adapters: no certificate is minted. Their falsity is established
in `tools/truth_check.py`, not by those failures.

**Corrupted certificates.** 7 cases had a genuine Tier 1 Farkas cert to
corrupt; 56 witness mutations; **56 of 56 agree with the oracle**. 55 were
classified `invalid_mutation` and all 55 were rejected, with the right named
reason — `not_contradictory` (residual printed), `negative_coefficient`,
`unknown_hypothesis`, `bad_coefficient`, `malformed_witness`. One was
classified `valid_transformation`: doubling the coefficient of `O1`'s ground
contradiction, which a correct verifier **must** accept, and does. Both
envelope mutations were rejected as `hash_mismatch` on the named field, in
every case. With the target corrected, `O1`'s other seven mutations — including
zeroing, negating and dropping the contradiction — are all rejected, matching
the review's independent run.

**An incidental defect the battery surfaced.** Four of the five
fallback-produced witnesses in this corpus (`O1`, `C1`, `C2`, `C3`) name `hP`
with a coefficient, and after the definition-unfolding pass `hP` compiles to
`0 = 0` — a term that contributes nothing. `O4`'s fallback witness does not,
and neither extracted witness (`O3`, `O6`) does. The certificates are sound
(`Farkas.verify` agrees) but carry a term nothing depends on, because
`Farkas_search.try_assignment` requires only that *some* coefficient be
nonzero, not that each one earn its place. Cosmetic, not a soundness issue.

## 7. Held out

`H1`..`H6` are defined in `tools/corpus.py` and generated into `heldout/` for
all seven closers. **No broker closer was run on any of them**, and no result
from them is used anywhere in §4 or §5.

What was run is `omega`, once per case, purely to establish that the held-out
set elaborates and that its truth values are what they claim
(`tools/run_heldout_wellformed.sh`, `logs/heldout_wellformed.txt`): `H1`–`H4`
and `H6` close, `H5` — false by construction — does not. `omega` sees no
certificate machinery, so nothing it reported can have steered the diagnosis.

They were chosen to separate the hypotheses a repair could confuse: the range
check in successor form (`H1`), a different (coefficient, bound) pair at the
same product size (`H2`), two large multipliers at once (`H3`), one multiplier
inside the enumeration bound and one far outside it (`H4`), a false goal at a
large multiplier (`H5`), and the same carry-stage shape at a different limb
width (`H6`).

## 8. Reproduction

```bash
cd experiments/c1-cert-recovery

tools/baseline.sh > baseline/artifacts-before.txt   # identity of everything loaded
python3 tools/truth_check.py                        # truth values, independent of any prover
tools/check_pbdiag_drift.sh                         # the copied front-end steps have not drifted

# from the repo root — diagnostic executables only; touches nothing in sdk/
(cd ../.. && dune build experiments/c1-cert-recovery/diag/diag.exe \
                        experiments/c1-cert-recovery/diag/negcheck.exe)

tools/probe.sh --olean tools/PbDiag.lean            # the IR-dump tactic
date +%Y%m%d-%H%M%S > logs/STAMP
python3 tools/gen.py runs/$(cat logs/STAMP)         # generate the corpus files
tools/probe.sh ir/CarryLiftDump.lean > logs/ir_carrylift_dump.log 2>&1   # O1..O4
tools/capture_ir.sh                                 # IR capture + stage trace, per case
tools/run_carrylift.sh                              # the fixed-helper comparison, 2 warm passes
python3 tools/run.py runs/$(cat logs/STAMP)         # 24 cases x 7 closers, sequential
tools/run_negchecks.sh                              # false goals + corrupted certificates
tools/run_heldout_wellformed.sh                     # omega only, well-formedness
python3 tools/summarize.py runs/$(cat logs/STAMP)   # the tables above
tools/baseline.sh > baseline/artifacts-after.txt
diff baseline/artifacts-before.txt baseline/artifacts-after.txt
```

Single-case reproduction of the failure, from a clean shell:

```bash
cd experiments/c1-cert-recovery
tools/probe.sh runs/<stamp>/lean/O5_site2_isolated.pbterm.lean   # EXIT=1, refused
../../_build/default/experiments/c1-cert-recovery/diag/diag.exe \
    ir/O5_site2_isolated.json /tmp O5                            # the stage trace
cat raw/<stamp>/O5_site2_isolated.z3.proof                       # z3's own proof
```

## 9. Remaining uncertainties

1. **Why z3 chooses the clause shape here and the direct shape at site 3 is
   observed, not explained.** The correlation with "the conflict collapses to
   one variable" holds across all 20 single-variable cases and both
   multi-variable ones in this corpus, but nothing here inspects z3's
   internals. *Discriminating experiment*: re-run the `C` sweep with
   `smt.arith.solver` at 1 and 6 as well as the adapter's forced 2, and add a
   two-variable goal whose multiplier **does** divide the constant (so
   tightening is available without a ceiling) — if the shape follows the
   tightening rather than the variable count, the mechanism is confirmed; if it
   follows the solver configuration, the adapter's `smt.arith.solver 2`
   preamble is itself part of the story.

2. **cvc5's failure is not uniformly `unmatched_literal`.** On `B4_true_exact`
   it is `no_la_generic` instead. Whether that is a third shape or the same
   tightening reaching a different rule is not settled here.

3. **The corpus is one obligation family.** Every case is a range-check bound
   over the Goldilocks prime. The support-≤-4 claim behind the proposed repair
   is established *on this corpus* (every lost case has a verified witness of
   support 2 or 3); it is not established for obligations with disjunctions,
   case splits, or LRA denominators.

4. **The proposed repair's cost is bounded analytically, not measured.** The
   subset counts and per-solve sizes are arithmetic; no exact-solve
   implementation was timed, because none was written.

5. **The existence probe minimizes multiplier mass, not support.** A reported
   support of 2 is a witness that exists at support 2, not a proof that no
   smaller-support witness was missed elsewhere; for the repair's scope claim
   only existence at support ≤ 4 matters, and that is what is shown.

6. **Incidental, and outside the certificate path: a true goal reported as not
   provable.** `P6_hyp_le` states the range check as `g_hi.val ≤ 2^42 - 1`.
   The ℕ subtraction puts the hypothesis outside the reifiable fragment, so the
   reifier **drops it** (visible in `proof_broker?`'s `skipped` line, invisible
   to the plain tactic), the solvers correctly answer `sat` on what is left, and
   the tactic fails with "solver returned sat: home-system goal is not
   provable" on a statement that is true. The same subtraction in the *goal*
   (`P3_le_pred`) is a loud, named refusal. The asymmetry — loud in the goal,
   silent in a hypothesis — is worth a look on its own.

   Stated precisely, because the message invites the wrong reading: `sat` here
   is a fact about the **weakened IR**, in which the range check is absent. It
   establishes nothing about the original Lean goal, which is true and which
   `omega` closes. Tracked separately from certificate recovery — no repair in
   this line of work touches it — and surfaced by name by
   `tools/run_negchecks.sh`, which lists every true case on which all three
   adapters answered `sat` instead of letting it pass unremarked.
