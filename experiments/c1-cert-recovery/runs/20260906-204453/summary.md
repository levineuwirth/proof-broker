# Campaign pass `20260906-204453` — tables


## 1. Closure, by case and closer

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

## 2. What the broker closers actually did

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

## 3. Certificate recovery, per case (stage tracer)

`need` is the largest multiplier in the smallest witness the existence probe found over the dispatched IR, re-checked by the SDK's own `Farkas.verify`. `route` is where a tier-1 witness came from: **extracted** from the backend's own proof, or **fallback** from `Farkas_search`.

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

## 4. Costs, separated where observable

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
| `P6_hyp_le` | 8 | None | 0 | n/a | n/a | 40.1 | 1.59 |
| `R1_reorder` | 8 | 0 | 0 | n/a | n/a | 17.7 | 1.96 |
| `R2_redundant3` | 10 | 0 | 1607 | n/a | n/a | 6000.0 | 2.85 |
| `R3_site2_in_context` | 8 | 0 | 60 | n/a | n/a | 227.0 | 3.19 |
| `R4_redundant6` | 10 | 0 | 90 | n/a | n/a | 350.0 | 2.41 |
| `B1_true_2p21` | 8 | 0 | 0 | n/a | n/a | 27.7 | 2.23 |
| `B2_false_2p22` | 7 | None | 0 | n/a | n/a | 29.8 | 0.677 |
| `B3_false_wide_bound` | 7 | None | 0 | n/a | n/a | 26.7 | 0.788 |
| `B4_true_exact` | 8 | 0 | 0 | n/a | n/a | 28.5 | 1.79 |
