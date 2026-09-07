# Campaign pass `20260907-113052` — tables


## 1. Closure, by case and closer

`closed` = the closer closed the original goal and the file elaborated (probe EXIT=0). Everything else is that run's own named outcome; none of it is a counterexample.

| case | truth | omega | grind | pb | pbterm | pbterm_z3 | pbterm_cvc5 | pbterm_cvc4 |
|---|---|---|---|---|---|---|---|---|
| `O5_site2_isolated` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `O6_E4` | TRUE | closed | closed | closed | closed | closed | refused(tier0) | refused(tier0) |
| `V1_chain_support5` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `V2_chain_support7` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C1_coef_1` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C2_coef_2` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C3_coef_3` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C4_coef_4` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C5_coef_5` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C6_coef_8` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C7_coef_2p10` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C8_coef_2p18` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `P1_decimal_coef` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `P2_operand_order` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `P3_le_pred` | TRUE | closed | closed | refused(reify) | refused(reify) | refused(reify) | refused(reify) | refused(reify) |
| `P4_prime_literal` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `P5_plain_nat` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `P6_hyp_le` | TRUE | closed | closed | failed | refused(no cert) | refused(no cert) | refused(no cert) | refused(no cert) |
| `R1_reorder` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `R2_redundant3` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `R3_site2_in_context` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `R4_redundant6` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `B1_true_2p21` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `B2_false_2p22` | FALSE | failed | failed | failed | refused(no cert) | refused(no cert) | refused(no cert) | refused(no cert) |
| `B3_false_wide_bound` | FALSE | failed | failed | failed | refused(no cert) | refused(no cert) | refused(no cert) | refused(no cert) |
| `B4_true_exact` | TRUE | closed | closed | closed | closed | closed | closed | closed |

## 2. What the broker closers actually did

| case | `proof_broker` closer/backend/tier/format | `proof_broker_term` closer/backend/tier/format |
|---|---|---|
| `O5_site2_isolated` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `O6_E4` | gated_omega / z3 / t1 / farkas | term_mode_nat / z3 / t1 / farkas |
| `V1_chain_support5` | alethe_walker / cvc5 / t3 / alethe-2024 | term_mode_int / cvc4 / t1 / farkas |
| `V2_chain_support7` | alethe_walker / cvc5 / t3 / alethe-2024 | term_mode_int / cvc4 / t1 / farkas |
| `C1_coef_1` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `C2_coef_2` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `C3_coef_3` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `C4_coef_4` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `C5_coef_5` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `C6_coef_8` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `C7_coef_2p10` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `C8_coef_2p18` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `P1_decimal_coef` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `P2_operand_order` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `P3_le_pred` | (no report line) refused(reify) | (no report line) refused(reify) |
| `P4_prime_literal` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `P5_plain_nat` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `P6_hyp_le` | (no report line) failed | (no report line) refused(no cert) |
| `R1_reorder` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `R2_redundant3` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `R3_site2_in_context` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `R4_redundant6` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `B1_true_2p21` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |
| `B2_false_2p22` | (no report line) failed | (no report line) refused(no cert) |
| `B3_false_wide_bound` | (no report line) failed | (no report line) refused(no cert) |
| `B4_true_exact` | gated_omega / cvc4 / t1 / farkas | term_mode_nat / cvc4 / t1 / farkas |

## 3. Certificate recovery, per case (stage tracer)

`route`: **extracted** from the backend's own proof, **enumerated** by the bounded coefficient search, **exact** by exact support-bounded recovery, **none** if nothing produced one. It is not the same question as `minted tiers`: cvc5 may prefer its own tier-3 trace over a tier-1 witness it could also have produced, and the parallel driver then picks among the minted certs.

`need` is the largest multiplier in the smallest witness the existence probe found over the dispatched IR, re-checked by the SDK's own `Farkas.verify`. `route` is explained above.

| case | inputs | witness exists | support | need | z3 route | cvc5 route | cvc4 route | minted tiers | where lost |
|---|---|---|---|---|---|---|---|---|---|
| `O1` | 10 | witness_exists | 1 | 1 | enumerated | enumerated | enumerated | z3=t1 cvc5=t3 cvc4=t1 | —(recovered: z3 via enumerated) |
| `O2` | 13 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `O3` | 16 | witness_exists | 3 | 262144 | extracted | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via extracted) |
| `O4` | 21 | witness_exists | 2 | 1 | enumerated | extracted | enumerated | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via enumerated) |
| `O5_site2_isolated` | 4 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `O6_E4` | 11 | witness_exists | 6 | 68719214592 | extracted | none | none | z3=t1 cvc5=t0 cvc4=t0 | —(recovered: z3 via extracted) |
| `V1_chain_support5` | 5 | witness_exists | 5 | 1 | extracted | enumerated | enumerated | z3=t1 cvc5=t3 cvc4=t1 | —(recovered: z3 via extracted) |
| `V2_chain_support7` | 7 | witness_exists | 7 | 1 | extracted | enumerated | enumerated | z3=t1 cvc5=t3 cvc4=t1 | —(recovered: z3 via extracted) |
| `C1_coef_1` | 4 | witness_exists | 2 | 1 | enumerated | extracted | enumerated | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via enumerated) |
| `C2_coef_2` | 4 | witness_exists | 2 | 2 | enumerated | enumerated | enumerated | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via enumerated) |
| `C3_coef_3` | 4 | witness_exists | 2 | 3 | enumerated | enumerated | enumerated | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via enumerated) |
| `C4_coef_4` | 4 | witness_exists | 2 | 4 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `C5_coef_5` | 4 | witness_exists | 2 | 5 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `C6_coef_8` | 4 | witness_exists | 2 | 8 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `C7_coef_2p10` | 4 | witness_exists | 2 | 1024 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `C8_coef_2p18` | 4 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `P1_decimal_coef` | 4 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `P2_operand_order` | 4 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `P3_le_pred` | — | — | — | — | — | — | — | — | reification (no IR captured) |
| `P4_prime_literal` | 4 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `P5_plain_nat` | 4 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `P6_hyp_le` | 3 | no_witness_exists | — | — | none | none | none | z3=FAILED cvc5=FAILED cvc4=FAILED | backend search (z3=sat,cvc5=sat,cvc4=sat) |
| `R1_reorder` | 4 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `R2_redundant3` | 10 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `R3_site2_in_context` | 13 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `R4_redundant6` | 16 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `B1_true_2p21` | 4 | witness_exists | 2 | 2097152 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `B2_false_2p22` | 4 | no_witness_exists | — | — | none | none | none | z3=FAILED cvc5=FAILED cvc4=FAILED | backend search (z3=sat,cvc5=sat,cvc4=sat) |
| `B3_false_wide_bound` | 4 | no_witness_exists | — | — | none | none | none | z3=FAILED cvc5=FAILED cvc4=FAILED | backend search (z3=sat,cvc5=sat,cvc4=sat) |
| `B4_true_exact` | 4 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |

## 4. Costs, separated where observable

Solver / extraction / fallback-search / Lean-side numbers are from different instruments and are NOT summable: the first three are the stage tracer's own timings of one sequential replay, the last two are the bridge's per-call report and Lean's profiler inside the probe. `n/a` = not measured.

| case | z3 solve ms | z3 extract ms | enumerate ms | exact ms | `pbterm` dispatch ms | `pbterm` verify ms | `pbterm` tactic ms | `omega` tactic ms |
|---|---|---|---|---|---|---|---|---|
| `O5_site2_isolated` | 7 | 0 | 0 | 0 | 21 | 0 | 30.5 | 2.13 |
| `O6_E4` | 10 | 0 | 33 | 1 | 89 | 1 | 104.0 | 3.85 |
| `V1_chain_support5` | 8 | 0 | 0 | 0 | 22 | 1 | 26.9 | 2.05 |
| `V2_chain_support7` | 8 | 0 | 3 | 0 | 26 | 1 | 32.3 | 2.05 |
| `C1_coef_1` | 25 | 0 | 0 | 0 | 32 | 0 | 43.0 | 1.84 |
| `C2_coef_2` | 8 | 0 | 0 | 0 | 21 | 0 | 35.8 | 1.83 |
| `C3_coef_3` | 8 | 0 | 0 | 0 | 21 | 1 | 38.7 | 1.82 |
| `C4_coef_4` | 7 | 0 | 0 | 0 | 21 | 0 | 30.9 | 2.17 |
| `C5_coef_5` | 8 | 0 | 0 | 0 | 21 | 1 | 31.8 | 1.85 |
| `C6_coef_8` | 8 | 0 | 0 | 0 | 22 | 0 | 34.6 | 2.41 |
| `C7_coef_2p10` | 7 | 0 | 0 | 0 | 22 | 0 | 33.0 | 1.93 |
| `C8_coef_2p18` | 8 | 0 | 0 | 0 | 21 | 0 | 30.1 | 2.22 |
| `P1_decimal_coef` | 7 | 0 | 0 | 0 | 21 | 0 | 35.6 | 1.95 |
| `P2_operand_order` | 10 | 0 | 0 | 0 | 22 | 0 | 33.2 | 2.05 |
| `P3_le_pred` | n/a | n/a | n/a | n/a | n/a | n/a | 0.223 | 2.56 |
| `P4_prime_literal` | 8 | 0 | 0 | 0 | 21 | 0 | 34.4 | 1.75 |
| `P5_plain_nat` | 7 | 0 | 0 | 0 | 21 | 1 | 31.4 | 1.69 |
| `P6_hyp_le` | 9 | n/a | 0 | 0 | n/a | n/a | 27.4 | 1.59 |
| `R1_reorder` | 8 | 0 | 0 | 0 | 22 | 0 | 31.7 | 1.95 |
| `R2_redundant3` | 8 | 0 | 1643 | 0 | 5541 | 0 | 5550.0 | 3.89 |
| `R3_site2_in_context` | 7 | 0 | 57 | 0 | 216 | 0 | 227.0 | 3.59 |
| `R4_redundant6` | 13 | 0 | 95 | 0 | 325 | 1 | 338.0 | 2.58 |
| `B1_true_2p21` | 8 | 0 | 0 | 0 | 21 | 1 | 32.9 | 1.84 |
| `B2_false_2p22` | 10 | n/a | 3 | 0 | n/a | n/a | 28.8 | 0.953 |
| `B3_false_wide_bound` | 8 | n/a | 0 | 0 | n/a | n/a | 28.3 | 0.684 |
| `B4_true_exact` | 8 | 0 | 0 | 0 | 21 | 1 | 31.4 | 1.58 |
