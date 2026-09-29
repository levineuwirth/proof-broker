# The frozen corpus

Generated from `tools/corpus.py`; the truth column is recomputed independently by `tools/truth_check.py` and confirmed by `omega` on every case.

`relation` — **same**: meaning-preserving with respect to the obligation it is derived from (same mathematical content, different presentation, or a larger but consistent assumption set). **changed**: a different obligation (the constant, the bound, or the truth value moved).

## In-context originals (captured inside the real proof)

| id | obligation | in scope |
|---|---|---|
| `O1` | `(2:ℕ)^18 < P` | `hq hS hlo hhi hP` + 4 atom-nonnegativity facts (9 IR hypotheses) |
| `O2` | `2^18 * g_hi.val < P` | the above + `h2L hpow` (12) |
| `O3` | `g_lo.val + 2^18 * g_hi.val < P` | the above + `hside1 hmul` (15) |
| `O4` | `q.val * S.val < P` | the above + `hside2 hsum hprodlt` (20) |

Captured by `ir/CarryLiftDump.lean`, which is `corpus/carrylift/CarryLiftPBTerm.lean` with each `-- SITE n` closer replaced by `pb_dump_ir` + `omega`.

## Standalone cases

| id | group | truth | relation | obligation | hypotheses | note |
|---|---|---|---|---|---|---|
| `O5_site2_isolated` | original | TRUE | — | `2^18 * g_hi.val < P` | `(g_hi : ZMod P) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321)` | SITE 2 of carry_stage_lift_production, isolated. The refusal the case study recorded. |
| `O6_E4` | original | TRUE | — | `g1l + 2^18 * B < P` | `(g1l B G2w : ℕ) (hg1l : g1l < 2^18) (hBG : B < 2^G2w) (hG2w : 2^(36 + G2w) ≤ 2^62) (hsplit : 2^(36 + G2w) = 2^36 * 2^G2w) (hP : P = 18446744069414584321)` | The related 2^18-multiplier bound that DOES reconstruct, in a richer context. |
| `C1_coef_1` | coefficient | TRUE | changed | `1 * g_hi.val < P` | `(g_hi : ZMod P) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321)` | multiplier 1 |
| `C2_coef_2` | coefficient | TRUE | changed | `2 * g_hi.val < P` | `(g_hi : ZMod P) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321)` | multiplier 2 |
| `C3_coef_3` | coefficient | TRUE | changed | `3 * g_hi.val < P` | `(g_hi : ZMod P) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321)` | multiplier 3 |
| `C4_coef_4` | coefficient | TRUE | changed | `4 * g_hi.val < P` | `(g_hi : ZMod P) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321)` | multiplier 4 |
| `C5_coef_5` | coefficient | TRUE | changed | `5 * g_hi.val < P` | `(g_hi : ZMod P) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321)` | multiplier 5 |
| `C6_coef_8` | coefficient | TRUE | changed | `8 * g_hi.val < P` | `(g_hi : ZMod P) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321)` | multiplier 8 |
| `C7_coef_2p10` | coefficient | TRUE | changed | `2^10 * g_hi.val < P` | `(g_hi : ZMod P) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321)` | multiplier 1024 |
| `C8_coef_2p18` | coefficient | TRUE | changed | `2^18 * g_hi.val < P` | `(g_hi : ZMod P) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321)` | multiplier 262144 — identical statement to O5 (determinism check) |
| `P1_decimal_coef` | presentation | TRUE | same | `262144 * g_hi.val < P` | `(g_hi : ZMod P) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321)` | does the literal-vs-power spelling change the reified IR? |
| `P2_operand_order` | presentation | TRUE | same | `g_hi.val * 2^18 < P` | `(g_hi : ZMod P) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321)` | commutativity of the multiplication in the goal |
| `P3_le_pred` | presentation | TRUE | same | `2^18 * g_hi.val ≤ P - 1` | `(g_hi : ZMod P) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321)` | strict vs loose presentation of the same ℕ fact |
| `P4_prime_literal` | presentation | TRUE | same | `2^18 * g_hi.val < 18446744069414584321` | `(g_hi : ZMod P) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321)` | removes the definition-unfolding pass from the pipeline |
| `P5_plain_nat` | presentation | TRUE | same | `2^18 * v < P` | `(v : ℕ) (hv : v < 2^42) (hP : P = 18446744069414584321)` | free variable instead of an opaque nonlinear atom + its nonnegativity hypothesis |
| `P6_hyp_le` | presentation | TRUE | same | `2^18 * g_hi.val < P` | `(g_hi : ZMod P) (hhi : g_hi.val ≤ 2^42 - 1) (hP : P = 18446744069414584321)` | strict vs loose presentation of the same range check |
| `R1_reorder` | context | TRUE | same | `2^18 * g_hi.val < P` | `(g_hi : ZMod P) (hP : P = 18446744069414584321) (hhi : g_hi.val < 2^42)` | hypothesis order only |
| `R2_redundant3` | context | TRUE | same | `2^18 * g_hi.val < P` | `(q S g_lo g_hi : ZMod P) (hq : q.val ≤ 2^42) (hS : S.val < 2^18) (hlo : g_lo.val < 2^18) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321)` | redundant context, all of it true and none of it needed |
| `R3_site2_in_context` | context | TRUE | same | `2^18 * g_hi.val < P` | `(q S g_lo g_hi : ZMod P) (hq : q.val ≤ 2^42) (hS : S.val < 2^18) (hlo : g_lo.val < 2^18) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321) (h2L : (2:ℕ)^18 < P) (hpow : ((2:ZMod P)^18).val = 2^18)` | the four ZMod-equation hypotheses of the real proof are omitted: the reifier drops them (`proposition outside the reifiable fragment`), so this should reify to the SAME IR as in-context O2 — the run checks that by hash |
| `R4_redundant6` | context | TRUE | same | `2^18 * g_hi.val < P` | `(g_hi : ZMod P) (hhi : g_hi.val < 2^42) (a b c d e f : ℕ) (ha : a < 7) (hb : b < 11) (hc : c < 13) (hd : d < 17) (he : e < 19) (hf : f < 23) (hP : P = 18446744069414584321)` | widens the compiled-input count without touching the obligation |
| `B1_true_2p21` | boundary | TRUE | changed | `2^21 * g_hi.val < P` | `(g_hi : ZMod P) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321)` | last power-of-two multiplier that is still true at this bound |
| `B2_false_2p22` | boundary | FALSE | changed | `2^22 * g_hi.val < P` | `(g_hi : ZMod P) (hhi : g_hi.val < 2^42) (hP : P = 18446744069414584321)` | DELIBERATELY FALSE. A closer that 'succeeds' here is unsound; a closer that fails here has produced no counterexample to anything. |
| `B3_false_wide_bound` | boundary | FALSE | changed | `2^18 * g_hi.val < P` | `(g_hi : ZMod P) (hhi : g_hi.val < 2^46) (hP : P = 18446744069414584321)` | DELIBERATELY FALSE (2^18·(2^46−1) = 2^64 − 2^18 ≥ P) |
| `B4_true_exact` | boundary | TRUE | changed | `2^18 * g_hi.val < P` | `(g_hi : ZMod P) (hhi : g_hi.val ≤ 70368744161280) (hP : P = 18446744069414584321)` | tight: 2^18·70368744161280 = P − 1. The Farkas residual is 1. |

## Held out — DEFINED, NOT RUN at this checkpoint

No broker closer is run on any of these and no result from them enters this checkpoint's diagnosis. `omega` is run once, as a well-formedness and truth check only (`tools/run_heldout_wellformed.sh`).

| id | truth | relation | obligation | hypotheses | note |
|---|---|---|---|---|---|
| `H1_hyp_succ_form` | TRUE | same | `2^18 * g_hi.val < P` | `(g_hi : ZMod P) (hhi : g_hi.val + 1 ≤ 2^42) (hP : P = 18446744069414584321)` | the range check in successor form |
| `H2_coef_2p36` | TRUE | changed | `2^36 * v.val < P` | `(v : ZMod P) (hv : v.val < 2^24) (hP : P = 18446744069414584321)` | a different (coefficient, bound) pair with the same product size |
| `H3_two_large_coefs` | TRUE | changed | `2^18 * a.val + 2^36 * b.val < P` | `(a b : ZMod P) (ha : a.val < 2^18) (hb : b.val < 2^24) (hP : P = 18446744069414584321)` | two multipliers, both far above the enumeration bound |
| `H4_mixed_small_large` | TRUE | changed | `3 * a.val + 2^18 * b.val < P` | `(a b : ZMod P) (ha : a.val < 2^40) (hb : b.val < 2^40) (hP : P = 18446744069414584321)` | one multiplier inside the enumeration bound, one far outside |
| `H5_false_2p19` | FALSE | changed | `2^19 * v.val < P` | `(v : ZMod P) (hv : v.val < 2^45) (hP : P = 18446744069414584321)` | DELIBERATELY FALSE (2^19·(2^45−1) = 2^64 − 2^19 ≥ P) |
| `H6_other_limb_width` | TRUE | changed | `2^19 * g_hi.val < P` | `(g_hi : ZMod P) (hhi : g_hi.val < 2^41) (hP : P = 18446744069414584321)` | the same carry-stage shape at LIMB_W = 19 |
