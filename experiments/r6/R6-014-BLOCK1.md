# R6-014 block 1 — audited and analysed

Block 1 is the first block of the planned cohort: eleven posable sites × draw 1, under contract v2 and cohort v9. It was collected on
2026-09-24 and accepted by the amended frozen auditor, under [amendment 1](R6-014-AMENDMENT-1.md) and lock `live-evaluation-v2`
(`96ce9f6d…`).

The first frozen audit, under `live-evaluation-v1`, rejected the collection on the policy-directory layout before any per-run case. That
rejection is retained in [R6-014-BLOCK1-LIVE-AUDIT-REJECTED.json](reviews/2026-09-24/R6-014-BLOCK1-LIVE-AUDIT-REJECTED.json). The
evaluation is therefore a post-collection amendment, not an unchanged preregistered one.

Records:
- [live audit](reviews/2026-09-24/R6-014-BLOCK1-LIVE-AUDIT-AMENDMENT-1.json): 550 cases, accepted;
- [analysis input](reviews/2026-09-24/R6-014-BLOCK1-ANALYSIS-INPUT.json) and [frozen analysis v3](reviews/2026-09-24/R6-014-BLOCK1-ANALYSIS.json);
- [operator scan](reviews/2026-09-24/R6-014-BLOCK1-OPERATOR-SCAN.json): 101,646 files, no disclosures, all eleven runs bound.

## Collection

- **Slots:** 11 of 11 authorized slots were sent and returned a response.
  - no unknown sends, pre-send releases or exhausted slots;
  - not a partial collection, but the other 77 planned slots are neither evidence nor permission.
- **Money:**
  - reserved: 1,126,400 µUSD, which equals the authorization;
  - provider-reported usage: 13,560 input tokens, 5,478 output tokens and 0 cached;
  - priced at the frozen rates, that usage gives a ceiling of **116,070 µUSD**. That is an estimate, not a bill.
- **Continuation:** no integrity stop and no operational pause, so continuation is permitted under the frozen rules. Further blocks need
  separate authorization.

## Stages (over 11 slots sent with a response)

| returned | verified | consumed | local | whole | axioms clean |
|---|---|---|---|---|---|
| 11 | 10 true, 1 false | 6 true, 4 false, 1 unobserved | 6 | 6 | 6 |

The denominators are unchanged: 15 primary, 11 posed, 10 certificate-feasible, 1 negative control, 6 closer-reachable and 4
closer-unreachable.

- **Proofs (whole declaration validated, axioms unchanged):** l069, l070, l071 and l078 through `term_mode_nat`, and l096 and l099
  through `term_mode_int`. That is all six closer-reachable sites.
- **Verified but refused by reconstruction:** l166, l175, l178 and l204 (`nat_closer_int_goal`). These are the four predeclared
  closer-unreachable sites.
- **Negative control, l170:** the proposal was rejected by the verifier. There is **no false certificate acceptance** and no
  contradictory observation.
- **Witnesses:** every verified witness is one proposal per site.
  - l070 and l071: the verified witnesses differ from the classification's certificate, even after rescaling.
  - The other eight verified sites: equal to it.
- **Exposure sensitivities (whole validated):**
  - excluding l070: 5;
  - excluding the `lift_cell` family: 2.
- **By family:** `lift_cell` 4 of 4, `threshold_unique` 2 of 2, `cell_value_neutral` 0 (all refused or the negative control), and
  `Row.s1_noninc` 0 (refused).

## Beside the deterministic arm

The deterministic arm is tabled separately and never pooled. Its certificate-consuming route proved l069, l070, l071 and l078. It
never invoked its backend on l096 and l099, the two sites the learned arm also closed, through `term_mode_int`.

These are single-draw results on one block. They are not estimates over the planned eight draws.
