# R6-014 block 2 — the complete collection, audited and analysed

Block 2 is draws 2–8 of the eleven posable sites, 77 slots, under contract v2 and cohort v9. With block 1 it completes the planned cohort
of 88 slots. It was collected on 2026-09-28 and 2026-09-29. The whole collection of 89 runs was accepted by the amended frozen auditor,
under [amendment 2](R6-014-AMENDMENT-2.md) and lock `live-evaluation-v3` (`dac9f307…`). That lock verified before the audit.

The evaluation is a post-collection amendment, not an unchanged preregistered one. Amendment 1 changed the policy-directory check.
Amendment 2 admits live pre-send releases and retried slots; it was prepared after block 2 paused and approved before collection resumed.

Records:
- [live audit](reviews/2026-09-29/R6-014-BLOCK2-LIVE-AUDIT-AMENDMENT-2.json): 4,327 cases, accepted;
- [analysis input](reviews/2026-09-29/R6-014-BLOCK2-ANALYSIS-INPUT.json) and [frozen analysis v3](reviews/2026-09-29/R6-014-BLOCK2-ANALYSIS.json),
  whose program digest `9feb2226…` matches the `analysis-v3` lock;
- [operator scan](reviews/2026-09-29/R6-014-BLOCK2-OPERATOR-SCAN.json): 132,450 files, no disclosures, all 89 runs bound;
- run logs: [first launch](reviews/2026-09-28/R6-014-BLOCK2-INCIDENT-1.md) (incident 1, nothing reserved),
  [run 2](reviews/2026-09-28/R6-014-BLOCK2-RUN-2.log) (paused, [pause 1](reviews/2026-09-28/R6-014-BLOCK2-PAUSE-1.md)),
  [run 3](reviews/2026-09-29/R6-014-BLOCK2-RUN-3.log).

## Collection

| run | runner | what happened |
|---|---|---|
| 1 (2026-09-28 20:30Z) | revision 5 | interrupted before any reservation; moved out byte-for-byte ([incident 1](reviews/2026-09-28/R6-014-BLOCK2-INCIDENT-1.md)) |
| 2 (23:00Z) | revision 5 | 53 slots; paused at l204 draw 6, a pre-send connection failure the ledger released |
| 3 (2026-09-29 15:25Z) | revision 7 | preflight over the 54 existing runs, then l204 draw 6 retried as `attempt2` and the remaining 23 slots, without a pause |

- **Slots:** 88 of 88 authorized slots were sent and returned a response.
  - one pre-send release (l204 draw 6, attempt 1), retried once; its slot is `sent_with_response` with one pre-send attempt;
  - no unknown sends and no exhausted slots; not partial.
- **Money:**
  - committed, net: 9,011,200 µUSD, which equals the authorization. The 89 reservation rows total 9,113,600 µUSD gross; the one
    release returned 102,400 µUSD, and nothing is open;
  - provider-reported usage: 108,480 input tokens, 44,886 output tokens and 0 cached;
  - priced at the frozen rates, that usage gives a ceiling of **944,490 µUSD**. That is an estimate, not a bill.
- **Continuation:** no integrity stop and no operational pause. The authorization is spent in full; nothing further is authorized.

## Stages (over 88 slots sent with a response)

| returned | verified | consumed | local | whole | axioms clean |
|---|---|---|---|---|---|
| 88 | 80 true, 8 false | 48 true, 32 false, 8 unobserved | 48 | 48 | 48 |

The denominators are unchanged: 15 primary, 11 posed, 10 certificate-feasible, 1 negative control, 6 closer-reachable and 4
closer-unreachable.

| stratum | slots | verified | whole validated |
|---|---|---|---|
| closer-reachable (l069, l070, l071, l078, l096, l099) | 48 | 48 | 48 |
| closer-unreachable (l166, l175, l178, l204) | 32 | 32 | 0: all refused, `nat_closer_int_goal` |
| negative control (l170) | 8 | 0 | 0 |

- **Proofs:** every closer-reachable slot, at every draw. l069, l070, l071 and l078 closed through `term_mode_nat`; l096 and l099
  through `term_mode_int`.
- **Verified but refused by reconstruction:** every closer-unreachable slot, as predeclared.
- **Negative control, l170:** all eight proposals were rejected by the verifier. There is **no false certificate acceptance** and no
  contradictory observation.
- **Witnesses, compared up to positive scaling:**
  - l070: four distinct verified witnesses over its eight draws; three of the eight slots match the classification's certificate;
  - l071: two distinct witnesses; none of its eight slots matches it;
  - every other verified site: a single witness at every draw, equal to the classification's certificate.
- **Exposure sensitivities (whole validated):**
  - excluding l070: 40 of 80;
  - excluding the `lift_cell` family: 16 of 56.
- **By family:** `lift_cell` 32 of 32, `threshold_unique` 16 of 16, `cell_value_neutral` 0 of 32 (refused or the negative control),
  `Row.s1_noninc` 0 of 8 (refused).
- **Draw prefixes:** whole-validated grows by exactly six per draw, 6 at draw 1 through 48 at draw 8.

**Reading.** Eight draws changed witness diversity (l070, l071) but never expanded proof coverage: the 48 whole-validated slots are the
same six obligations at every draw, in two declaration families (`lift_cell`, `threshold_unique`). The learned arm's gain over the
deterministic arm remains l096 and l099, where that arm never reached its backend. The two post-collection amendments qualify the result.

## Beside the deterministic arm

The deterministic arm is tabled separately and never pooled. Its certificate-consuming route proved l069, l070, l071 and l078. It never
invoked its backend on l096 and l099, the two sites the learned arm closed through `term_mode_int`.
