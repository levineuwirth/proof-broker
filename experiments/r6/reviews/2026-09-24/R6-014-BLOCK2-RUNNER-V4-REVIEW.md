# Block 2 runner revision 4 — review

Reviewed `58f50110` on 2026-09-25. **Both revision 3 findings are repaired. One P2 stage-population gap remains; keep activation and transmission pending.**

I reran all 46 controls in fresh and restart modes: 92 records pass, with the same decisions, outcomes and launch counts as the supplied record. Source digests match. All eleven block 1 baselines continue with no reasons. I also reran both earlier reviewer-probe wrappers: the negative-control acceptances stop, the remaining corruptions pause, and the eleven genuine-ledger baselines still continue. The new terminal shape matches the live finalizer for continuable outcomes. The transport receipt is now unique and equal to its record.

**P2 — Stage comparison is driven only by surviving process files** (`run_block2.py:81–82`, `115–116`). Both seal requirements and receipt comparisons discover process records with a filesystem glob. Neither checks the reverse relationship: that each `stage_finished` receipt has its process record. As a result:

- Deleting the export process record while retaining its `stage_finished` receipt, then resealing, returns `continue / proof` with no reasons.
- Adding a validly chained `stage_finished` receipt for an additional stage with no process record also returns `continue / proof` with no reasons.

Both probes reach the next attempted launch in fresh and restart modes. The first uses the existing production seal routine after deleting the process file; there is no stale seal hash. The second preserves monotonic receipt times and recomputes the event chain and seal. Each changes one relationship.

Require a one-to-one correspondence between the stage-finish receipt population and process records, with the same stage names, no duplicate or unmatched entries, and exact payload equality. Derive required process-file coverage from that correspondence rather than only the files that happen to remain. Retain the changed-process-payload control and add missing-process-record and unmatched-receipt controls. This closes the missing direction of the new receipt-agreement check; it does not require changing the frozen scientific method or block 1 evidence.

Evidence:
- `R6-014-BLOCK2-RUNNER-V4-REVIEW-CONTROLS.json`: fresh 92-control record.
- `R6-014-BLOCK2-RUNNER-V4-REVIEW-V2-PROBES.json` and `R6-014-BLOCK2-RUNNER-V4-REVIEW-V3-PROBES.json`: fresh earlier-probe results.
- `R6-014-BLOCK2-RUNNER-V4-REVIEW-PROBES.json` and `block2_runner_v4_review_probes.py --output <fresh-path>`: the two new cases, each in both modes.

These tests use synthetic copies and mocked sender/ledger boundaries; the probe stops at the attempted next launch. No actual sender process, credential read or transmission occurred. Production remains revision 1 with eleven authorized slots, and the unchanged evaluation v2 lock verifies all 69 files at `96ce9f6d…`. The fresh-pricing-capture and approval-addendum steps remain pending runner approval.
