# R6-014 block 2 runner, revision 5

This responds to [R6-014-BLOCK2-RUNNER-V4-REVIEW.md](R6-014-BLOCK2-RUNNER-V4-REVIEW.md), which reviewed revision 4 (`58f50110`). It found
one P2: stage receipts were compared only with the process records that survived. Nothing has been authorized, activated or sent. The frozen
collection, analysis and evaluation sources are unchanged.

## The gate, revision 5 ([`run_block2.py`](run_block2.py))

- **One to one.** For every stage that has either a finish receipt or a process record, there must be exactly one of each. Only then are
  their payloads compared. This closes both of the review's probes.
- **The whole chain.** The complete event chain, supervisor receipts and child reports in order, must equal the frozen sequence for the
  run's outcome:

  | outcome | frozen sequence |
  |---|---|
  | proof | `proof` |
  | closer refusal | `reconstruction_refused` |
  | rejected witness | `witness_rejected` |
  | invalid response | `response_invalid` |

  The sequences come from the auditor frozen under `live-evaluation-v2`, and the runner checks that auditor's digest against the lock
  before using it. They reproduce all eleven block 1 chains exactly.
- **Stages.** The stages whose finish receipts the sequence names must be exactly the run's stage directories and process records.

This closes the class, not just the two instances: a missing, extra, duplicated or reordered receipt of any kind now pauses. All eleven
audited block 1 runs still continue, with no reasons.

## Controls

**[R6-014-BLOCK2-RUNNER-V5-CONTROLS.json](R6-014-BLOCK2-RUNNER-V5-CONTROLS.json).** 50 cases, each fresh and on restart: 100 records, all as
expected.
- The review's two probes pause, fresh and on restart:
  - the export's process record deleted, with the run resealed;
  - a stage-finish receipt with no process record.
- Two further cases also pause: a stage directory with no receipts, and two receipts swapped with their receipt times kept.
- The invalid-response fixture follows the frozen `response_invalid` sequence.

**The reviewers' reproducers, recorded against revision 5:**
- **Revision 4 review's**
  ([R6-014-BLOCK2-RUNNER-V5-REVIEWER-V4-PROBES.json](R6-014-BLOCK2-RUNNER-V5-REVIEWER-V4-PROBES.json),
  [`block2_reviewer_v4_probes_recorded.py`](block2_reviewer_v4_probes_recorded.py)): both pause in both modes.
- **Revision 3 review's** ([…-V3-PROBES.json](R6-014-BLOCK2-RUNNER-V5-REVIEWER-V3-PROBES.json)): both pause.
- **Revision 2 review's** ([…-V2-PROBES.json](R6-014-BLOCK2-RUNNER-V5-REVIEWER-V2-PROBES.json)):
  - the l170 acceptances stop collection;
  - the other probes pause, including the genuine-ledger foreign reconciliation;
  - the eleven genuine-ledger baselines continue.

Capture 4 has expired. After approval, `authorize` needs a fresh admitted capture and an addendum to the block 2 approval record.
