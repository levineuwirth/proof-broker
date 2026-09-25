# R6-014 block 2 runner, revision 4

This responds to [R6-014-BLOCK2-RUNNER-V3-REVIEW.md](R6-014-BLOCK2-RUNNER-V3-REVIEW.md), which reviewed revision 3 (`ba300752`) and found
two P2 receipt-agreement gaps. Nothing has been authorized, activated or sent. The frozen collection, analysis and evaluation sources are
unchanged.

**Runner versions:**

| revision | commit | status |
|---|---|---|
| 1 | `c1b9c91c` | defective |
| 2 | `9e0e9d0c` | reviewed |
| 3 | `ba300752` | reviewed |
| 4 | this change | pending review |

## The gate, revision 4 ([`run_block2.py`](run_block2.py))

Both findings belong to one class: a receipt in the chain that mirrors a retained record, but was never compared with it. So revision 4
closes the class rather than the two instances. A new step, `receipts_agree`, requires each such receipt exactly once and equal to its
record, or to the record's digest:
- `transport_validated` equals `transport-validation.json`. This was the review's first probe.
- `https_observed` equals the digests of `http.json`, `server.json` and `pricing-check.json`.
- `credential_use_checked` equals `credential-receipt.json`.
- `request_reserved` equals `reservation.json`, and `reservation_reconciled` binds the run's `ledger-after.ndjson`.
- `pricing_admitted` binds `host-pricing-admission.json`, and `payload_validated` equals `live-payload.json`.
- `prepared_problem` binds `prepared.json`, `input-ir.json` and `payload-audit.json`.
- `episode_started` binds the search policy.
- `live_transport_authorized` names this permit's reservation and slot, and the recorded commitment nonce.
- Every `stage_finished` equals its stage's process record.
- `certificate_assembled` binds `validated-response.json` and the certificate record's hash. It is required exactly where a certificate
  record exists.

The terminal receipt must have the frozen live shape from `cohort_episode.finalize`:
- exactly its ten keys;
- `accepted: false`;
- `publication_pending: true` and `publication_accepted: null`. This closes the review's second probe;
- its shared fields equal to the summary's;
- a finished terminal exactly when a proof is accepted with complete evidence.

Pending operator publication stays normal. The seal must also retain every record these receipts mirror.

All eleven audited block 1 runs still continue, with no reasons.

## Controls

**[R6-014-BLOCK2-RUNNER-V4-CONTROLS.json](R6-014-BLOCK2-RUNNER-V4-CONTROLS.json).** 46 cases, each fresh and on restart: 92 records, all as
expected.
- After any record change, the fixture builder refreshes the receipts that mirror it, as the driver writes them. It also derives the
  terminal's fields and event from the summary, as `finalize` does. Each case therefore still changes one relationship.
- There are 13 new receipt-only cases, each pausing for exactly its own reason:
  - the review's two probes;
  - a missing and a duplicated transport receipt;
  - the terminal's publication-pending and acceptance fields, and a finished event on a refusal;
  - the HTTPS, credential, reservation, stage, transport-authorization and assembly receipts.
- The positive cases carry the frozen live terminal, with publication pending.

**The reviewers' reproducers, recorded against revision 4:**
- **Revision 3 review's probes** ([R6-014-BLOCK2-RUNNER-V4-REVIEWER-V3-PROBES.json](R6-014-BLOCK2-RUNNER-V4-REVIEWER-V3-PROBES.json),
  [`block2_reviewer_v3_probes_recorded.py`](block2_reviewer_v3_probes_recorded.py)): both pause in both modes.
- **Revision 2 review's probes** ([R6-014-BLOCK2-RUNNER-V4-REVIEWER-V2-PROBES.json](R6-014-BLOCK2-RUNNER-V4-REVIEWER-V2-PROBES.json)):
  - the two l170 acceptances stop collection;
  - the other probes pause;
  - the genuine-ledger foreign reconciliation pauses;
  - the eleven genuine-ledger baselines continue.

Capture 4 has expired. After approval, `authorize` needs a fresh admitted capture and an addendum to the block 2 approval record.
