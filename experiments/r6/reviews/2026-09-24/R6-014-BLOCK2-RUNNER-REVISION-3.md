# R6-014 block 2 runner, revision 3

This responds to [R6-014-BLOCK2-RUNNER-V2-REVIEW.md](R6-014-BLOCK2-RUNNER-V2-REVIEW.md), which found one P1 and two P2 gaps. Nothing has been
authorized, activated or sent. The frozen collection, analysis and evaluation sources are unchanged.

**Runner versions:**

| revision | commit | status |
|---|---|---|
| 1 | `c1b9c91c` | defective; reviewed in [R6-014-BLOCK2-REVIEW.md](R6-014-BLOCK2-REVIEW.md) |
| 2 | `9e0e9d0c` | reviewed in the revision 2 review |
| 3 | this change | pending review |

Correction: the revision 2 note says "the reviewed version is at `c1b9c91c`". That meant the version the first review examined, which is the
defective revision 1. It was not an approved version.

## The gate, revision 3 ([`run_block2.py`](run_block2.py))

1. **Raw acceptance first (P1).** Before any classification, the gate reads every acceptance signal:
   - the verifier receipt in the chain and the certificate record;
   - any consumer stage or child observation, and the refusal record;
   - the kernel receipts, the proof receipt and the verdict record;
   - the summary's and the terminal's `proof_accepted`, and a finished terminal.

   On l170, any one of them is an integrity stop, whatever another record says.
2. **Agreement.** Receipts must agree with the records:
   - the verifier receipt equals the certificate record, and each is present only with the other;
   - a proof needs:
     - its consumption receipt (`certificate_consumed`);
     - both kernel receipts, equal to the verdict's replays;
     - a proof receipt binding the verdict's digest;
     - a finished terminal;
   - a refusal needs its refusal receipt equal to the record, a closer selection, and no consumption or kernel receipt;
   - a rejection or an invalid response reaches no consumer at all.

   The terminal receipt must bind the summary and both publication records by digest, and agree with the summary. Any disagreement pauses.
3. **Seal coverage (P2).** The seal must retain every record the gate reads (and every outcome record present) and list every file in the
   run. Every retained digest and the chain must hold. An empty inventory pauses.
4. **Slot identity (P2).** All of these must be this slot's:
   - the event chain's run and task;
   - the search policy;
   - the permit and reconciliation (task, draw, episode and one reservation);
   - the run's own ledger snapshots, which must end at them;
   - the chain's ledger receipts, which must bind their row hashes.

   The live ledger must hold the permit and the reconciliation once each, in that order. Agreement with some consumed row is no longer
   enough.

## Controls

**[R6-014-BLOCK2-RUNNER-V3-CONTROLS.json](R6-014-BLOCK2-RUNNER-V3-CONTROLS.json)** ([`block2_runner_controls.py`](block2_runner_controls.py)).
It runs 33 cases, each twice (fresh and restart), 66 records, all as expected.
- Every positive fixture is consistent at every identity:
  - the permit and reconciliation rows are rewritten to the draw-2 slot and episode;
  - the ledger chain is re-hashed;
  - the run's snapshots are regenerated;
  - the chain's ledger receipts are repointed;
  - the run identity is renamed;
  - the terminal digests are refreshed;
  - the run is resealed.
- Each case then changes one relationship.
- Positive cases continue with no reasons: a proof, a closer refusal, a rejected l170 witness and an invalid response.
- The eleven audited block 1 runs, read-only, all continue.

**[R6-014-BLOCK2-RUNNER-V3-REVIEWER-PROBES.json](R6-014-BLOCK2-RUNNER-V3-REVIEWER-PROBES.json).** This is the review's own reproducer, run
against revision 3 by [`block2_reviewer_probes_recorded.py`](block2_reviewer_probes_recorded.py). The wrapper records each decision instead
of asserting continuation. In both modes:
- l170's raw verifier acceptance and its summary's proof claim are integrity stops;
- a proof's rejecting verifier receipt, the missing consumption receipt, the foreign ledger task and the empty seal inventory pause;
- the genuine-ledger foreign-reconciliation probe pauses;
- the eleven baselines against the genuine 23-row ledger continue.

Capture 4 expired at 2026-09-25 08:49 UTC. After review, `authorize` needs a fresh admitted capture and an addendum to the block 2 approval
record, which names capture 4.
