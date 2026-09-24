# R6-014 block 2 runner, revision 2

This responds to [R6-014-BLOCK2-REVIEW.md](R6-014-BLOCK2-REVIEW.md). That review found two P1 defects and judged the runner not ready to
activate. Nothing has been authorized, activated or sent since. The frozen collection, analysis and evaluation sources are unchanged.

[`run_block2.py`](run_block2.py) now decides every slot with one continuation gate, `gate`. The reviewed version is at `c1b9c91c`.

**When the gate runs.** It runs after each fresh episode, and on restart for every existing run before that run could be skipped. It is
deterministic over the retained records, so a pause cannot be bypassed by restarting. There is no override: resolving a pause needs a
reviewed decision.

**What it reads.** The gate reads the run's own bound evidence:
- the seal and the event chain, and the terminal event;
- the slot identity;
- the live ledger's terminal row, compared with the run's reconciliation, and the slot's consumption, with nothing left open;
- the run's own synthetic-canary publication scan;
- the provider status and every transport binding;
- the outcome records and whether they agree with each other.

**Its decisions:**
- **continue:** a proof, a diagnosed closer refusal, a witness rejected by the checker, or an invalid response with all bindings intact;
- **integrity stop:** any verifier or consumer acceptance on l170, following the frozen rule;
- **pause:** everything else, failing closed. That includes missing or inconsistent evidence. Operator publication pending is normal and
  is not a failure.

The process exit code is not used.

**Controls.** [R6-014-BLOCK2-RUNNER-CONTROLS.json](R6-014-BLOCK2-RUNNER-CONTROLS.json) comes from
[`block2_runner_controls.py`](block2_runner_controls.py). It runs 18 cases, each twice with the same decision: once as a fresh episode and
once as an existing run on restart, 36 records in all.
- Each case is a copy of an audited block 1 run, retargeted to draw 2, changed in one relationship and resealed.
- The sender and the ledger are mocked, so nothing is launched or read.
- The review's three probes are all caught, in both modes: the sealed release on restart, the returned binding failure and the l170
  acceptance.

Read-only, the gate also returns "continue" on all eleven audited block 1 runs.
