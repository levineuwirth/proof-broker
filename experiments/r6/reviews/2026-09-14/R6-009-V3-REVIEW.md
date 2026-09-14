# Review of R6-009 v3 at 7240ae5

Reviewed `7240ae5a14aaf780f40cd26c31f0850f0ce0ec82` on 2026-09-14. The three v2 findings are closed, and the reported demonstration is internally consistent. Two further P2 gaps remain in the non-locked auditor. Both can be repaired with copied-artifact controls without changing the frozen harness or rerunning the native episodes.

1. **P2 — the command check does not bind the runtime to its pin or exclude additional read-only mounts.** In [cohort_audit.py](cohort_audit.py), `mounts` derives the module paths from the recorded ledger root, which correctly closes the foreign-adapter probe. But the runtime check at lines 394/404 only requires a mount matching `roles['runtime_path']` and an argv element matching `roles['python']`. Neither is joined to the policy's runtime pin and retained runtime inventory; the full mount population is not checked.

   Three separate copies of `r2-c8-draw2` still pass all 197 cases: changing the stdlib mount source and its role to `/tmp/r6-009-v3-unapproved/stdlib`; changing the interpreter mount source and its role to `/tmp/r6-009-v3-unapproved/python3.14`; or adding a read-only mount of the repository at `/extra-reference`. The first two leave the runtime pin, `provenance/python-runtime.json`, and binary inventory unchanged. The third leaves all existing roles and required mounts unchanged. Each copy passes before mutation and is rescanned, given a new terminal receipt, and resealed by the production finalizer afterward.

   Bind the retained runtime record to the policy's pinned runtime bytes, then derive the stdlib source/destination and interpreter source/destination from that record and the recorded repository root. Validate the complete command mount population, including library mounts and explicitly permitted ephemeral credential/TLS mounts. Preserve portability by checking retained relationships, without requiring the original directories to exist. Keep independent controls for the runtime source, interpreter source, and extra mount. These probes establish an audit acceptance gap; they do not establish that the real episodes used another runtime, exposed the repository, or leaked any model input.

2. **P2 — successful continuation is required only for the sender stage.** `receipts` at lines 412–429 checks the exit and resource outcome of `proposal-1`. `payload_receipts` at lines 439–443 compares every other stage's finish receipt with its process record, but does not require those stages to have succeeded.

   Two independent mutations pass all 197 cases: assembly exit `0 → 7`, and whole-declaration validation exit `0 → 7`. Each updates the matching `stage_finished` payload as well as the process record and runs the normal finalizer. Both retain an accepted proof and completed episode. The executing [episode.py](../../episode.py) rejects a nonzero exit at lines 99–108, so these are continuations the recorded driver could not have taken. Matching the two failure records is not sufficient.

   Apply the stage-success predicate to every stage that must return successfully on each frozen path: preparation, assembly, certificate verification, reconstruction, export, and both independent validations, as well as the sender. Check exit, exhaustion, monitor/observation status and workload cleanup separately from receipt equality. Keep limits appropriate to each stage; the sender's policy limits are not the build/replay limits. Give the assembly and final-validation corruptions their own controls.

The five new probes and their accepted results are retained in [cohort_v3_review_probes.py](cohort_v3_review_probes.py) and [R6-009-V3-REVIEW-PROBES.json](R6-009-V3-REVIEW-PROBES.json). The record uses `complete`, not a passing-conformance verdict: accepting these corruptions is the finding. None of the altered commands was executed. No new locked-code defect was reproduced in this review.

The old repairs were checked directly. Reservation now syncs attempt, draw, task, slots, and ledger directory in that order on every reservation, including after either interrupted-creation probe. Both failures leave only the activation row; each retry completes the full ancestry before appending. The zero-price copy rejects at `ledger:reservation_priced_from_contract_limits`; the foreign module, nonzero sender, credential-hash pair and five false payloads reject at their intended boundaries. The resource-limit receipt also rejects. These results are in the freshly rerun focused and mutation suites, not inferred from their reports.

| Independently checked | Result |
| --- | --- |
| Frozen focused suite | 28/28; exact names, no duplicates; includes the 17-fault sweep |
| Audit controls | 39/39: one accepted baseline and 38 rejected mutations, exact names and rejection cases |
| Current v3 audit | 197/197 |
| Superseded v2 audit | 197/197, explicit superseded status |
| Superseded v1 audit | 160/160, explicit superseded status |
| Six v3 event chains | 238 hashes, no mismatch |
| Six v3 seals | 1,632 entries: 1,596 retained and 36 ephemeral; all present and matching in the original trees |
| Campaign ledger | 12 chained rows; four consumed slots; 409,600 µUSD from checked prices; no open reservations |
| D1 entity bodies | Three serialized, two outbound, two received; all `e684c116…` |
| C8 entity bodies | Two serialized, two outbound, two received; all `797e2826…` |
| Proof exports and replay records | D1 `cd6081da…`, 3,702/3,721; C8 `67e53933…`, 1,470/1,471; empty axiom deltas |
| Review-start preservation | 42,777 files, zero changed or missing; excludes `.cache` and `__pycache__` |

The source lock still verifies and the policy remains disabled. The independent recount checks the original suite records as well as the fresh reruns, including their named populations and source digests. It decompresses and hashes the proof exports, reads the retained kernel reports, checks all seal entries including the available ephemeral files, and computes campaign money from the reservation prices. The preservation inventory is in the review scratch directory, with its digest and scope recorded in the recount; it is not a new committed artifact population.

Evidence:

- [Focused rerun](R6-009-V3-REVIEW-FOCUSED.json) and [audit-control rerun](R6-009-V3-REVIEW-CONTROLS.json).
- [Current audit](R6-009-V3-REVIEW-AUDIT.json), [superseded v2](R6-009-V3-REVIEW-SUPERSEDED-V2.json), and [superseded v1](R6-009-V3-REVIEW-SUPERSEDED-V1.json).
- [Independent recount program](cohort_v3_review_recount.py) and [recount result](R6-009-V3-REVIEW-RECOUNT.json).

Fresh outputs were written under `/home/jeans/scratch/tmp/r6-009-v3-review-zgw3vtel`, then copied to the new review records above. Reproduction commands take fresh output paths:

```bash
python3 -B experiments/r6/reviews/2026-09-14/cohort_audit.py --output /tmp/r6-009-v3-audit-fresh.json
python3 -B experiments/r6/reviews/2026-09-14/cohort_v3_review_probes.py --scratch /tmp --output /tmp/r6-009-v3-probes-fresh.json
```

Scope: I reran the focused controls, including their local canned HTTPS subprocesses, and the three historical audits and copied-artifact mutation suite. I did not rebuild or rerun the six native episodes, Lean, certificate generation, or kernel replay. Their retained observations remain the evidence being audited. No provider call, real credential read, signing, commit, or push was performed. Only new files under this non-locked review directory were added.

Repair these two audit relationships and carry the five probes into the exact-name-gated control suite. There is no reason from this review to spend another native freeze on the same harness. After the auditor accepts the untouched episodes and rejects the new copies, proceed to the extended capture-anchor checkpoint and freeze census membership before either arm.
