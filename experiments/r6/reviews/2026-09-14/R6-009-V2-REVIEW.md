# R6-009 v2 independent review — eb8bf13

The six original findings are repaired on their demonstrated paths. The new D1/C8 demonstration also rederives. Three follow-ups remain before closeout: directory durability after an interrupted creation, the auditor's reservation-to-price binding, and remaining execution/receipt bindings in the auditor. The last two are audit defects; the observed native results remain supported by their original bytes.

All work was confined to temporary copies and new non-locked review files. No policy was signed, no real credential read, no provider contacted, and no original episode or authoritative campaign ledger modified. I reran the focused loopback suite and artifact audits, not native Lean episodes or kernel replay.

## Verified again

| Check | Fresh result |
| --- | --- |
| Locked focused suite | 27/27, exact frozen case set, including the 17-fault sweep |
| Current public audit | 181/181 named cases |
| Superseded-v1 audit | 147/147, explicitly reported as superseded |
| Supplied audit controls | 29/29; the original fifteen review probes now reject |
| Event chains | 238 hashes recomputed |
| Seals | 1,596 retained entries plus 36 ephemeral entries = 1,632, all present and hash-matching on the original trees |
| D1 bodies | Three serializations, two outbound bodies, two receiver captures; all `e684c116…` |
| C8 bodies | Two serializations, two outbound bodies, two receiver captures; all `797e2826…` |
| Ledger | Twelve rows; four consumed slots; 409,600 µUSD committed; no open reservation |
| Retained proof reports | D1 exports `cd6081da…`, 3,702/3,721 declarations; C8 exports `67e53933…`, 1,470/1,471; empty axiom deltas |
| Preservation | 41,112 review-start files unchanged; inventory excludes `.cache` and `__pycache__` |

The [recount](R6-009-V2-REVIEW-RECOUNT.json) derives these values from the body files, chains, seals and ledger rows. In particular, it checks each original reservation against the frozen token limits and rates, independently of the existing auditor. The 1,632 count includes ephemeral entries; it is not a count of Git-retained files or a retained-only checkout guarantee.

## 1. P2 — interrupted directory creation defeats the durability repair on retry

Location: [cohort_ledger.py:234](../../cohort_ledger.py), `Ledger.reserve`.

The normal path correctly fsyncs the new hierarchy. However, the list of directories to sync is derived from `path.exists()`. A failed attempt can create the directories and then fail before syncing their ancestors. A later attempt sees existing directories and no longer syncs those ancestors.

Two separate production-reserve probes establish this in [R6-009-V2-REVIEW-DURABILITY.json](R6-009-V2-REVIEW-DURABILITY.json):

1. Start with a new task/draw, then raise once at the task-directory fsync.
2. Independently, start fresh and raise once at the `slots` fsync.

In each case, the first reservation fails before any reservation row is appended. The directories remain. The next reservation succeeds and appends a 102,400 µUSD reservation, but its completed fsync calls cover only the new attempt directory, the draw directory and the ledger directory. It does not repeat the failed ancestor sync. Both probes assert the initial absence, the actual injected failure, the activation-only ledger after failure, and successful retry.

This is an interrupted-operation counterexample, not a simulated power loss or a claim that a retained grant disappeared. Directory existence does not establish that its parent link was made durable.

**Repair:** ensure the entire required authority ancestry is durable before every reservation append, including paths left by an earlier failed attempt. Syncing the bounded ancestry on every reservation is simpler than maintaining a separate durable-creation state. Add the two interrupted-creation/retry controls beside the clean first-task/new-draw controls. This changes locked code and needs a new lock and native checkpoint.

## 2. P2 — the auditor accepts a zero reservation against a 102,400 µUSD price admission

Locations: [cohort_audit.py:276](cohort_audit.py), `ledger_rows`; [cohort_audit.py:485](cohort_audit.py), `actor_check`; the cross-run committed-money calculation.

The auditor checks that the permit amount equals its nested reservation amount, and that those agree with other mirrors. It also rederives the pricing admission. It does not join the reservation amount to that independently rederived amount.

`zero_reservation_coherent` changes the last C8 reservation from 102,400 to zero, consistently updating the permit, reservation, accounting mirrors, ledger/head, snapshots, affected receipts, scan, terminal and seal. Host and actor pricing records still correctly say **102,400**. The public audit nevertheless returns **accepted, 181 cases**, now reporting only **307,200 µUSD committed** for the same four consumed slots.

The scope distinction is decisive: the probe also invokes the executing actor's `pricing_check` at the retained evaluation time. The original permit passes; the zero permit is rejected with **`pricing_reservation_amount`**. This is not a demonstrated live-spending bypass. The auditor has omitted a condition the executing actor already enforces.

Evidence: `zero_reservation_coherent` in [R6-009-V2-REVIEW-PROBES.json](R6-009-V2-REVIEW-PROBES.json).

**Repair:** compare every permit/reservation amount with the rederived price admission and bind the remaining reservation inputs—message bytes, reserved input/output tokens—to the actual envelope and frozen limits. Derive campaign committed money from those checked reservations. Keep the coherent-zero mutation so agreement among the mirrors cannot hide this relationship.

## 3. P2 — several execution and receipt claims remain detached from their evidence

Nine additional, independent copied-artifact probes still pass the public auditor at **181 cases**. Each copy passes an unmutated audit first and is finalized with the production scan/terminal/seal procedure. The failed-exit probe additionally rebinds the process receipt, reconciliation evidence, authoritative ledger/head and snapshot.

| Probe | Corruption accepted |
| --- | --- |
| `mounted_adapter_foreign` | `/adapter.py` is mounted from `/tmp/r6-009-v2-review-unapproved/cohort_https.py`, retaining only the approved basename |
| `nonzero_sender_exit_coherent` | The sender exits 7, while the episode is still accepted as having proceeded through proof consumption and final validation |
| `credential_hash_pair_false` | Expected and observed credential hashes, in both the receipt file and receipt event, are changed to the same all-zero digest; the actual canary and receiver digest remain unchanged |
| `pricing_admitted_receipt_wrong` | The admission receipt names an all-zero admission hash |
| `request_reserved_receipt_wrong` | The reservation event reports zero microdollars while the actual reservation remains 102,400 |
| `reservation_reconciled_receipt_wrong` | The reconciliation event names an all-zero row hash |
| `https_observed_receipt_wrong` | The HTTP-observation event names an all-zero HTTP record hash |
| `transport_validated_receipt_false` | The transport-validation event says envelope acceptance was false while the independently interpreted file says true |
| `resource_limit_receipt_wrong` | The proposal's start receipt claims a zero-second wall limit instead of the command's frozen 60 seconds |

Evidence: [R6-009-V2-REVIEW-PROBES.json](R6-009-V2-REVIEW-PROBES.json). Together with finding 2, these are ten accepted corrupted copies. They are not ten passing rejection controls.

Three concrete omissions account for the results:

- **Mounted implementation identity.** `mounts` at [cohort_audit.py:350](cohort_audit.py) checks module mount basenames. Separately proving that approved source files equal retained copies does not establish that the recorded command selected those files. Bind mount sources to the recorded repository layout and retained provenance. Preserve portability by mapping that recorded layout into the artifact; do not require a future auditor to have the original absolute directories.
- **Successful execution versus terminated workload.** `receipts` at [cohort_audit.py:378](cohort_audit.py) compares the finish receipt with the process record. Disposition checks establish termination and grant consumption. Neither establishes that the proposal stage returned successfully so the driver could continue into proof consumption. For these successful canned paths, enforce the stage acceptance conditions: zero exit, no exhaustion, monitor/observation success, and the frozen resource limits. A grant legitimately consumes allowance after a failed sender; that does not make the later proof path an admissible continuation of this driver run.
- **Receipt meaning versus receipt presence.** The expected sequence and hash chain are checked, but the listed event payloads are not compared with their files or independently derived values. The credential receipt similarly compares its two hashes with each other without binding them to the canary and receiver observation. Reconstruct the expected receipt payloads, including resource settings, and compare them exactly. Keep each corrupted relationship as a separate control.

These are narrower defects than the previous auditor's missing whole classes of checks. The restored body, task, context, attribution, publication and exact-case checks are useful and their supplied controls now pass. Restoring a named case population does not by itself complete every binding inside those cases.

## Closeout recommendation

Keep v2 as the reviewed record. Repair the directory retry path under a new lock; make the audit repairs in non-locked review files. Carry forward the original controls plus the new independent mutations, then rerun the native two-task/two-policy demonstration under the new lock. The findings do not change the experimental contract, model-visible prompt or proposed cohort design.

The raw results are retained as [focused controls](R6-009-V2-REVIEW-FOCUSED.json), [current audit](R6-009-V2-REVIEW-AUDIT.json), [superseded audit](R6-009-V2-REVIEW-SUPERSEDED.json), [supplied audit controls](R6-009-V2-REVIEW-CONTROLS.json), [fresh mutation probes](R6-009-V2-REVIEW-PROBES.json), and [durability probes](R6-009-V2-REVIEW-DURABILITY.json). Reproducers: [cohort_v2_review_probes.py](cohort_v2_review_probes.py) and [cohort_v2_review_recount.py](cohort_v2_review_recount.py).

The review recount initially treated the report's seal-entry count as retained entries only; it stopped at that assertion. Inspecting both inventories established the correct split, and the completed recount verifies all 1,632 entries rather than reclassifying the report as wrong. Only the completed recount is retained. Nothing was committed or pushed by this review.
