# R6-008 revision 2 — independent review

2026-09-13. **Keep the policy disabled.** The retained checkpoint is internally
consistent and the existing controls reproduce, but the failure/reconciliation
contract and its independent audit are not closed. Six findings below include
reproductions through production code and coherently rewritten artifact copies.
They do not establish that any original rehearsal overspent or used an invalid
proof.

I reran 39 focused controls (including actual subprocess/loopback actors), the
63-case campaign audit, 23 auditor controls, six synthetic operator-scan controls,
and the 124-case pilot audit using its retained scan-summary route. All passed.
The first focused run stopped at the sandbox's socket restriction; the fresh
loopback-enabled run completed all 39. I did not rerun a native episode, rebuild
the overlay, or execute Lean replay. The production fault probes use the same
setup/preparation/launcher doubles as the frozen interrupted-record control.
There was no real credential read, provider request, signing, commit or push.

The independent [recount](R6-008-V2-REVIEW-RECOUNT.json) verifies 86 event hashes,
705 sealed entries, the policy/source lock and all 34,047 review-start files,
with zero changes or missing files. That preservation inventory describes the
working tree at review start, excluding `.cache` and `__pycache__`; it is not a
committed baseline. The three retained seals contain 215 / 209 / 281 files.
The proof export remains `cd6081daac2fc64d718d28202d1742ff1e653e9862031fb19a5efeb7cd7d1812`,
with empty axiom deltas. The retained timing differences are 10,991,729 ns from
grant creation to durable completion and 486,847 ns from completion to header.

All new probe observations are in [R6-008-V2-REVIEW-PROBES.json](R6-008-V2-REVIEW-PROBES.json),
produced by [campaign_v2_review_probes.py](campaign_v2_review_probes.py). The twelve
named probes have asserted preconditions and asserted outcomes. Every full-audit
mutation first accepts its unmodified copy under all 63 cases. Auxiliary I/O
experiments are grouped in one named probe; these observations are not a new
checkpoint suite or an assertion that the defects are repaired.

1. **P1 — an exception after reservation can leave it open while the sealed
   summary asserts reconciliation.**

   [campaign_episode.py](../../campaign_episode.py#L104) accepts any JSON value as a
   record. A nonempty list in `http.json` reaches `.get` in ledger reconciliation;
   a list in the process record reaches `.get` while constructing evidence.
   Neither produces a reconciliation row. The outer handler then assigns zero
   reservations, `scope: "failed before any reservation"`, and derives
   `ledger_reconciled: true` from that default
   ([fallback](../../campaign_episode.py#L398)).

   `http_nonempty_list_after_grant` and `process_list_after_grant` each retain a
   real temporary reservation and authoritative grant, leave one reservation
   open, write no reconciliation, and still seal those false accounting claims.
   The terminal event is correctly `episode_rejected`; this is a false account
   of lifecycle completion, not a falsely accepted proof.

   The same defect does not require malformed sender output.
   `copy_failure_after_reservation` injects a `PermissionError` while copying
   transport pricing sources, after reservation and before launching the sender.
   That copy is outside the protected stage-launch block. It leaves an open
   reservation without a grant and produces the same false summary.

   Unreadable-file handling also remains incomplete: `read_record` catches
   `PermissionError` and immediately tries to hash the same unreadable file;
   evidence construction separately hashes files without guarding the read.
   `ledger.read_grant` catches JSON errors but not `OSError`. With actual
   temporary mode-000 files, both record reading and grant reconciliation raise
   `PermissionError`, rather than recording unavailable evidence or consuming an
   unknown outcome. The probe establishes unreadability before testing it.

   **Repair:** track reservation ownership independently of the returned
   accounting object. Put every operation after reservation under one
   reconciliation/finalization lifecycle. Reject non-object and invalid record
   shapes, make evidence hashing tolerate unavailable bytes, and preserve
   unreadability explicitly. If reconciliation itself cannot finish, record
   `ledger_reconciled: false` with the actual reservation and conservative
   allowance status. Do not derive absence of a reservation from an exception.
   The current open-reservation guard prevents a replacement reservation in
   these reproductions; no overspending bypass was demonstrated.

2. **P1 — the independent auditor does not reconstruct the new authority and
   release conditions.**

   Three separate relationships remain unchecked:

   - **Termination:** [ledger_rows](campaign_audit.py#L206) compares the recorded
     `termination_established` flag with the recorded row kind. It never applies
     the termination predicate to the hash-bound supervisor record.
     `release_despite_live_workload` changes only the substantive fact
     `workload_empty_after_cleanup` to false, then updates the matching finish
     receipt, evidence digest, ledger chain, snapshots, markers, scans and seals.
     Production's termination predicate returns false; all 63 audit cases still
     accept the asserted release.
   - **Authority contents:** [shared_ledger](campaign_audit.py#L425) checks only
     that some marker exists in each authoritative slot. In
     `authoritative_grant_altered`, the actual ledger-side grant is changed to an
     unrelated object while its retained run copy stays intact. Production's
     grant reader rejects `campaign_grant_binding`; the full audit accepts.
   - **Authority handoff:** [receipts](campaign_audit.py#L238) checks a few command
     tokens, including the presence of `/grant`, without binding either mount's
     source to the policy-derived ledger and reservation slot. Independently
     changing the host source for `/ledger.ndjson` or `/grant`, followed by normal
     finalization, still passes all 63 cases. These are command-record mutations;
     I did not execute a sender with the altered mounts.

   **Repair:** independently derive termination and expected disposition from
   the actual process/HTTP/grant evidence; compare each authoritative marker's
   type and contents with its reservation, terminal row and retained copy; and
   validate the complete authority mount relationship, including read/write
   mode, using the recorded original-path mapping. Preserve separate controls
   for each relationship. A copied audit tree needs an explicit mapping to the
   original execution paths, not an assumption that execution occurred there.

3. **P2 — the successfully reconciled interrupted-record path invents zero
   transport observations.**

   [accounting_for](../../campaign_episode.py#L141) substitutes zero counters,
   `grant_committed: false` and `send_outcome: "not_started"` when the HTTP record
   is unavailable. `truncated_http_after_grant` reproduces the existing `{`
   interruption: reconciliation correctly records a committed grant,
   `send_outcome: "unknown"`, and one consumed slot; accounting simultaneously
   says the grant was not committed and nothing started.

   **Repair:** derive grant/disposition facts from authoritative reconciliation.
   Keep unavailable connection/header/body/receipt observations null or explicitly
   unobserved. Preserve a distinction between the allowance conservatively
   consumed and the number of transmissions actually observed. Missing evidence
   cannot establish a zero even when the proof episode is rejected. Add controls
   that inspect accounting, not only the reconciliation and terminal event.

4. **P2 — a short write is reported as a complete durable grant.**

   [write_exclusive](../../campaign_ledger.py#L65) ignores the return value of
   `os.write`. The I/O probe injects a short write that really writes seven of the
   expected 350 bytes. `commit_grant` returns a durability timestamp; the grant
   reader rejects the resulting truncated record. The actor's call site treats
   a successful return as permission to proceed with headers.

   **Repair:** complete the write with a checked loop before reporting durable
   completion; handle zero progress and exceptions without sending. Retain the
   final-name marker so uncertainty remains consumed. In this probe later
   reconciliation does conservatively produce `unknown`; no second grant or
   live transmission was demonstrated. Test a short write and a failure after a
   partial write independently. The current fsync and racing-writer controls do
   not exercise either condition.

5. **P2 — publication recomputation leaves false provenance fields accepted.**

   [publication_recomputed](campaign_audit.py#L259) exempts `events.ndjson` from
   the inventory hash comparison, rather than comparing its pre-terminal byte
   prefix. It also omits inventory length and per-entry scan-status comparisons.
   `scan_event_hash_forged` changes that entry's hash to 64 zeroes;
   `scan_event_length_forged` separately changes its length to zero. Each rebinds
   the scan's final record, terminal commitments and seal; each passes all 63
   cases. The second observation does not depend on the special hash exemption.

   **Repair:** compare the exact prefix before the terminal event and validate
   unique inventory membership, lengths and relevant scan fields. Keep final
   report/seal exceptions explicit. The fresh scan still catches actual
   disclosures in the existing controls; these probes establish false scan
   provenance being accepted, not a demonstrated hidden credential disclosure.

6. **P2 — multiple publication roots collide on relative filenames.**

   [bind_runs](operator_disclosure_scan.py#L46) assigns every inventory entry to
   every root. The frozen scanner records paths relative to their individual
   roots, so identical relative paths overwrite earlier entries in that map.
   `operator_multi_root_collision` constructs two different, valid sealed runs:
   both pass alone; the combined scan is clean; both seals and commitments pass;
   combined coverage becomes `[false, true]`.

   **Repair:** retain root-qualified entry identity, scan roots separately before
   joining their inventories, or temporarily enforce one enclosing directory.
   Add a two-root control with colliding relative paths and distinct contents.
   This reproduction is a false rejection in the advertised repeatable `--root`
   interface; it does not defeat the current single-root scan.

There are also three reporting corrections:

- The native table says 3,700 / 3,719 declarations. The retained v2 verdict
  records **3,702 / 3,721**, independently confirmed by the recount.
- The 23 audit controls comprise **19 copy mutations, three predicate
  mutations, and one unmutated positive**, not 20 rejected copy mutations plus
  three predicate mutations.
- A v2 auditor refusing v1 at `modules:bound_to_retained_copies` establishes
  **auditor/source incompatibility**. It is not a new invalidity verdict on the
  historical episode. V1's already established defects remain defects, but
  supersession itself is not one. Preserve a matching versioned auditor or
  explicit version dispatch so that historical results remain independently
  interpretable; keep the incompatibility qualification distinct.

The 64-transmission rehearsal authorization is appropriate for exercising the
same ledger mechanics without spending live allowance. The purpose and exact
authorization checks passed their controls, including live rejection of a
rehearsal activation. There is no reason to remove that ledger for this review.

Repair findings 1, 3 and 4 under a new disabled source lock and rerun the focused
and native paths affected by those changes. The auditor and scanner repairs can
remain under non-locked review paths, with the independent mutations retained.
Do not sign this revision on the strength of its current green recount.

Evidence: [focused controls](R6-008-V2-REVIEW-FOCUSED.json),
[campaign audit](R6-008-V2-REVIEW-AUDIT.json),
[audit controls](R6-008-V2-REVIEW-AUDIT-CONTROLS.json),
[operator controls](R6-008-V2-REVIEW-OPERATOR-CONTROLS.json),
[pilot audit](R6-008-V2-REVIEW-PILOT-AUDIT.json),
[new probes](R6-008-V2-REVIEW-PROBES.json),
[recount source](campaign_v2_review_recount.py),
[review-start inventory](R6-008-V2-REVIEW-BEFORE.json.gz).

From the repository root, use fresh output paths:

```bash
python3 -B experiments/r6/reviews/2026-09-13/campaign_v2_review_probes.py --output /tmp/r6-008-v2-new-probes.json
python3 -B experiments/r6/reviews/2026-09-13/campaign_v2_review_recount.py --before experiments/r6/reviews/2026-09-13/R6-008-V2-REVIEW-BEFORE.json.gz --evidence-dir experiments/r6/reviews/2026-09-13 --output /tmp/r6-008-v2-new-recount.json
```

The production probes use the current frozen policy and its time-limited pricing
admission; a later rerun can require an explicitly recorded evaluation clock.
They must not be interpreted as a live authorization or an instruction to change
the retained policy. The recount and historical audits do not refresh pricing.
