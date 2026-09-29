# R6-008 revision 4 — independent review

**Disposition: the recorded checkpoint results hold; keep v4 disabled.**
Recovery can still lose ownership when its diagnostic writes fail, and an
operator-scan error can disclose the credential through stderr. The auditor
also accepts removal of v4's attempt identity. These need repair before
signing. Two further evidence-contract issues are described below so they can
be settled before the next freeze.

This review reran the focused controls, historical auditor, auditor controls,
operator-scan controls and pilot auditor. It also ran twelve new review probes
against temporary state. It did **not** rebuild the native overlay, rerun the
three complete native episodes, replay Lean, read a real credential, sign a
policy, or contact a provider. The focused suite includes its existing
subprocess/loopback controls; these are distinct from a new native episode.

| Independently checked | Result |
| --- | --- |
| Focused controls, exact case population | 47 pass, including the 13-fault sweep |
| Current episode audit | 73 cases accept |
| Audit controls | 31 copy mutations and 4 predicate mutations reject; 1 unmutated positive; 3 superseded positives separately |
| Operator-scan controls | 8 pass |
| Historical pilot audit | 124 cases accept |
| v4 event hashes / sealed entries | 89 / 705, no mismatch; per run 20/215, 18/209, 51/281 |
| Saved proof export | `cd6081daac2fc64d718d28202d1742ff1e653e9862031fb19a5efeb7cd7d1812`; recorded checks 3,702/3,721; empty axiom deltas |
| Recorded grant timing | 10,547,068 ns creation to durability; 419,668 ns durability to header |
| Review-start preservation | 35,536 files, zero changed or missing; working-tree baseline excluding `.cache` and `__pycache__` |
| Archived v1–v3 run files versus the independent v3-review snapshot | 2,158 unchanged |
| Restored v3 policy / lock | Match all three retained copies **and** the earlier independent review snapshot: `3a5af1d8…` / `30934b33…` |

The [recount](R6-008-V4-REVIEW-RECOUNT.json) binds these results to their
source records and exact bytes. Its `accepted: true` means the recount
completed, not that this review approves the policy. The new
[probes](R6-008-V4-REVIEW-PROBES.json) retain observations and precondition
checks; no raw credential-bearing stderr is retained.

1. **P1 — recovery receipts can still prevent lifecycle recovery.**
   [recover_reservation](../../campaign_episode.py#L216) emits
   `reservation_uncertain` before changing the initial `not_reserved` state
   or consulting the ledger. After finding a committed row, it emits
   `reservation_recovered` before assigning that row to `lifecycle['permit']`;
   ownership is assigned later in [invoke](../../campaign_episode.py#L269).

   Two probes start with the same head-write failure as the locked sweep,
   then fail one recovery-event append. This is explicitly a **compound
   fault**, not another single-cut result. The head-failure-only positive
   releases the reservation. With either receipt failure, the authoritative
   ledger instead retains one open reservation, no sender launches, and
   reconciliation is never called. Nevertheless, the sealed report says
   `attempts_reserved: 0`, `ledger_reconciled: true`, and
   `evidence_complete: true`. The first variant says `not_reserved`; the
   second says `reserved` while still counting zero attempts.

   The open reservation still blocks further reservations; these probes do
   not demonstrate extra spending. They demonstrate loss of known ownership
   and false accounting, precisely inside the new recovery path. Mark an
   uncertain operation as unknown before fallible diagnostics, retain a
   recovered permit immediately, and put lookup, snapshot and recovery
   receipts inside the same unconditional reconciliation guard. Failed
   receipt writes must not decide whether that guard runs. Accounting must
   also reject or conservatively represent a `reserved` state without its
   permit instead of calling it zero and reconciled.

   Evidence: `recovery_control`, `reservation_uncertain_event_failure`,
   `reservation_recovered_event_failure` in the probe record.

2. **P1 — the scanner's error path bypasses its output scan.**
   [bind_runs](operator_disclosure_scan.py#L60) reopens files after the frozen
   scan, including an unguarded `http.read_bytes()` at line 81. The final
   assembled-report scan is reached only if those reads succeed.

   The positive control creates a valid sealed run under a root named by a
   fresh synthetic canary and produces no disclosure. The negative changes
   only the bound HTTP file's readability, first establishing that reading it
   raises `PermissionError`. The frozen scan handles unreadability, but
   binding then throws an uncaught exception: exit 1, no report, **one canary
   occurrence in stderr** from the absolute path in the traceback. Stdout
   contains none. Thus rejection is correct, but confidentiality is not.

   Handle unreadable and malformed binding inputs as bounded failure
   records, and contain exceptions throughout the credential-bearing
   operation, including report writes. Exception messages and tracebacks
   must not bypass output sanitization. Add a control over stderr as well
   as stdout/report bytes, with an explicit unreadability precondition.
   Evidence: `operator_readable_control`, `operator_unreadable_bound_file`.

3. **P2 — attempt identity remains optional in a v4 audit.**
   [chain](campaign_audit.py#L209) requires `reservation_attempted` only if
   the event already appears in the input. [ledger_rows](campaign_audit.py#L253)
   checks the identity only if the permit contains `attempt_id`.

   Starting from a copy that accepts at all 73 cases, the mutation removes
   rehearsal-3's attempt field and its attempt event, rehashes the shared
   ledger and all affected mirrors, updates reservation/accounting bindings,
   and uses the normal finalizer to regenerate scans, terminal commitments
   and seals. **The mutated population still accepts at all 73 cases.**
   This tests removal of the relationship, unlike the existing wrong-value
   control.

   Derive mandatory events and fields from the declared revision. For v4,
   require one correctly ordered attempt receipt and a well-formed bound
   identity; let older revisions retain their explicit absence rules.
   Control deletion of each endpoint, their joint removal, and null/empty
   identities. Evidence: `attempt_identity_removed`.

4. **P2 — evidence completion is neither consistently recorded nor enforced.**
   These are separate observations, not one bundled mutation:

   A single failed `reservation_reconciled` event append occurs **after** a
   terminal ledger row and its evidence copies have committed. The driver
   reports `reconciliation_failure` and “Reservation left open”, although
   the ledger is closed, allowance 1 is correctly recorded, and
   `ledger_reconciled: true`. It also reports `evidence_complete: true`
   despite the missing receipt. The event append at
   [line 171](../../campaign_episode.py#L171) sits outside the evidence-write
   recorder, and [line 338](../../campaign_episode.py#L338) equates that
   exception with an open reservation.

   Separately, changing only the top-level summary's `evidence_complete`
   from true to false, leaving its audited accounting value true, and
   refinalizing the copy still passes all 73 audit cases. The
   [terminal check](campaign_audit.py#L399) authenticates the summary bytes
   but does not check this duplicated fact against accounting.

   Finally, a **predicate-only** control supplies positive proof/credential
   flags and `evidence_complete: false` to
   [finalize](../../campaign_episode.py#L432). It emits `episode_finished`
   with an accepting seal. This last control establishes the finalizer's
   behavior; it is not a claim that an incomplete native proof episode
   passed the full auditor.

   Freeze what this field means and which evidence is mandatory. Record
   failed receipts as evidence failures while preserving the actual ledger
   disposition, independently compare summary mirrors with audited facts,
   and give full-episode acceptance an explicit evidence requirement. Proof
   validity can remain a separate true fact. If the current field is meant
   only to describe the three reconciliation-copy operations, narrow its
   name and add the missing whole-episode predicate. The report's
   “permit receipt write fails → complete” row currently uses the broader
   wording for that narrower implementation.

   Evidence: `reservation_reconciled_event_failure`,
   `summary_evidence_contradiction`, `finalize_incomplete_evidence`.

5. **P2 — torn-marker recovery leaves an unreadable terminal receipt.**
   [Ledger.reconcile](../../campaign_ledger.py#L355) chooses a recovered
   release/unknown decision from the marker's filename without parsing its
   contents. A control writes a complete release marker, fails the terminal
   append, then confirms normal next-call recovery. Its paired fault writes
   only seven bytes of `release.json` before raising. On retry,
   reconciliation returns a successful `release`, closes the reservation,
   and hashes the unchanged seven-byte, invalid-JSON marker.

   This is **not** an unauthorized-release or overspending demonstration:
   the first call legitimately intended to release a terminated sender.
   The gap is that ledger recovery does not restore a valid evidence
   record, while the [slot auditor](campaign_audit.py#L314) expects a parsed,
   bound marker. Either recover a validated terminal receipt, or explicitly
   define incomplete marker evidence and its acceptance consequences. A
   hash of torn bytes does not by itself make them the declared receipt.

   The existing `reconcile_append_failure_after_marker` sweep case starts
   with the interrupted sender's already committed **send grant**. It does
   not test writing or recovering a torn release/unknown marker. Add that
   distinction to the sweep before the next lock. Evidence:
   `marker_recovery_control`, `partial_release_marker_recovery`.

One wording correction: “`_rows` never writes” is too broad.
[_rows](../../campaign_ledger.py#L266) opens the ledger for writing, truncates
a partial tail and fsyncs it. It never writes **the head**. The tail-repair
behavior is tested and described elsewhere; use that precise qualification.

The next step remains repairs and canned validation. Do the recovery-event,
marker-write and mandatory-field controls before freezing again. Auditor and
operator-scanner repairs can remain under the non-locked review paths.
Changes to the lifecycle/finalizer or locked suite require a new policy/lock
and native rehearsals under those bytes; retain v4 as the reviewed record.

Reproduce the review probes and recount with fresh output paths:

```bash
python3 -B experiments/r6/reviews/2026-09-13/campaign_v4_review_probes.py --output /tmp/r6-v4-probes-new.json
python3 -B experiments/r6/reviews/2026-09-13/campaign_v4_review_recount.py --before experiments/r6/reviews/2026-09-13/R6-008-V4-REVIEW-BEFORE.json.gz --evidence-dir experiments/r6/reviews/2026-09-13 --output /tmp/r6-v4-recount-new.json
```

The production probes use the current disabled v4 and its dated pricing
admission. Like the focused suite, they depend on the retained capture's
validity window; later expiry is a reproducibility constraint, not evidence
that the recorded fault observations changed. The recount reads retained
evidence without issuing requests or rerunning those time-sensitive paths.

Only additive files in this review directory were written. No locked source,
policy, historical run, ledger or handed-over report was edited. Nothing was
committed or pushed.
