# R6-008 revision 5 — independent review

**Disposition: checkpoint results verified; three P2 issues remain to close
before signing.** The previous directed controls now produce the required
outcomes. The new probes did not reproduce a credential disclosure or permit
another transmission. The remaining problems concern summary bindings and
preserving evidence through a second recovery fault.

| Independent verification | Result |
| --- | --- |
| Focused suite | 49/49, exact names; 16 sweep rows matched against the frozen source's `FAULTS` population |
| Current historical auditor | 73/73 |
| Auditor controls | 37 copy mutations and 4 predicate mutations reject; 1 unmutated positive; 4 superseded positives counted separately |
| Operator-scan controls | 9/9, including the unreadable-file precondition and no canary in stderr |
| Pilot audit | 124/124 |
| Event hashes / sealed entries | 89 / 705, zero mismatches; per run 20/215, 18/209, 51/281 |
| Saved proof | `cd6081daac2fc64d718d28202d1742ff1e653e9862031fb19a5efeb7cd7d1812`; recorded 3,702/3,721 declarations, empty axiom deltas |
| Recorded grant timing | 24,924,538 ns creation to durability; 501,335 ns durability to header |
| Review-start preservation | 36,281 files, zero changed or missing |
| Earlier run trees | 2,878 v1–v4 files unchanged against the independent v4-review snapshot |
| Earlier policies and locks | All eight files match that snapshot and their three retained copies each |

The [recount](R6-008-V5-REVIEW-RECOUNT.json) binds the records, source hashes,
case populations and preservation results. Preservation uses the review-start
working tree, excluding `.cache` and `__pycache__`; it is not a committed
baseline. The actual three native summaries have correct task IDs, accounting
copies and completion fields; the recount checks those independently of the
auditor gap below.

The review reran controls, artifact audits and eleven supplemental probes. It
did not rebuild the overlay, rerun the complete native episodes, replay Lean,
read a real credential, sign a policy or contact a provider. The focused
suite's subprocess and loopback controls are distinct from new native
episodes. The initial focused invocation encountered the sandbox socket
restriction; the retained result is a fresh complete run with local socket
access. An initial review probe stopped because I expected the wrong first
rejection stage; that review-code assertion was corrected and the complete
probe set rerun into a fresh record.

1. **P2 — the summary's embedded accounting and task identity remain
   unaudited.** [terminal](campaign_audit.py#L412) compares the new top-level
   completion fields, while [accounting](campaign_audit.py#L508) recomputes
   `accounting.json`. Neither compares `credential-summary.json.accounting`
   with that audited object, or binds the summary's `task_id` to the task.

   Three separate mutations each begin with a copy accepting at 73 cases:
   set only the embedded `evidence_complete` to false; set only its
   `allowance_consumed` from 1 to 0; or set the summary's task ID from
   `verinf-d1-70` to the registered C8 ID `c1-c8-2p18`. Each uses the normal
   finalizer to rebuild the publication records, event chain and seal.
   **Each mutated copy still accepts at all 73 cases.** A separate control
   changing the top-level completion field is rejected, showing that the
   newly added guard itself works.

   A reader of the summary can therefore get a different obligation or cost
   disposition from a reader of the audited records. This does not change
   the proof's actual D1 binding or the authoritative ledger. Bind the entire
   embedded accounting object to the independently checked file, and bind
   summary identity fields to the task and policy. Keep the three mutations
   separate. This repair belongs in the non-locked auditor and its controls.

   Evidence: `summary_top_level_control`, `summary_nested_evidence`,
   `summary_nested_allowance`, `summary_task_identity` in the
   [probe record](R6-008-V5-REVIEW-PROBES.json).

2. **P2 — terminal-row recovery still preserves ownership after a fallible
   snapshot read.** In [reconcile](../../campaign_episode.py#L149),
   `find_terminal()` successfully recovers the committed row, then
   `book.snapshot()` runs before the row is assigned to
   `lifecycle['reconciliation']` at line 155. The analogous reservation path
   already preserves the permit before this operation.

   The positive control fails the terminal head write and confirms successful
   recovery. Its paired **compound-fault** probe additionally fails the
   subsequent snapshot read. `find_terminal()` has already returned the
   `send_grant` row, but reconciliation raises with the lifecycle still
   lacking it. The authoritative ledger has zero open reservations and one
   consumed allowance; accounting reports `ledger_reconciled: false` and
   `allowance_consumed: null`.

   This is conservative accounting, not an extra-spending path. It discards
   a disposition that was already learned, and sends the caller into its
   open-reservation diagnostic. Preserve the recovered row before reading
   its evidence snapshot; record a failed snapshot as incomplete evidence
   while retaining the known disposition. The probes exercise the production
   reconciliation helper and accounting, not a complete episode or its
   finalization. A standing production-lifecycle control should also check
   finalization and the failure label after the repair.

   Evidence: `reconciliation_head_failure_control`,
   `reconciliation_recovery_snapshot_failure`.

3. **P2 — interruption of torn-marker repair loses the torn-marker
   association on retry.** The new single-fault path works: seven bytes of
   `release.json` become a terminal `unknown` row with a valid `unknown.json`
   beside them, and the slot predicate accepts that layout.

   A paired **compound-fault** control then fails the terminal append after
   the valid replacement marker has been written. On the next call,
   [the valid-marker branch](../../campaign_ledger.py#L363) produces
   `unknown / completed_from_marker` but drops `torn_marker: release.json`.
   Both files still exist. The ledger safely consumes one allowance and
   closes the reservation, but [slot_contents](campaign_audit.py#L310)
   expects only `unknown.json` and rejects the layout.

   Preserve the association across recovery retries, or derive the permitted
   residual-marker layout independently in the auditor under an explicit
   rule. The probe compares the single-fault positive and repeated-fault
   outcome at the slot predicate; it does not claim to have run either as a
   complete native episode or through the full three-run checkpoint audit.
   Evidence: `marker_release_repair_control`,
   `marker_release_repair_interrupted`.

One **non-blocking qualification**: a torn `unknown.json` is deliberately
unrecoverable by the current method. It raises
`campaign_marker_torn_unrecoverable`, leaves the reservation open, and blocks
the next reservation with `campaign_reservation_open`. The generic wording
“a torn marker → unknown” should distinguish this from recovery of a torn
release marker. This is a safe stop, not a demonstrated allowance bypass;
record its operator-recovery limitation rather than promising automatic
recovery. Evidence: `marker_unknown_torn`.

The scanner containment also survived two additional paths: a malformed
nonce causing `TypeError`, and a report write failing with
`IsADirectoryError` on a canary-bearing path. Both produce a sanitized stdout
refusal, exit 2, empty stderr and no token occurrence. No report is written
in these fallback cases; the control records that absence explicitly.

The lifecycle repair is narrow: move preservation of an already-known row
before the evidence read. Settle that and the repeated-marker rule, add the
paired controls, and then freeze once if locked code changes. The summary
binding repair can be made without changing the frozen policy. Keep v5's
native evidence as the reviewed record; do not edit it to express a repaired
auditor's conclusions.

Reproduction, using fresh output paths:

```bash
python3 -B experiments/r6/reviews/2026-09-13/campaign_v5_review_probes.py --output /tmp/r6-v5-probes-new.json
python3 -B experiments/r6/reviews/2026-09-13/campaign_v5_review_recount.py --before experiments/r6/reviews/2026-09-13/R6-008-V5-REVIEW-BEFORE.json.gz --evidence-dir experiments/r6/reviews/2026-09-13 --output /tmp/r6-v5-recount-new.json
```

The focused actor/sweep suite depends on the retained pricing window;
these supplemental copy/ledger/scanner probes and the recount issue no
provider request. All repository changes made by this review are additive
files in this non-locked directory. No handed-over file, policy, ledger or
run was edited. Nothing was committed or pushed.
