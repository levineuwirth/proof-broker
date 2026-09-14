# R6-008 revision 3 — independent review

2026-09-13. **Keep v3 disabled.** Its original controls reproduce and the
specific v2 regressions now reject, but three issues still block signing:
partial ledger operations can be misreported, an incomplete object can prevent
finalization, and the operator scanner can introduce the credential into its own
report. Three further findings concern append durability, an accounting field,
and incomplete auditor bindings. None of these probes demonstrates overspending
or an invalid proof in the original rehearsals.

Fresh results: 45 focused controls; 73 campaign audit cases; 31 auditor controls
(27 copy mutations, three predicate mutations, one positive), plus two
superseded-revision positives; seven operator-scan controls; and the 124-case
pilot audit using its retained scan-summary route. All pass. The focused suite
used local loopback subprocess actors. I did not execute new native episodes,
rebuild the overlay, or rerun Lean replay. There was no real credential read,
provider call, signing, commit or push.

The independent [recount](R6-008-V3-REVIEW-RECOUNT.json) verifies 86 event hashes,
705 sealed entries, policy `3a5af1d8…`, lock `30934b33…`, and all **34,791** files
in the review-start inventory with zero changed or missing. The inventory is a
working-tree snapshot of `experiments/r6`, excluding `.cache` and `__pycache__`,
not a committed baseline. The native records agree with the corrected report:
215 / 209 / 281 sealed files; 3,702 / 3,721 declarations; empty axiom deltas;
proof export `cd6081daac2fc64d718d28202d1742ff1e653e9862031fb19a5efeb7cd7d1812`.
The grant timing differences are 16,668,950 ns from creation to durable completion
and 322,365 ns from completion to first header.

[Eleven named review probes](R6-008-V3-REVIEW-PROBES.json) were run through
[campaign_v3_review_probes.py](campaign_v3_review_probes.py). The production
probes use the frozen focused suite's construction: doubles for setup,
preparation and the sender launcher, with real lifecycle, ledger and finalizer
code. The interrupted-record positive still closes the reservation and records
the grant, unknown outcome, consumed allowance and null observations correctly.
The adverse results below are separate from the checkpoint's passing tests.

1. **P1 — lifecycle ownership still follows successful returns, rather than
   committed ledger effects.**

   Three independently injected failures expose different parts of this gap:

   | Probe | Authoritative state | Episode's result |
   | --- | --- | --- |
   | `reserve_head_failure` | Reservation row was appended and fsynced; one reservation is open | Sealed rejection says `attempts_reserved: 0`, `reservation_id: null`, `ledger_reconciled: true` |
   | `reservation_receipt_failure` | Reservation succeeded; writing its run-local permit receipt fails | Reservation is correctly reported open, but reconciliation is never attempted |
   | `reconciliation_receipt_failure` | `send_grant` terminal row committed; zero open, one consumed; writing the run-local reconciliation receipt fails | Sealed rejection says `Reservation left open`, with disposition unavailable |

   The first injection fails `_write_head` after `_append` has durably written
   the reservation row. `snapshot()` can still read it: the old head is a valid
   prefix. The lifecycle is initialized before reserve, but its permit is assigned
   only after `budget.reserve` returns
   ([campaign_episode.py](../../campaign_episode.py#L182)). The absence of that
   assignment is still treated as evidence that nothing was reserved.

   The second injection fails the `campaign-permit.json` write. Several receipt
   writes remain between permit assignment and the protected block
   ([lines 195 onward](../../campaign_episode.py#L195)); this is why the new copy
   failure is handled but this earlier write failure is not. Its accounting is
   truthful, but it contradicts the claim that every post-reservation exit
   attempts reconciliation.

   The third injection fails the receipt write after `book.reconcile` committed.
   The outer assignment has not happened, so an artifact-write error is presented
   as an open ledger reservation. A failed function return cannot establish that
   its side effects did not occur.

   **Repair:** distinguish reservation/disposition state from artifact
   persistence. Establish transaction identity before effects can occur; recover
   the matching authoritative state after uncertain returns, or record that state
   as unknown. Put all post-reservation receipt writes inside the same lifecycle.
   Distinguish a failed reconciliation from a committed reconciliation whose
   evidence copy failed. Do not claim absence, release, or an open reservation
   from an exception alone. In these reproductions the ledger prevents a new
   reservation while one remains open; no authorization bypass was demonstrated.

2. **P1 — accepting an object is insufficient to make a transport record safe
   for finalization.**

   `http_empty_object` uses the same granted/interrupted episode as the passing
   positive but writes `{}` to `http.json`. `read_record` accepts it without a
   diagnostic. Reconciliation correctly consumes the grant. Later, the fallback
   calls [accounting_for](../../campaign_episode.py#L146), which indexes
   `http['connection_attempts']` without validating that field. The resulting
   `KeyError` escapes the last-resort handler: **no seal or terminal episode event
   is written**. The last event is `credential_receipt_checked`.

   **Repair:** validate required fields and their types for the process, HTTP and
   receiver records, retaining invalid bytes and a classified schema failure.
   Accounting must remain total for unavailable or invalid evidence; it must not
   throw while handling an earlier exception. Test missing required fields and
   invalid field types as well as non-object JSON. This probe establishes a
   malformed-object failure, not a claim that normal interrupted JSON writes
   naturally produce `{}`.

3. **P1 — root qualification reintroduces a credential disclosure in the
   scanner's own output.**

   [scan_roots](operator_disclosure_scan.py#L41) adds an unrestricted
   `'root': str(root)` to every inventory entry *after* the frozen scan. The
   original root label is redacted correctly, but these new strings are not.

   `scan_root_canary` runs the real operator CLI with a synthetic credential and
   a valid sealed run under `<temporary>/<canary>/episode`. The run's name, file
   contents and relative inventory paths contain no canary. Its scan is accepted,
   all four binding predicates pass, reported disclosures are zero, stdout is
   clean, and the process exits zero — yet the report contains **three copies of
   the token**, one in each new inventory root field. The otherwise identical
   safe-root positive contains zero copies. No real credential is involved.

   **Repair:** use a safe root identifier or index and keep absolute paths in the
   in-memory lookup only, or apply the frozen path-label mechanism consistently.
   Check the fully assembled report before publishing it. The regression should
   require no token or declared encoded form in the report, including when the
   root itself contains the canary. A clean scan of input files is not a scan of
   metadata added afterwards. This also preserves the successful two-root
   collision repair.

4. **P2 — short-write handling was fixed for grants but not ledger appends.**

   [Ledger._append](../../campaign_ledger.py#L268) still calls `os.write` once and
   ignores the return count before advancing the head. `ledger_short_append`
   injects a short write only on the ledger file descriptor: seven of the
   requested 728 bytes are written. `reserve` returns a successful reservation,
   the head advertises two rows, and the next `snapshot` raises `JSONDecodeError`.

   **Repair:** share the complete-write logic across exclusive creation and
   append, and do not advance the head until the append is complete. Preserve
   uncertainty on a partial failure. The grant short-write loop and its existing
   controls are correct; this is a remaining writer, not evidence that the grant
   repair failed. This fault probe executes ledger code only, with no sender or
   transmission. Subsequent parsing fails closed.

5. **P2 — a live accounting field still turns an unknown disposition into zero.**

   [accounting_for](../../campaign_episode.py#L170) computes
   `live_transmissions_consumed` as `(consumed or 0)` when `live` is true.
   `live_unknown_accounting` calls that pure function with an owned reservation
   and unavailable reconciliation: `allowance_consumed` is null,
   `ledger_reconciled` is false, but `live_transmissions_consumed` is zero.
   This is a helper-level probe; no policy was enabled or live transport invoked.

   **Repair:** preserve unknown in this field as well, or remove it and give
   consumers one unambiguous allowance field. If zero is established for a
   particular pre-launch path, bind it to that path's evidence. It cannot be the
   default for an unavailable disposition.

6. **P2 — three remaining auditor relationships are not checked.**

   Each has its own probe and scope:

   - **Imported accounting source:** v3's auditor now calls
     `driver.accounting_for`, but `campaign_episode` is absent from its
     [module bindings](campaign_audit.py#L51). `imported_driver_source` loads the
     actual helper from a temporary source copy with a harmless added comment.
     Its digest differs from the retained source; both the normal audit and the
     audit using that imported module accept all 73 cases. No retained artifact
     was changed. Bind this newly executed dependency with the appropriate
     revision rules. The probe demonstrates a missing source check, not malicious
     accounting behavior or inference attestation.
   - **Actual scanned streams:** [publication_recomputed](campaign_audit.py#L357)
     checks that each entry includes `raw` and that the gzip count agrees with
     the reported stream lists. It does not compare those lists to recomputation.
     `scan_stream_mutation` removes `gzip` from the solution export's stream list
     and decrements the aggregate count, then rebuilds the report-final, terminal
     commitments and seal. The unmodified copy and the mutation both pass all 73
     cases; scanning that file yields `['raw', 'gzip']`. Compare per-entry stream
     coverage to the fresh scan, not just to its own total. This is false
     provenance being accepted; the fresh scan still checks the actual gzip for
     disclosures.
   - **Durability versus legacy timestamps:** [grant](campaign_audit.py#L403)
     defaults a missing `grant_durable_at_ns` to creation time for every revision.
     `missing_durability` removes the v3 field and the grant predicate still
     passes. This is a predicate-only control, not a full rewritten-episode
     acceptance claim. Require the field in revisions that promise it; keep the
     creation-only qualification for v1 explicit. The original v3 timing field
     exists and independently matches the report.

Version dispatch is otherwise an improvement: the original v1 and v2 positives
now audit under explicit historical rules, with supersession and source
incompatibility recorded separately. Their original failures are not erased by
these positive historical-artifact audits.

There is one narrower preservation qualification. The named v2 focused, audit
and audit-control records match the prior review snapshot, but the shared
`R6-008-OPERATOR-SCAN-CONTROLS.json` was replaced by the seven-control record;
v2's report still links to it. Thus “all records unchanged” needs that exception.
Use a revision-specific filename for the new operator record and preserve an
explicit historical reference. My review-start preservation count above applies
to the state handed over for this review, not the transition from v2 to v3.

Before freezing another revision, run a small table-driven fault sweep around
each ledger persistence boundary, including exceptions **after** side effects,
and required-field/schema failures at the record boundary. For each injection,
check authoritative state, lifecycle state, allowance accounting, and evidence
completion separately. The existing “raise before reconciliation does anything”
control cannot establish what happens after a terminal row commits. This sweep
can live under non-locked review paths while the candidate repair is developed.

Then freeze once, rerun the affected native paths, and carry all existing
mutations forward. The runtime repairs require a new source lock; the scanner
and auditor repairs can remain under non-locked review paths. Keep the synthetic
64-transmission rehearsal authorization: its separation from live authority is
still appropriate and its substitution/replay controls pass.

Evidence: [focused controls](R6-008-V3-REVIEW-FOCUSED.json),
[campaign audit](R6-008-V3-REVIEW-AUDIT.json),
[audit controls and historical positives](R6-008-V3-REVIEW-AUDIT-CONTROLS.json),
[operator controls](R6-008-V3-REVIEW-OPERATOR-CONTROLS.json),
[pilot audit](R6-008-V3-REVIEW-PILOT-AUDIT.json),
[new probes](R6-008-V3-REVIEW-PROBES.json),
[recount source](campaign_v3_review_recount.py),
[review-start inventory](R6-008-V3-REVIEW-BEFORE.json.gz).

Reproduce from the repository root with fresh output paths:

```bash
python3 -B experiments/r6/reviews/2026-09-13/campaign_v3_review_probes.py --output /tmp/r6-008-v3-new-probes.json
python3 -B experiments/r6/reviews/2026-09-13/campaign_v3_review_recount.py --before experiments/r6/reviews/2026-09-13/R6-008-V3-REVIEW-BEFORE.json.gz --evidence-dir experiments/r6/reviews/2026-09-13 --output /tmp/r6-008-v3-new-recount.json
```

The production fault probes use the current disabled v3 policy and its pricing
admission clock; its capture expires on 2026-09-14 at 10:58 UTC. Historical
reruns need an explicitly recorded clock for those synthetic tests. These
commands do not authorize changing the policy, refreshing live pricing, or
making a provider call.
