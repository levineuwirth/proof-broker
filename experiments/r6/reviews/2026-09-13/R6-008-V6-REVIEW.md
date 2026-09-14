# R6-008 revision 6 — independent review

**Disposition: passes review at the canned checkpoint scope. All three v5
P2 findings are closed; no further blocking finding.** Policy `0f83bf91…`
and lock `1ac95bfa…` remain frozen, disabled and unchanged. This review does
not authorize signing or spending.

| Independent verification | Result |
| --- | --- |
| Focused suite | 49/49, exact names; all 17 sweep rows match the frozen source's `FAULTS` population |
| Current artifact audit | 76/76 |
| Auditor controls | 40 copy negatives, 4 predicate negatives, 1 layout positive; the baseline positive and 5 superseded positives are additional |
| Operator-scan controls | 9/9 |
| Pilot audit | 124/124 |
| Supplemental review probes | 11 completed, including the three previous reproductions |
| Event hashes / sealed entries | 89 / 705, zero mismatches; per run 20/215, 18/209, 51/281 |
| Saved proof | `cd6081daac2fc64d718d28202d1742ff1e653e9862031fb19a5efeb7cd7d1812`; recorded 3,702/3,721 declarations, empty axiom deltas |
| Recorded grant timing | 15,692,976 ns creation to durability; 442,062 ns durability to header |
| Review-start preservation | 37,026 files, zero changed or missing |
| Earlier run trees | 3,598 v1–v5 files unchanged against the independent v5-review snapshot |
| Earlier policies and locks | All ten files match that snapshot and their three retained copies each |

The [recount](R6-008-V6-REVIEW-RECOUNT.json) binds the fresh records, programs,
case populations, retained bytes and preservation results. The 45 directed
auditor controls mean 44 rejections and one layout acceptance; the baseline
and historical positives are counted separately. Historical revisions audit
under explicit version rules, retaining their source-compatibility
qualifications. Preservation uses the review-start working tree, excluding
`.cache` and `__pycache__`, rather than a committed baseline.

1. **Summary binding is repaired.** The new
   [summary predicate](campaign_audit.py#L444) binds the task, policy, mode
   and entire embedded accounting object to the audited records. Each of
   the previous isolated mutations—nested completion false, nested allowance
   1→0, and task ID changed to C8—now rejects at
   `rehearsal-3:summary:bound_to_audited_records`. Each copied population
   accepts first; the mutations use the production finalizer to rebuild
   publication records, event chain and seal. Their rejection is semantic,
   not stale byte provenance.

2. **Recovery now preserves the known disposition before the next read.**
   [Reconciliation](../../campaign_episode.py#L149) assigns the recovered
   terminal row to the lifecycle before taking the evidence snapshot.
   Repeating the head-write failure followed by snapshot-read failure now
   leaves `send_grant`, allowance 1 and `ledger_reconciled: true`, while
   recording missing `ledger-after` evidence and `evidence_complete: false`.
   The supplemental probe checks the reconciliation helper and accounting;
   the locked sweep separately drives the production lifecycle and confirms
   a sealed `episode_rejected` with those same dispositions. A positive
   head-failure-only control retains complete evidence.

3. **Repeated marker repair retains the torn-marker association.** The
   [valid-marker recovery branch](../../campaign_ledger.py#L363) preserves
   `torn_marker`. The repeated-fault probe creates a seven-byte release
   marker, writes the replacement unknown marker, interrupts the terminal
   append, then retries. The result is
   `unknown / completed_from_marker / torn_marker: release.json`, with one
   consumed allowance, no open reservation and an accepting slot predicate.
   This supplemental check covers the recovery operation and slot predicate,
   not a new complete native episode. The separate layout positive makes
   the auditor's acceptance of the resulting layout explicit.

The torn-`unknown.json` limitation is now accurately stated and tested:
`campaign_marker_torn_unrecoverable` holds the reservation open, and the
next reservation is refused. It does not promise automatic recovery. The
two additional scanner refusal probes also remain clean: malformed nonce
and unwritable report destination both yield sanitized stdout, empty stderr
and no canary occurrence, with no report created. Detailed outcomes are in
the [probe record](R6-008-V6-REVIEW-PROBES.json).

The next step is preparation for signing. The retained model capture reaches
its 86,400-second age limit at **2026-09-14 10:58:56.965977 UTC**, slightly
before the caching capture. The recount re-derives the historical admission
exactly and confirms `pricing_capture_stale` one second past the earlier
deadline. This checks local retained-source admission; it does not fetch
current prices or attest billing.

Put any fresh captures in a new directory, preserve these historical bytes,
and bind the selected capture into the next disabled policy before signing.
Compare the extracted rates and applicability conditions, exercise host and
actor admission and the affected rehearsal under that exact binding, then
sign the reviewed policy. [The current signing helper](../../campaign_contract.py#L212)
changes authorization and activates ledgers; it neither fetches nor refreshes
pricing. `SOURCES` and `freeze()` currently inherit the pilot source selection
and pricing pins, so refreshing them needs an explicit binding change.
After signing, the planned unit remains one authorized transmission followed
by its audit before cohort work. No further proof/search code change is
requested by this review.

The review reran the focused loopback/subprocess controls, artifact audits
and fault probes. It did not rebuild the overlay, rerun the complete native
episodes, replay Lean, read a real credential or contact a provider. The
focused suite tests synthetic signing in temporary state; the actual policy
was not signed and its live ledger remains absent. The initial recount used
the compact search-policy receipt for pricing and stopped on its missing
field; the corrected recount uses the retained full policy and was rerun
before producing its result.

Reproduction, using fresh output paths:

```bash
python3 -B experiments/r6/reviews/2026-09-13/campaign_v6_review_probes.py --output /tmp/r6-v6-probes-new.json
python3 -B experiments/r6/reviews/2026-09-13/campaign_v6_review_recount.py --before experiments/r6/reviews/2026-09-13/R6-008-V6-REVIEW-BEFORE.json.gz --evidence-dir experiments/r6/reviews/2026-09-13 --output /tmp/r6-v6-recount-new.json
```

The focused actor/sweep suite depends on the pricing window; the recount
uses explicit historical times. All repository changes made by this review
are additive files in this non-locked directory. No handed-over source,
policy, ledger, run or report was edited. Nothing was committed or pushed.
