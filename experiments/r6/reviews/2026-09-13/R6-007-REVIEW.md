# R6-007 independent review — 2026-09-13

**The live proof result survives independent checking. R6-007's current audit
and spending controls do not justify closeout as a reusable evaluation harness.**
Preserve this pilot as exploratory evidence, correct the reporting and add a
non-locked auditor for its historical artifacts. Repair executing code in a new
policy before another provider call. Do not edit the frozen pilot sources or
retrofit its receipts.

This review made no provider request and read no operator credential. It did
execute the saved certificate verifier and both kernel replays, in isolated
`bwrap --unshare-all` processes, and a small deterministic SDK diagnostic.
The original live call, assembly, reconstruction, compiler build and TLS
handshake were not repeated. Nothing was committed or pushed.

## What independently holds

| Evidence | Result |
| --- | --- |
| Published recount / control replay | 230 predicates and 17 named controls pass on the current tree. These are different populations, not 247 conformance tests. |
| Every recorded event chain | 167 event hashes across all six runs; all valid. |
| Every existing seal | 1,109 retained entries across five sealed runs; all hashes match. live-1 remains unsealed. |
| Source / binary binding | All 53 recorded SDK/bridge base hashes match `e627efe`; all 53 current overlay hashes match their records; all 15 recorded binary hashes match. This is not compilation attestation. |
| Frozen task / context / input | Pristine bytes match `Bracket.lean@c07e03c`; reconstruction, preparation and frozen contexts agree; the pilot request and arguments independently regenerate. |
| Pricing | Host and actor admission independently re-derive at their recorded evaluation times from the retained sources. Reservation 102,400 µUSD; ceiling of reported usage 12,403 µUSD. Neither is a bill. |
| Farkas witness | `hwidth + 32769·neg_goal` cancels every variable and leaves `604462909666027343249410 > 0`. |
| Saved proof-path audit | The shared proof checker passes, with additional context, task and witness equality checks. |
| Fresh certificate verification | Accepted; semantically identical verdict to the saved certificate report. The JSON formatting differs. |
| Fresh kernel replay | Both accepted; 3,700 / 3,719 declarations; both raw reports reproduce byte for byte, including expected declarations, types, reference checks and axioms. |
| Review preservation | All 1,346 paths snapshotted at review start remain unchanged. This is the review's selected input population, not a recount of every historical file in the repository. |

The new replay uses the recorded executables after hash checks and the current
host shared libraries. It rechecks the saved proof export against the frozen
challenge and freshly reconstructed validation policies; it does not reproduce
the compilation that created those executables. The original provider metadata
remains provider-reported evidence, with no inference attestation.

## Findings requiring action

1. **P1 — The one-attempt cap is per run directory, not per authorization.**
   [pilot_episode.py:105](../../pilot_episode.py#L105) supplies
   `run/'reservation-ledger.ndjson'`. Every new `--run-dir` therefore starts a
   new budget. [pilot_budget.py:46](../../pilot_budget.py#L46) only checks the
   rows of that file. The native artifacts already contain two reservations of
   102,400 µUSD, live-1 and live-2, under the **same** policy and approval.
   live-1 did not connect; this is not evidence of two provider charges.

   The offline probe creates two new ledgers under that same policy. Both host
   reservation and actor transport admission accept both: 204,800 µUSD reserved
   against the stated campaign ceiling of 102,400. A second reservation in the
   *same* ledger correctly rejects, proving which boundary exists. The
   `ledger_ceiling_is_one_attempt` control checks policy numbers; it never calls
   the ledger. The report's claim that another call requires a new signature is
   consequently an operator rule, not an executing guard.

   Use an authorization-scoped ledger outside individual run directories,
   shared across invocations, with atomic reservation and explicit treatment
   of pre-send failures. Preserve live-1's reservation instead of silently
   reclassifying or removing it. If author approval is for transmissions rather
   than reservations, freeze that distinction and its release evidence before
   executing it. The actor's authorization check also accepts a monetary
   authorization of zero and an empty approver that the host check rejects;
   independently enforce the full scope in both paths. The current “signature”
   is a name/timestamp record, not a cryptographic signature.

2. **P1 — The recount is not an episode auditor.**
   [pilot_final_checks.py:52](pilot_final_checks.py#L52) reads selected claims,
   but never invokes the shared proof checker, binds the proof export to its
   reported hash, checks the frozen type/axiom policy, reconstructs the live
   request, or re-derives the recorded pricing/ledger semantics.

   Twelve independent mutations each still return **230 checks, accepted**.
   Every mutated copy first passes unmodified. For the first nine below, the
   publication scan, report scan, terminal event, event chain and seal are
   regenerated using the normal finalizer. All 263 retained hashes and all 52
   event hashes remain consistent. These are not stale-seal failures.

   | Mutation | What the recount misses |
   | --- | --- |
   | Wrong verdict task | Original task identity |
   | Wrong local target type, with report/receipt agreement | Frozen statement fingerprint |
   | `sorryAx` in the replay report, with report/receipt agreement | Axiom ceiling / recomputed delta |
   | Invalid decompressed proof export | Actual proof bytes versus claimed solution hash |
   | Reconstruction context target changed to `False` | Equality to the frozen obligation |
   | Assembled witness coefficient changed to `999999` | Model response → certificate binding |
   | Host admission changed to `accepted: false` | Re-derived admission and its receipts |
   | Ledger replaced by one `{}` line | Ledger contents; only its line count is checked |
   | Changed outbound body | Local serialization → send-capture binding |
   | Corrupted rehearsal-4 proof file, original seal left stale | Rehearsal retained-file hashes are not checked at all |
   | Changed live-1 preparation file | Its post-hoc manifest is recomputed, not compared to the reviewed population/digests |
   | Extra `live-3` directory | The six-run population is not checked for additions |

   The shared proof checks plus explicit task/context/witness equality reject
   the six proof-side mutations at their intended boundaries. The original
   unmutated proof passes them and fresh replay. This finding concerns the
   checker, not a demonstrated defect in the original mathematical result.

   Add a non-locked pilot auditor that reconstructs the complete evidence
   relationships, uses the shared proof checker, and binds the six-run
   population, individual source/policy versions and historical inventories.
   Do not validate copied `--runs` data against unrelated originals: the current
   `locks()` and `operator_scan()` still read their fixed original locations.
   Add exact-name-gated, single-relationship mutations. Pin the named semantic
   cases independently of the output's self-reported count. The 230 count is
   currently computed, not asserted; 167 predicates check individual event
   hashes, and availability of the optional local scan report changes the count.

3. **P2 — Live mode discards a locally available transport check.**
   [pilot_budget.py:132](../../pilot_budget.py#L132) requires both `sent` and
   `received` before testing either against the serialized body. A real provider
   supplies no local `received-body.json`, so `accepted` is always null for
   this combined predicate. In the changed-outbound control, production
   `interpret(..., live=True)` returns **no error**, although the saved sent
   bytes differ from the serialized envelope.

   Split local `serialized == outbound` from remote receipt. The first must be
   checked; the second is unavailable. Keep the existing qualification that a
   local send capture does not attest the remote model input. Authentic live-2
   has equal local bytes; this is an unguarded relationship, not an observed
   alteration of that request.

4. **P2 — The actual live trace misattributes the proposer and duplicates
   supervisor receipts.** The live-2 verdict and `recovery_started` name
   `live_model_response`, while event 22 (`certificate_assembled`) and event 26
   (`recovery_finished`) name `canned_provider_response`. Those values are
   hardcoded in the reused [consumer](../../provider_episode.py#L200).
   Retaining the consumer's version/route is correct; attributing the witness
   to a canned proposer is a different claim. The report's unqualified “new
   proposer identity” does not describe the whole trace.

   Events 13/14 are both `supervisor / proposal-1 / stage_started`, and 15/16
   are both `stage_finished`. [pilot_network.py:73](../../pilot_network.py#L73)
   and line 88 append receipts that the frozen supervisor already appends.
   There was one process, not two; the finish payloads agree. The current
   recount never checks that relationship or the expected event sequence.

   For these frozen artifacts, retain the literal values and supply an audited
   interpretation of the reused component and duplicate receipt pairs. A new
   policy should pass proposer provenance through the consumer and let the
   supervisor own stage receipts, or distinguish observer/event identities.
   This belongs before any analysis of routing, fallback, attempts or latency.

5. **P2 — The deterministic-search comparison overclaims novelty and names
   the wrong baseline hash.** The report's bounded-enumeration observation is
   correct; its later “region ... deterministic search does not cover” is not.
   Existing [exact recovery](../../../../sdk/lib/farkas_search.ml#L732) searches
   small supports without the coefficient bound of three. A new offline probe
   against the existing SDK produces:

   | Diagnostic input | Bounded search | Exact recovery |
   | --- | --- | --- |
   | Full saved final IR | `2·hZ + neg_goal`, verified | Same first witness, verified |
   | Same IR retaining only the `hwidth` hypothesis | No witness | **`hwidth + 32769·neg_goal`, verified** |

   The restricted input is a diagnostic, not a new original-obligation episode
   or a performance comparison. It directly disproves exclusion from the
   deterministic recovery mechanism's witness space. Say “a different observed
   support from the deterministic first hit, outside bounded enumeration”;
   make no capability gain claim. Also, `cd6081da…` is R6-003's **canned** proof
   export. The three golden deterministic broker episodes all have
   `f4c179f3…`. Restrict the earlier-witness comparison to successful **D1**
   cases; the C8 controls use `hhi`, not `hZ`.

6. **P2 — Keep credential use, exact receipt and publication evidence
   separate at the live boundary.**
   [pilot_episode.py:174](../../pilot_episode.py#L174) sets `exact_receipt` true
   for every non-null status other than 401, including 500 or 503. Those can
   describe server failures, not exact receipt of a particular credential.
   [Official OpenAI error documentation](https://developers.openai.com/api/docs/guides/error-codes)
   distinguishes invalid authentication from server failures; it supplies no
   exact-credential receipt guarantee. live-2's 200/completed response is useful
   evidence of a successful provider request, with a narrower meaning than the
   old fixture's digest-matched receipt.

   The operator scan is useful supplementary evidence. Its full report digest
   matches the summary; all 43,108 inventory entries are unique; all 1,329 pilot
   files are covered and unchanged. Across that inventory, only `.gitignore`
   differs now. The report and later review files were added after the scan.
   I verified inventory/hashes, **not** the secret-dependent search. There is
   no retained commitment to the actual live header that binds the operator's
   later scanner input to the bytes sent. Treat that identity as an operator
   assertion, not an independently reconstructed binding.

   A future version should bind a scanner receipt to a commitment recorded at
   the credential handoff, and bind its result to the final publication
   inventory. A digest-matched candidate search is not automatically equivalent
   to the existing full-value scanner: it needs a declared candidate space and
   controls for the supported encodings, gzip streams and boundaries. Preserve
   the operator-mediated full-value scan until an alternative establishes the
   intended coverage. A final publication scan must cover the chosen release
   bytes, including later additions, without calling the live synthetic-canary
   scan a real-credential admission gate.

## Known defects and smaller qualifications

The three defects already documented are real: the synthetic scan does not
test the real credential; credential decoding is outside the actor's exception
boundary; and a `StageFailure` prevents episode finalization. The last applies
beyond credential format, including timeouts, resource failures and later proof
stages. Fix and exercise each phase in the new policy; do not edit the old
locked source to make its history look cleaner.

`live_model_calls` is computed from `body_sends_returned` at
[pilot_episode.py:195](../../pilot_episode.py#L195). A partial send followed by
an exception can have `body_sends_started == 1`, `body_sends_returned == 0` and
unknown provider processing, yet be reported as zero calls. Retain the separate
attempt/transmission counters and represent this uncertainty explicitly. The
observed successful live-2 result is unaffected. Likewise
`live_model_cost_usd` currently contains a usage-priced estimate; it should not
become a billing observation in downstream tables merely because of its name.

The report's “four housekeeping runs (`rehearsal-1` … `rehearsal-3`)” is three.
Its reproduction command for the control replay refuses to overwrite the
already-existing output; use a new `--output` path. Preserve the old preflight
as dated history, including its disabled-policy state and incomplete credential
format instructions, rather than presenting it as the current runbook.

## Retention, publication and commits

**Keep all six runs under an explicit allowlist.** The current selection has
1,305 files, 35,099,485 apparent bytes, 413 distinct blobs and 8,325,998 unique
bytes. Keeping only live-1, live-2 and rehearsal-4 gives 725 files and 6,634,867
unique bytes. The first three rehearsals therefore cost only **1,691,131
additional unique bytes**, before Git compression, within this population.
All currently sealed required paths survive the ignore rules. Deleting the
three early directories from the release also breaks the documented six-run
recount and weakens the account of the repairs.

Full-tree and retained-only coverage must remain distinct. live-1's 193-file
post-hoc inventory contains two `.olean` files excluded by Git; only 191 files
are selected. The review-start inventory preserves those historical hashes,
but a clean checkout cannot reproduce unavailable bytes. Give its audit an
explicit retained-only mode and preserve the full historical inventory, rather
than silently recomputing a different “193-file” commitment. The large local
operator scan report is also intentionally excluded; a public summary is an
operator assertion with a digest commitment, not a reproducible secret scan.

**The credential filename is publishable as host metadata; keep the sealed
command unchanged.** It contains a private-file path, not a key value or an
authentication capability. The other commands already disclose the same home
directory. This choice accepts disclosure of that file layout and label. Do
not copy the credential itself. If that layout later needs to be withheld,
make an explicitly redacted derivative with a separate inventory; do not edit
the original record and claim its seal still verifies.

The proposed four-commit split is right: R6-004, R6-005, R6-006 including v2,
then R6-007 including its historical limitations and review. Each should include
its own source locks, retained captures, reports and closeout records. Complete
the R6-007 reporting/audit repairs before its commit. Executing fixes require a
new policy and controlled runs; they should not be folded back into pilot-v1.

## Cohort decisions

Endorse a census of the pinned file, and **both deterministic recovery and
learned witness proposal independently on every admitted obligation**. This
allows paired comparison and a declared deterministic-first hybrid calculation
without selecting learned trials only where deterministic search happened to
fail. Preserve different policy costs and the shared certificate/replay success
predicate; do not equate a native `omega` closure with certificate recovery.

`Bracket.lean@c07e03c94884e9084ffaf7a7294fc0907672f6c2` is byte-identical to
the frozen D1 pristine file and has exactly **15 textual `omega` occurrences**,
manually inspected as tactic sites: lines 69, 70, 71, 78, 96, 98, 99, 101, 158,
166, 170, 175, 178, 180 and 204. This is an extraction candidate census,
not 15 admitted or independent mathematical problems. Inline subproofs and
goals reached after `simp` need extraction at their actual local state.

Freeze all 15 candidate IDs and eligibility rules before either measured arm.
Record every extraction failure and unsupported fragment. Do not admit tasks
only because a deterministic witness was found. Mark D1/70 as a development
control already seen in live work; it is not a fresh held-out observation.
If it remains in an exploratory census table, report that stratum separately.
The remaining at-most-14 sites share containing declarations and assumptions,
so avoid treating them as independent reliability trials. Keep the frozen
dropped-hypothesis/IR-satisfiable criterion as a separate admission diagnostic.
Apply the criterion independently of both search outcomes. Freeze the protocol
and repair the guards above before executing the cohort.

## Review artifacts and reproduction

- [Fresh original recount](R6-007-REVIEW-RECOUNT.json) and
  [17-control replay](R6-007-REVIEW-CONTROLS.json).
- [Adversarial results](R6-007-REVIEW-PROBES.json), produced by
  [pilot_review_probes.py](pilot_review_probes.py): 12 accepted corruptions,
  the shared-ledger negative control, two fresh-ledger admissions, and
  independently differing authorization checks. `checkpoint_approved: false`
  travels with the data.
- [Fresh native replay](R6-007-REVIEW-REPLAY.json), with reports, commands,
  binary digests and [replay program](pilot_review_replay.py).
- [Exact-recovery diagnostic](R6-007-REVIEW-EXACT.json), with build/run commands,
  library/archive/executable hashes and [OCaml source](pilot_exact_probe.ml).
- [Source, retention and census check](R6-007-REVIEW-INVENTORY.json),
  [program](pilot_review_inventory.py), and
  [review-start inventory](R6-007-REVIEW-BEFORE.json).

Use fresh output paths. These commands do not invoke a provider or access the
operator credential:

```bash
python3 -B experiments/r6/reviews/2026-09-13/pilot_review_probes.py --output /tmp/r6-007-new-probes.json
python3 -B experiments/r6/reviews/2026-09-13/pilot_review_replay.py --output-dir /tmp/r6-007-new-replay
python3 -B experiments/r6/reviews/2026-09-13/pilot_review_inventory.py \
  --before experiments/r6/reviews/2026-09-13/R6-007-REVIEW-BEFORE.json \
  --verinf-repo /path/to/VerInf --output /tmp/r6-007-new-inventory.json
```

The replay needs permission to create the isolated checker namespaces. On this
host the outer sandbox blocked that operation; the authorized rerun succeeded
inside the intended `bwrap` isolation. The 17-control replay similarly needed
an authorized rerun because the outer sandbox blocked `ldd` during command
construction. The probe/inventory commands use the current original artifact
trees and local scan report; they are review reproductions, not a portable
replacement for the missing retained-only pilot auditor.
