# R6-008 independent review — 2026-09-13

**Do not sign this revision. The recorded canned results reproduce, but the
executing allowance and publication boundaries still have gaps.** Keep the
separate rehearsal ledger. Its larger synthetic allowance is useful for
rehearsals; the missing property is enforced separation from live authority.

Reviewed policy: `d63a6680d591201b43332134be4f53c3a5a91ce683bb80b04ebc4d6739188e0b`.
Reviewed source lock: `077aa0e1a82866d69ebaf71294a2338dfe78b6b9f8d96e2b6cfb38845d1309a2`.
The policy remains disabled and its live ledger does not exist. No operator
credential was read and no provider call was made. Local actors read synthetic
credential files and contacted loopback TLS fixtures. This review did not
repeat the three complete Lean episodes, rebuild the overlay, or execute new
kernel replays.

## What independently holds

| Population | Fresh result |
| --- | --- |
| R6-008 focused controls | 30 pass, exact names; initial sandbox attempt stopped at forbidden socket creation, then a fresh run with loopback permission passed. |
| R6-008 historical audit | 56 named cases pass. |
| R6-008 audit controls | 16 controls: 12 copy mutations, 3 predicate mutations, 1 accepted copy. All pass. |
| R6-007 auditor repairs | The 124-case baselines and 27 reported controls pass, including summary-only rejection of the three previously inventory-masked mutations and rejection of negative scan reports. |
| Rehearsal event chains | 19 / 17 / 50 events, 86 total; all hashes valid and terminal hashes match seals. |
| Rehearsal seals | 214 / 208 / 281 entries, 703 total; zero mismatches. |
| Frozen sources | `campaign_contract.verify_sources()` passes; all three retained campaign policies equal the disabled policy bytes. |
| Saved proof export | Decompressed hash `cd6081daac2fc64d718d28202d1742ff1e653e9862031fb19a5efeb7cd7d1812`; both recorded axiom deltas empty. This is saved-artifact verification, not another native replay. |
| Preservation | All 33,301 files in the review-start inventory remain unchanged. The population excludes `.cache` and `__pycache__` path components and is not a Git-selected retention count. |

These are distinct populations, not one combined conformance score. Records:
[focused](R6-008-REVIEW-FOCUSED.json), [audit](R6-008-REVIEW-AUDIT.json),
[audit controls](R6-008-REVIEW-AUDIT-CONTROLS.json),
[pilot controls](R6-008-REVIEW-PILOT-CONTROLS.json),
[recount](R6-008-REVIEW-RECOUNT.json),
[preservation](R6-008-REVIEW-PRESERVATION.json).

## Findings requiring action

1. **P1 — A used permit can authorize another sender; the grant is not single-use across the authorization.**

   [campaign_episode.py:159](../../campaign_episode.py#L159) saves the open
   ledger as `transport-ledger.ndjson`, mounts that copy at line 177, and
   allocates a grant directory inside the run at line 185.
   [verify_permit](../../campaign_ledger.py#L105) verifies those supplied bytes;
   it has no access to subsequent consumption in the authoritative ledger.

   The independent loopback control creates a one-transmission ledger,
   invokes the real actor once, reconciles the grant into that ledger, then
   invokes the actor again with the same permit and old snapshot but a fresh
   grant directory. **Both actors return HTTP 200 and each local receiver
   records one request.** The shared ledger says one transmission consumed;
   there have been two observed loopback requests. This is a reproduction at
   the actor boundary, not two ordinary `campaign_episode` invocations and
   not evidence of two provider calls.

   A separate concurrency probe also defeats a shared grant directory:
   [commit_grant](../../campaign_ledger.py#L124) checks absence before creating
   its temporary file, then uses overwriting `os.rename`. Two callers can
   both observe absence; after the first renames its temporary file, the
   second creates that temporary name and overwrites the committed grant.
   A controlled interleaving of the actual filesystem operations reproduces
   two successful grants, with only the second retained. The mocks control
   scheduling, not the return values of the filesystem writes.

   Consume a permit against authoritative authorization state, atomically and
   durably before the actor can send. A replayed snapshot or a fresh run
   directory must not provide a fresh grant slot. Grant publication must also
   resist concurrent acquisition; the current check-then-rename construction
   does not. Add independent stale-permit and concurrent-grant controls.

2. **P1 — Release does not establish sender termination.**

   [campaign_ledger.py:245](../../campaign_ledger.py#L245) tests only
   `process_record is not None`. Both an empty dictionary and a record with
   `workload_empty_after_cleanup: false` produce a release when the grant is
   absent and counters are zero. The corresponding positive control with
   confirmed cleanup also releases.

   This is reachable from the supervisor contract: `supervise.py` writes a
   process record even if cleanup leaves the workload populated, and
   `campaign_network.stage` correctly raises a supervisor failure for that
   condition. `invoke` catches it and calls this permissive reconciliation.

   Require validated evidence that the sender's entire workload terminated,
   including the relevant cleanup and monitor fields. Missing or contradictory
   termination evidence must keep the allowance consumed/held as unknown.
   A process-record filename or an exit code alone does not establish this.

3. **P1 — A rehearsal activation is accepted under live authorization.**

   The actor separately validates the policy authorization and the ledger,
   but [verify_permit](../../campaign_ledger.py#L105) takes its limits from
   the activation without comparing that activation's authorization with the
   policy's authorization. The ledger format also has no enforced live versus
   rehearsal authority discriminator.

   An in-process actor probe supplies a synthetic live policy authorizing one
   transmission and a ledger activated by `rehearsal` for 64 transmissions,
   both under the same policy digest. Live authorization, permit verification
   and pricing admission all pass. The probe deliberately stops at the
   credential-read boundary, with zero credential reads and zero connections.

   Keep the rehearsal ledger, but bind activation identity, purpose and all
   limits to the live authorization in both host and actor. A directory name
   is not this binding. Under a signed policy, a rehearsal ledger for those
   same policy bytes must still be inadmissible to live mode.

4. **P2 — Interrupted transport records bypass finalization.**

   [campaign_episode.reconcile](../../campaign_episode.py#L100) decodes
   `http.json` before reconciling the grant. A killed process can leave that
   file truncated because the actor rewrites it during execution.

   The probe drives production `execute`/`invoke` with a simulated stage
   termination after a grant is committed and while `http.json` contains
   only `{`. Setup, preparation and the stage launcher are test doubles;
   the driver, record reads and reconciliation path are production code.
   `JSONDecodeError` escapes: no terminal event, no seal, and the reservation
   remains open despite a retained grant. No network connection occurs.

   Reconcile durable grant state despite missing, malformed or unreadable
   observational records; preserve the record-read failure as evidence and
   finalize the episode. The current outcome fails closed on further spending,
   but fails the promised complete episode/uncertainty accounting contract.
   Add a production-path interruption control, not only a direct call to
   `finalize` with an already constructed summary.

5. **P1 — The operator scan does not bind its population or sealed bytes to `--bind-runs`.**

   [operator_disclosure_scan.py:38](operator_disclosure_scan.py#L38) computes
   a credential commitment and copies the seal's digest. Its success test at
   line 80 checks scan acceptance and commitment matches, without requiring
   that the bound runs were scanned or that their seals cover the observed
   bytes.

   Three separate controls first pass a sealed synthetic baseline, then:
   (a) change only the scan root to an empty directory; (b) remove only the
   seal; (c) change only the HTTP record after sealing while preserving its
   credential commitment. **All three still exit 0.** A combined consequence
   probe also leaves a synthetic credential disclosure in an unscanned,
   unsealed bound run and receives acceptance after scanning zero files. That
   combined probe is illustrative; the individual controls establish the
   separate missing comparisons. Credential reads are stubbed with a
   synthetic value; no operator credential is accessed.

   Enforce coverage of every bound run, verify its seal and the commitment
   record's membership/hash, and compare the scan inventory with those actual
   bytes. Preserve publication acceptance as a separate predicate. A matching
   commitment plus a seal digest is insufficient. Apply the existing report
   safety discipline to the augmented operator report as well.

6. **P2 — Campaign audit does not bind the source lock to the retained policy.**

   [campaign_audit.versions](campaign_audit.py#L111) checks the sources against
   the lock and the lock against `search-policy.json`, but omits
   `policy['source_lock_sha256'] == sha(lock_bytes)`.

   A copy mutation changes retained `campaign_ledger.py`, updates its retained
   lock entry and the search-policy lock digest, then performs normal
   finalization. The retained policy remains unchanged and still identifies
   the original lock. **All 56 cases pass.**

   Add that missing comparison and retain the earlier auditors' binding of
   imported checker/builder modules to their recorded source revisions.
   Agreement between freely updated mirrors is not a frozen policy binding.

7. **P2 — Campaign completion audit trusts publication claims and misses terminal commitments.**

   [campaign_audit.seal](campaign_audit.py#L191) checks a reported publication
   flag and the scan-file hash without checking the scan's acceptance. A
   scan changed to `accepted: false`, with chain and seal repaired, passes
   all 56 cases. A stronger control adds a real synthetic-canary disclosure
   and uses normal finalization, which correctly rejects it. Changing the
   terminal claims/event to success and resealing makes the auditor accept
   while the scan still records the disclosure and rejection.

   Independently, replacing only the terminal `summary_sha256` with zeros
   and repairing the chain/seal also passes. These are distinct missing
   comparisons, not one bundled test whose first rejection hides the rest.

   Recompute publication findings, coverage and acceptance using the frozen
   scanner, bind both scan reports and the summary to their terminal
   commitments, and derive the completion predicate. Add a control for each
   relationship. This finding concerns the auditor; the actual native scan
   reports checked in this review are clean.

## Reporting and implementation qualifications

- `grant_committed_at_ns` is assigned from a timestamp sampled **before**
  `commit_grant` writes and fsyncs. The reported 207,736 ns and 16,957,836 ns
  intervals are relative to grant-record creation, not observed durability
  completion. The source orders completion before header sending, but the
  artifact does not time that completion. Record both instants or narrow the
  timing claim.
- The grant path fsyncs its directory; ledger activation/head replacement do
  not. `_write_head` ends at `os.replace`. Include directory durability in
  the ledger lifecycle before describing it as durable across a host crash.
  This review did not simulate power loss.
- The exposed `freeze()` refuses when the disabled policy, lock or runtime
  already exists. Provide an explicit reviewed signing/activation procedure
  that preserves the disabled checkpoint instead of treating signing as an
  already exercised operation. This is a lifecycle gap, not authorization for
  this review to sign anything.

## Evidence and next checkpoint

[campaign_review_probes.py](campaign_review_probes.py) is outside every policy
source lock. Its [offline observations](R6-008-REVIEW-PROBES.json) and
[real loopback replay](R6-008-REVIEW-LOOPBACK.json) identify the exact review
program hash and the reviewed policy/lock. Copy mutations first pass the
unmodified audit; the grant concurrency probe uses controlled scheduling;
the interrupted-record and authorization probes use the explicit test doubles
described above. They are diagnostic reproductions, not native conformance
episodes or a capability measurement.

```bash
cd experiments/r6
python3 -B reviews/2026-09-13/campaign_review_probes.py --output <fresh path>
python3 -B reviews/2026-09-13/campaign_review_probes.py --loopback-replay --output <fresh path>
```

The second command requires local socket permission. Both refuse to overwrite
their output. Pricing-dependent probes require the captured sources still to
be within the policy's admission window; a later rerun must explicitly account
for that prerequisite.

Next: repair the authorization/grant/reconciliation state machine and the
publication bindings, add independent controls for these reproductions, then
freeze a new source lock and run new native rehearsals. Preserve R6-008 v1 and
its three runs. Repair the historical auditors under non-locked paths. Only
after that checkpoint passes should signing and a live transmission resume.
