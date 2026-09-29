# R6-014 amendment 2, revision 2

This responds to [R6-014-AMENDMENT-2-REVIEW.md](R6-014-AMENDMENT-2-REVIEW.md), which reviewed `557f1556` and `536f66c8` and requested
changes: P1 (contradictory send evidence permits retry) and P2 (restart skips existing attempts).

The auditor is revised in place as amendment 2, revision 2. The runner is at revision 7. Revision 1's records are retained unchanged.
Nothing has been authorized, reserved or sent. No collected run or credential was read.

## P1: the complete pre-grant state

Both the auditor (`live_release`) and the runner's gate now require `pre_grant_state`. The predicate is the same in both places and is
derived from `cohort_https`:
- **The initial record.** Every field that `execute` initializes and `handoff` would change must be present, with its initial value and
  type:
  - both started and both returned counters;
  - TLS, and the TLS-verification, header-send and grant milestones;
  - the grant fields and the grant-write flag;
  - the outbound body digest and the response fields;
  - retries, redirects, the send outcome and the failure codes.
  A missing or malformed field fails. Nothing defaults to zero or absence, and a boolean is not a counter.
- **One connection attempt.** The four milestones before `handoff` (permit, pricing, credential read, connection start) must be integers
  in that order.
- **The verification code** is set exactly when the failure is a certificate failure.
- **No outbound-body or provider-response file.**

The ledger's release is not taken as evidence of any of this.

One consequence: a connection-phase category with a verified TLS session and no grant is reachable only through a local record-write
failure after verification. It now pauses the runner and fails the audit. It is not retried.

## P2: the existing population before any sender

`preflight` runs before the first launch. It requires, in order:
1. every entry in the run directory is a directory with a canonical name: block 1's draw-1 runs, or `<site>-draw<d>[-attempt<k≥2>]` for a
   block 2 slot;
2. the slots with runs form a prefix of the schedule;
3. the ledger holds exactly these block 2 slots, with nothing open;
4. each slot's attempts are 1..n, within the pre-send limit;
5. every attempt is gated in order: each but the last must decide `retry`, and only the last slot may await one;
6. each slot's ledger reservations, releases and consumption agree with its attempts and decisions.

Collection then resumes at the next missing attempt. A run directory that appears after the preflight pauses.

## Controls

All are synthetic.

**Auditor** ([R6-014-AMENDMENT-2-V2-AUDIT-CONTROLS.json](R6-014-AMENDMENT-2-V2-AUDIT-CONTROLS.json)):
- **Revision 1's population:** every record has the same outcome.
- **27 new regenerated controls,** one per pre-grant field or file, each contradicted alone. Each is applied to the release's source, and
  the whole fixture is regenerated with the unchanged generator and the production ledger. The ledger reconciles every one as a release.
  - 23 are rejected at `l096-draw2:failure:classified_and_finalized`. These include the review's three: `body_sends_returned`,
    `header_send_at_ns` and `tls_verified_at_ns`.
  - 4 are rejected first by shared checks:
    - `retries` and `redirects_followed`, at `transport:record_consistent`;
    - `send_outcome`, at `grant:consistent_with_outcome`;
    - an outbound-body file, at `transport:bodies_are_the_contract_rendering`.
- **A direct probe of `pre_grant_state`:** the predicate alone rejects all 27, including those four, and passes the unmodified record.

**Runner** ([R6-014-BLOCK2-RUNNER-V7-CONTROLS.json](R6-014-BLOCK2-RUNNER-V7-CONTROLS.json)):
- **88 cases, fresh and on restart: 176 records.** Revision 6's 122 records keep their decisions, launches and reasons. Each of the 27
  pre-grant cases pauses on the pre-grant reason and nothing else.
- **16 restart populations,** each asserting its sender invocations and its stop reason:
  - **resuming:** a release awaiting its retry resumes at attempt 2; a completed retry resumes at the next slot, also with block 1's runs
    beside it;
  - **pausing before any launch:** an attempt after a sent attempt, a missing first attempt, a gap before a later run, a stray file, two
    non-canonical names, a ledger slot without its run, a run without its ledger slot, attempts beyond the limit, a released slot followed
    by a later slot, a reservation count that disagrees, an open reservation;
  - **a later invalid run:** gated, then paused at that run.
- The mocked ledger now holds no block 2 slot before the first launch, and holds the case's slot, with its reservation count, afterwards.

**The review's own probes** ([R6-014-AMENDMENT-2-V2-REVIEWER-PROBES.json](R6-014-AMENDMENT-2-V2-REVIEWER-PROBES.json),
[`amendment_2_reviewer_probes_recorded.py`](amendment_2_reviewer_probes_recorded.py)), reproduced:
- the restart baseline gates both attempts and launches only the next site;
- the extra attempt, the gap before the retry and the later bad run all stop before any sender invocation;
- the three transport contradictions are rejected by the auditor and paused by the gate on the pre-grant reason.

**Fixture:** unchanged. It is accepted with the same 639 cases, and the analysis input and analysis are identical to revision 1's
([audit](R6-014-AMENDMENT-2-V2-RELEASE-FIXTURE-AUDIT.json), [analysis](R6-014-AMENDMENT-2-V2-RELEASE-FIXTURE-ANALYSIS.json)).

## Scopes, as the review asked

- **`release_exhausted_pauses`** lowers the mocked limit to 1 and tests the first release. It exercises the exhaustion comparison. It is
  not a fixture-backed third release.
- **The auditor's three- and four-attempt test** is a direct probe of `slot_attempts_ok`. The sources hold one release, so no fixture
  reaches a fourth attempt.
- **Non-zero exit:** its rejection comes from the shared stage-receipt check. It is not isolated coverage of the exit-code test inside
  `live_release`.
