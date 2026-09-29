# R6-014 Amendment 2 review

Reviewed commits: `557f1556` (synthetic fixture), `536f66c8` (amendment).
Decision: changes requested. Do not freeze live-evaluation-v3 or resume collection on this revision.

This review uses synthetic evidence only. No collected release was inspected, no credential was read, and no authorization, reservation,
pricing revision or transmission was performed. The runner's sender and ledger were mocked for restart probes. Transport probes use the
amendment's fixture generator and production ledger on temporary synthetic copies. Cached checker/exporter builds run through the auditor;
no native episode or proof replay was launched by this review.

## P1 — contradictory send evidence is accepted as a retryable release

Locations: `reviews/2026-09-28/cohort_v9_audit_amended_2.py:1420` and `reviews/2026-09-24/run_block2.py:234`.

Both predicates check the started counters, but omit the returned counters and the timestamps that independently report passage through
the handoff. Starting from the unmodified synthetic source, change just one HTTP field and regenerate the entire fixture with the unchanged
generator, including the production ledger, receipts, seals and operator scan:

| Source mutation | Ledger disposition | Complete auditor | Runner gate |
|---|---|---|---|
| `body_sends_returned = 1` | release | accepts, 639 cases | retry, no reasons |
| `header_send_at_ns = 12345` | release | accepts, 639 cases | retry, no reasons |
| `tls_verified_at_ns = 12345` | release | accepts, 639 cases | retry, no reasons |

The sender increments the returned-body counter only after `conn.send(body)` returns. It records header-send time immediately before
`endheaders`, and TLS-verification time after verification. These fields contradict the asserted connection-phase failure, even though the
other fields continue to say nothing started. This is not evidence that any real transmission escaped accounting; it demonstrates that
contradictory retained evidence currently authorizes retry and passes final audit.

Require the complete pre-grant state in both predicates: all send counters zero, handoff milestones absent where this path cannot have
reached them, and no other evidence of sending or response. Missing or malformed required fields should reject rather than become zero or
absence. Add separate, coherently regenerated controls for each relationship, including both returned counters. Do not infer consistency
from the ledger's release: its classifier also uses the started counters, so it is not an independent check on these contradictions.

## P2 — restart does not check the complete existing attempt population before launch

Location: `reviews/2026-09-24/run_block2.py:315`.

The loop discovers attempts only while the previous gate returns `retry`. Once a sent attempt returns `continue`, it breaks to the next
slot without inventorying later attempt directories. It can also launch a missing earlier directory before inspecting later existing ones.
This differs from the amendment's stated rule that every existing attempt is gated before anything launches, and from the auditor's
explicit attempt-population checks.

Independent restart probes use the same consistent synthetic release plus successful retry as the positive baseline:

| Population | Directories gated before sender invocation | Mock sender invoked for |
|---|---|---|
| Unmodified release + sent retry | first attempt, attempt2 | next site (positive baseline) |
| Add `l096-draw2-attempt3`, copied from the sent retry | first attempt, attempt2; extra attempt ignored | next site |
| Remove first attempt, leave attempt2 and its consumed ledger state | none | missing first attempt |
| Keep the valid pair, put an incomplete existing run later in schedule with a gap before it | valid pair only | the gap, before checking the bad run |

The second probe is the direct new retry-population gap: the auditor rejects a second sent attempt, but the runner silently skips its
directory and proceeds. The missing-first-attempt probe only establishes that the runner invokes the sender; the production ledger may
refuse that already-consumed slot. No real send is claimed for any probe.

Inventory and validate the existing block/attempt population before invoking any sender. Require canonical contiguous names, no attempts
after a sent attempt, the frozen attempt bound, agreement with authoritative slot history, and a gate decision for every existing attempt.
Only after that preflight should collection advance to the next eligible missing attempt. Add controls with a valid completed retry plus
an extra attempt, a missing predecessor, and a later invalid existing run, asserting zero sender invocations.

## Verification and qualifications

- The full supplied synthetic audit suite passed: 13 release-section records, 9 shared-directory controls and 51 carried-forward live
  records. Its unmodified release fixture accepts at 639 cases, and its isolated 550-case population matches the frozen record.
- All 122 fresh/restart expected decisions from the supplied runner controls were reproduced on copies, without running their production-ledger
  block-1 baseline pass. The independent probes above expose cases outside that population.
- Each contradictory transport probe was audited after full synthetic regeneration and evaluated by the actual runner gate against that
  fixture's ledger. The successful unmutated regeneration is also in the supplied audit suite.
- The amendment diff leaves the rehearsal path unchanged. Nonzero-exit rejection at the earlier stage check is valid evidence of overall
  rejection; it is not isolated coverage of the duplicate exit-code test in `live_release`.
- The runner control called `release_exhausted_pauses` lowers the mocked attempt limit to one and tests the first release. It exercises
  exhaustion comparison, but is not a native or fixture-backed third-release path. The auditor's three/four-attempt probe is explicitly a
  direct predicate test. Keep those scopes distinct in the report.

Reproducer and output: `amendment_2_review_probes.py`, `R6-014-AMENDMENT-2-REVIEW-PROBES.json`.
The supplied full synthetic audit-suite rerun is recorded separately as `R6-014-AMENDMENT-2-REVIEW-CONTROLS.json`.
