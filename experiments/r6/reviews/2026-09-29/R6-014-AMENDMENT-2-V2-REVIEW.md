# R6-014 Amendment 2 revision 2 review

Commit reviewed: `8fc2cab8`. Decision: approved for the live-evaluation-v3 freeze, with no blocking findings.

Both findings in the first review are closed. This review uses synthetic copies and previously audited block-1 templates only. No collected
release or credential was read, no production ledger was opened for mutation, and nothing was frozen, signed, reserved or sent. This is
approval of the evaluation/runner revision, not an additional spending authorization or acceptance of the actual collected release.

## Release evidence

The release predicate requires the initial values and exact types of the send counters, handoff milestones, grant and response fields.
Missing fields do not become zero or null, and booleans do not count as integers. It also checks ordered pre-handoff milestones, one
connection attempt, the verification-code/category relationship, and the absence of outbound-body and provider-response files.

All three original single-field transport probes were freshly regenerated through the production fixture generator and ledger. Each still
reconciles as a release, but now rejects at `l096-draw2:failure:classified_and_finalized` and pauses the actual runner gate for the pre-grant
reason alone. The regenerated audit and runner results exactly match the committed reviewer-probe record.

The 27 direct predicate controls were rerun, including the four whose full audits reject earlier; the unmodified record passes and every
mutation fails. Additional independent tests remove or mistype each required predicate field, on both implementations.

Implementation qualification: these are two copies of the same predicate, not one imported implementation. Their function bodies match
structurally after excluding the docstrings, and `PRE_GRANT`, `REACHED` and `CONNECT_PHASE` agree exactly. The evaluation freeze should bind
both source files as planned; a future change should preserve or explicitly review their equivalence.

Verified TLS without a grant is correctly outside this amendment's admitted retry state: pause and audit rejection are appropriate. That
decision does not require attributing the underlying failure exclusively to a record write. The review confirms the phase restriction,
not an exhaustive diagnosis of every possible local exception.

## Restart population

`preflight` now inventories block-2 directories before any sender invocation. It validates names, schedule prefix, contiguous bounded
attempts, each existing attempt's gate result, and the corresponding ledger slot/reservation/release/consumption population. It rejects an
attempt after a sent attempt and a released slot followed by a later collected slot. Block 1 remains the separately audited history.

The original baseline freshly resumes at the next site. The extra attempt, missing predecessor and later bad population all freshly stop
with zero sender invocations. All 176 supplied fresh/restart cases and all 16 restart populations were independently rerun and match the
committed decisions, launches and reasons, normalizing only random temporary-directory names in diagnostics.

## Verification scope

- The fresh synthetic fixture audit accepts the exact 639-case population and reproduces the committed analysis input. The recorded
  analysis is byte-identical to revision 1's; the analysis program was not rerun in this review.
- The committed audit-control record binds the current auditor, its control program, amendment 1's auditor and the fixture descriptor by
  SHA-256, with the exact expected control names. It records 40 release-section records (the previous 13 plus 27 new negatives), nine
  shared-directory controls and 51 carried-forward live records. Previous outcomes are unchanged; the 27 new negatives split 23 at the
  new predicate and four at earlier checks.
- This review did **not** repeat the full hour-long regenerated audit-control suite. It verified that record's source bindings and
  populations, reran the original three regenerated transport probes, the direct predicate controls, the runner controls and the positive
  fixture audit. Cached checker/exporter builds occur through the auditor; no native episode or proof replay was run.
- The mocked-limit exhaustion test and direct three/four-attempt predicate test are now described at their actual scopes. The nonzero-exit
  case remains evidence of rejection at the earlier stage check, not isolated coverage of the duplicate release-condition test.

Evidence: `R6-014-AMENDMENT-2-V2-REVIEW-CHECKS.json`, `R6-014-AMENDMENT-2-V2-REVIEW-PROBES.json`, and
`amendment_2_v2_review_checks.py`. The regenerated probes use the committed `amendment_2_reviewer_probes_recorded.py` unchanged.

Next: freeze and verify live-evaluation-v3; ensure pricing is fresh through the established revision procedure; then the operator may
resume under the existing approved scope. The runner must evaluate the actual existing population and release before retrying. Any real
evidence mismatch still pauses and returns for review.
