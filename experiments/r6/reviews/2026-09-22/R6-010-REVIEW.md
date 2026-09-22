# R6-010 review at 51dd7ab

The original fifteen captures and their retained replay evidence hold up. Keep all fifteen sites in the primary operational census, including line 70 and both symmetric branches. Close the artifact-audit gap and qualify the exposure metadata before executing either arm. The population decision is recorded now in [R6-010-MEMBERSHIP-REVIEW.json](R6-010-MEMBERSHIP-REVIEW.json), bound to the proposed membership, census and fifteen manifests; it does not authorize execution or spending.

1. **P2 — the census controls do not establish that the admitted export and expected types agree with the replay evidence.** [test_census.py](../../test_census.py), lines 111–138, checks supplied manifest hashes and matching metadata, but never decompresses the challenge to derive `expected.challenge_sha256`, never derives the expected type digests from the raw replay reports, and does not require the exact artifact-key population. The raw freeze reports are not inputs to those checks.

   Three independent, coherently rebound copies pass all eleven non-native production controls: substitute line 99's challenge export for line 69's and update its compressed-file hash; set line 69's expected local type and matching census-result type to 64 zeroes; or replace the required `challenge.ndjson.gz` binding with `context/../expected.json`, maintaining the schema's four-property minimum. Each copy passes before mutation; outer membership/census/manifest hashes are updated afterward. The native exclusion control is explicitly skipped in these probes, never counted as passed.

   Add a non-locked historical census auditor before driver integration. Require exact populations and canonical artifact paths; recompute decompressed challenge and family-baseline digests; normalize the raw replay type representations and compare complete targets, axioms, policies and admission results; bind capture contexts, instrumented source/helper bytes and successful stage records to the retained freeze. Carry the three probes into an exact-name-gated audit suite. The existing bytes satisfy the joins I checked independently; this is a missing rejection boundary, not evidence that the original census contains a wrong theorem. The repairs need not change the frozen helper or rerun all fifteen captures.

2. **P2 — exposure needs to distinguish prior targets, prior input formulas, and generated answers.** [census.py](../../census.py), lines 31–34, correctly identifies line 70 as the only prior target, but its broader `model-visible` wording is too strong. Both retained outbound D1 requests contain `hzsum` with row `x_atom + z_atom - 2*Zmax - 16777215 ≤ 0`. The corresponding captured hypothesis type equals line 69's target exactly: `x.val + z.val < 2 ^ 24 + 2 * Zmax`. Thus line 69 was exposed as a premise under the IR projection, although it was not extracted or submitted as its own target. This does not establish contamination or proof leakage.

   The deterministic first-hit witness was not supplied in either request. The pilot returned `hwidth + 32769*neg_goal`; the later live run returned `2*hZ + neg_goal`. Describe these as generated responses, not exposure to a provided reference witness. The retained system message contains only a response-schema template, not a numeric witness example. [The recount](R6-010-REVIEW-RECOUNT.json) records both outbound/request hashes, the `hzsum` row and returned witnesses. Preserve the frozen records and attach an exposure addendum that the next protocol actually consumes; `exposed: false` must mean only no recorded prior use as a target, not unseen mathematics or an uncontaminated task.

The helper difference also needs a narrower description and control. Besides the signature and two identities, `CaptureSite.lean` adds a two-line anonymous/existing-name guard. That is a reasonable change. The current `capture_helper_differs_only_by_parameterization` control constrains removed lines and checks for three expected additions, but leaves other added logic unrestricted. An exact transformation check should permit the documented name guard and comment changes and reject other additions. No harmful added logic was found in the actual helper. Likewise, `forms_classified_exactly_once` implements first-match precedence, not uniqueness of regex matches; the report's first-match description is accurate.

Fresh verification:

| Check | Result |
| --- | --- |
| Upstream source | Git blob at VerInf `c07e03c9…` equals both pristine copies, SHA-256 `03b4d5ca…` |
| Census | 15 distinct spans, four families, seven first-match forms |
| Full production controls | 12/12, including the native task-build collision exclusion |
| Retained replay population | Exactly 34 raw reports; all normalized reports agree, 15 require the local-proof binding |
| Retained process records | 87 successful exits |
| Frozen challenge exports | All 15 decompressed digests match expected/census records |
| Expected types, axioms and baselines | Match retained raw replay reports and family baselines |
| Capture inputs and contexts | All instrumented sources, helpers and context copies agree with the frozen artifacts |
| Line 70 equivalence | Full context modulo the two identity fields; local type `26b1db6f…`; matching whole type and axioms |
| Census source lock | `e2a33824064d742af943ba8b1cf402c7758fe7fea2df364f0589b635906af52c` verifies |
| Review-start preservation | 43,397 files, zero changed or missing, excluding `.cache` and `__pycache__` |

The recorded per-site freeze times sum to 181.6 seconds; these include orchestration around the sandbox calls. The four-freeze determinism claim cannot be independently re-derived from only the final retained freeze. Keep it explicitly as a construction-time observation unless earlier digest records are retained.

The membership decision is to retain the exhaustive population, not select a more favorable subset. Report every site and each of the four families. Keep line 70 as a prior-target stratum, line 69 as a prior-premise-formula stratum, and flag the whole `lift_cell` family as related to the pilot. Predeclare sensitivity summaries excluding line 70 (14 sites) and excluding the pilot family (11 sites). Neither subset deserves an uncontaminated-data claim. Treat the symmetric pairs as 96↔99 and 98↔101; 96/98 and 99/101 are the two branches. Keep both branches in the population and avoid presenting their sites or repeated draws as independent mathematical samples. Four families are clustering units, not a guarantee of independence or repository-level representativeness.

`False` at 98/101 is the intended refutation goal after `by_contra`, not itself a benchmark defect. Before learned calls, classify whether each site is representable by the frozen IR and certificate/reconstruction path. Preserve the fifteen-site denominator and distinguish unsupported theory or dropped hypotheses from model failure; do not filter the population according to deterministic success. Prior live samples remain exploratory history and must not be pooled with the new cohort draws.

Evidence: [fresh controls](R6-010-REVIEW-CONTROLS.json), [corruption probes](R6-010-REVIEW-PROBES.json) and [their program](census_review_probes.py), [independent recount](R6-010-REVIEW-RECOUNT.json) and [its program](census_review_recount.py). The first restricted control invocation stopped before the expected task-build output; the approved native rerun completed all twelve controls. Review scratch records are under `/tmp/r6-010-review-9o6gyrbl`.

Scope: the full control suite built/reused the trusted exporter/checker and ran its native exclusion, but I did not rerun the fifteen successful captures or the 34 kernel replays. Their retained observations were checked, including type normalization and export hashes. No model call, real credential read, policy signing, commit or push occurred. Only new non-locked review files were added. Keep membership as the fixed design decision above; finish the census auditor and exposure addendum before the next arm executes.
