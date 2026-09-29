# R6-004 revision 3 review — finish the outer provenance bindings

Reviewed on 2026-09-09. The three submitted corrections hold, including the
independent v2 reconstruction-context reproduction. The gate-suite split is
accepted. One part of the complete-checkpoint contract remains unfinished:
the outer gate accepts contradictory checkpoint/native provenance and an empty
preservation inventory. Keep the pre-live requirement open until those
comparisons are added.

The submitted artifacts themselves agree under independent recomputation.
These findings concern what the outer audit fails to reject, not an invalid
Lean proof or a disclosure in a publication-accepted episode.

Evidence: [review record](R6-004-V3-REVIEW.json),
[fresh regression results](R6-004-V3-REGRESSIONS.json),
[independent probe results](R6-004-V3-PROBES.json), and
[probe program](r6_004_v3_review_probes.py).

## What reproduces

- The checkpoint binds all **67 recorded checks**, in exact 26 / 5 / 30 / 6
  populations, with matching hashes/counts, no duplicates and every check
  explicitly `passed: true`.
- All **62 non-native controls** pass again on disposable copies: 26 focused,
  30 artifact audits and six checkpoint gates. This includes twelve historical
  audits. The five native episodes and Lean replay were not rerun.
- Independent recomputation confirms **111 event hashes**, **685 sealed
  entries**, and the reported five episode predicates. The public recount
  returns 67 checks, 13 bundle roots, five canaries, two expected overlapping
  synthetic findings, no unexpected findings and none in publication-accepted
  episodes. Before this review added files, it scanned 744 files.
- The **9,986 prior files** match both the current tree and independently read
  `ac0f50f` Git objects, including the exact path population. The first review's
  719 v1 checkpoint/policy paths and the v2 review's 717 checkpoint paths are
  unchanged.
- V3 retention excluding `final-checks.json` is exactly **701 files,
  8,598,395 apparent bytes, 247 distinct contents and 4,821,969 unique bytes**.

## The three corrections are effective

The prior review's context probe, with only its input checkpoint changed to
v3, now rejects with `reconstruction context differs from the frozen
obligation`. It still rewrites the captured target to `False` and recomputes
the receipt, scan and seal. No stale hash is the detector.

The six gate controls pass again, including the deleted frozen check,
substituted native case and incomplete status. Keeping `publication_gate`
independent of suite completion avoids the former `finalize_copy` workaround.
The public entry point composes `recount` with `gate_suite`. Four additional
probes confirm that `gate_suite` rejects a missing record, a deleted case with
updated count/hash, a failed suite and a missing passing-baseline precondition.
There is no need to make the probes validate their own unfinished results.

The independent canary-named symlink reproduction now rejects publication and
records a null name with the correct digest. Its diagnostic JSON contains no
canary. The focused unreadable-file/directory controls actually exercised the
permission failures in this review; neither was skipped by a privileged reader.

## Remaining finding: the complete gate leaves provenance claims unbound

Locations: [credential_final_checks.py](credential_final_checks.py),
`case_contract` lines 54–91 and `recount` lines 154–190.

The full public command, including `gate_suite`, accepts all four mutations
below with exit code 0, `passed: true` and `total_checks: 67`. The program first
establishes a passing unmodified copy and restores original bytes between
mutations. None changes an episode's proof, certificate or seal.

| Mutation | Missing relationship |
| --- | --- |
| Replace `checkpoint.json`'s `policy_sha256` and `source_lock_sha256` with false digests | The gate computes the current hashes for its output but never compares them with the checkpoint's declarations |
| Replace the native suite's `d1_valid.detail.seal_sha256` with zeroes and update the suite hash in the checkpoint | `case_contract` checks seal acceptance and four predicates, but never compares the native record's seal digest with the episode seal |
| Make that native record report zero scanned files, 999 disclosures, false `outer_log_clean`, and invalid coverage; update the suite hash | Those observations are ignored when cross-checking the native record, so it can contradict the independently audited episode |
| Replace `prior-artifacts.sha256.json` with `{}` | The gate accepts the supplied inventory as its population and vacuously reports preservation success with `prior_files_checked: 0`, while the preservation-suite record still says 9,986 |

The last case is an omission control for the preservation claim. The independent
recount in this review establishes that the original 9,986 files really are
unchanged; the submitted gate does not establish that its supplied inventory is
the original population.

Finish these comparisons together:

1. Bind checkpoint policy/source-lock declarations to the frozen files. Check
   the other machine-readable contract declarations against their authoritative
   configuration instead of silently replacing them in the recount output.
2. Bind each native-suite seal digest to its episode. Cross-check re-derivable
   scan/disclosure counts and log results as well as the four current
   predicates. Validate coverage fields without equating historical native
   coverage with a later retained-only re-audit: omitted build products must
   retain their existing, explicit `recorded_not_recomputed` qualification.
3. Verify the preservation inventory's exact membership and values against the
   pinned Git source, or an independently anchored digest of that complete
   inventory. A count check alone would still admit substitutions. Cross-check
   the preservation-suite record with the verified population and result.

These are outer recount/record-validation changes. They do not require another
native credential experiment if the frozen adapter, auditor, policy and their
dependencies remain untouched. Preserve v3's evidence; retain the corrected
gate source and fresh, exact-name-gated supplementary mutation results
separately. The existing non-native controls can run against the corrected
gate using copies of the v3 checkpoint.

From the repository root, reproduce this review against the submitted gate:

```bash
python3 -B experiments/r6/reviews/2026-09-09/r6_004_v3_review_probes.py /tmp/r6-004-v3-probes-new.json
```

The output records whether the public gate accepts the provenance mutations;
it is an observation program, not a passing regression assertion for those
mutations. Each fixed gate must reject them. The context, safe-path and
gate-record controls already assert their expected rejections.

## Small documentation corrections

`R6-004.md` still links the coverage declaration to `credential-http-v2.json`
and its two episode-audit reproduction commands still select v2 runs. The
current auditor is v3; those commands should select the v3 inputs. The recount
example's output filename also still says v2.

The scanner derives its target inventory independently, but the auditor does
consult recorded hashes/counts to compare them with its recomputation.
“Never trusted without comparison” describes that behavior more accurately
than “never consulted.” A repeat recount's inventory count can change when
files are added; it need not change on every invocation. The initial repeat
in this review also returned 744.

Only review artifacts were added. Submitted sources, policies, suites and
episode artifacts were preserved, and the live-policy requirement was not
marked satisfied. Nothing was committed or pushed.
