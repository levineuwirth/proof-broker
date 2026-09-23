# R6-014 revision 3 review at 75c12d25

The six repair paths hold under the checks below. Two P2 issues remain in the unlocked auditors, so the checkpoint is not yet approved for signing or the live-evaluation freeze. Both can be repaired without changing the locked cohort/analysis sources or rerunning native episodes.

1. **P2 — The deterministic artifact audit now requires an unretained export file.**

   Location: `reviews/2026-09-23/deterministic_audit.py:343–346`.

   The new solution join requires `stages/export/export.stdout` to exist and equal the retained decompressed solution. That stdout is Git-ignored and appears only in `seal.json.ephemeral_sha256`; its bytes are not part of the committed evidence. `solution.ndjson.gz` does retain the bytes, and the seal retains the stdout digest.

   The full local copy passes **539 cases**. Moving just l070's ephemeral stdout aside, leaving every retained artifact and every digest unchanged, makes the audit reject at `site_cvc4_term_mode_v1/bracket-l070:proof:solution_bound`. This is also the state a clean checkout has for that file (`git ls-files` returns no entry).

   Bind the retained decompressed solution to the recorded export stdout digest and output size regardless of whether the ephemeral file survives. When stdout is present, also compare its bytes; when absent, explicitly report that availability qualification. Preserve the current rejection of another site's substituted solution. Add a retained-only positive and a substituted-solution negative under that same retained-only condition, rather than requiring a native export to recreate already-retained bytes.

2. **P2 — Scan inventory paths can escape the declared root before the auditor reads them.**

   Location: `reviews/2026-09-23/cohort_v9_audit.py:1994–1999` (`streams_from_bytes`).

   The bytes-based stream check fixes the gzip issue, but `scan_root / entry['path']` accepts absolute paths and parent traversal. The auditor then opens that path without checking containment or the scanner's relative-path contract.

   On two separate temporary fixture copies/report mutations, I added one clean inventory entry for an inert sentinel outside the declared scan root: first by its absolute path, then by `../outside-scan.txt`. Its digest and size were authentic and the file count was updated. **Both audits accepted all 550 cases.** A read hook confirmed that the auditor actually read the outside file. No real credential or other sensitive file was used.

   Reject absolute, non-normalized and parent-traversing entry paths before opening them. Enforce containment and the scanner's symlink policy too, so a relative spelling cannot escape through a symlink. Controls should assert rejection *and zero reads of the outside sentinel*, separately for each escape form. A read-only audit still needs to honor its declared input boundary.

The repaired behavior that was re-exercised:

- **Progress floor:** the prior same-activation rollback probe now rejects with `cohort_ledger_rolled_back`. Independent fault injection after a durable reservation append but before its floor update recovers the floor from 1 to 2 through `find_open`. The analogous interruption after the terminal append recovers it from 2 to 3 through `find_terminal`, retaining one consumed transmission and no open reservation. These are isolated synthetic-authority operations, not network transmissions.
- **Scan coverage:** the compressed `.bin`, changed non-run file and miscounted gzip total now reject at `operator_scan:report_bound`; the compressed control establishes two gzip disclosures and zero raw disclosures first.
- **Declaration map:** the prior family relabeling is rejected; all **19 analysis controls** pass freshly.
- **Deterministic evidence:** the fresh baseline passes **539 cases**. The zeroed local type, zero witness on a refused run, wrong refused closer, altered verification certificate, nonempty search workload and substituted l069 solution all reject at their expected checks.
- **Case population:** the deterministic auditor now gates its full expected case set.
- **Cohort audits:** the public rehearsal audit passes **665 cases**, and the regenerated live fixture passes **550 cases**.

One control qualification, not another implementation finding: `refused_zero_witness_resealed` currently fails for two reasons at `search:observations_bound`: stale nested `certificate_bound.before/after` fields and the independently rejected arithmetic. The checker demonstrably runs, but the rejection control alone does not isolate its necessity. Rebind those nested certificate copies too for a standing control whose only failure is the certificate check.

Independent recount:

- Cohort v9, deterministic and analysis v3 source locks recompute, with zero mismatches.
- Recorded control populations match their source declarations: **48** cohort, **19** analysis, **32** deterministic-audit, **101** rehearsal-audit and **47** live records (baseline, 44 mutations, two acceptance probes).
- All 57 episode trees rehash cleanly: **1,786 event hashes / 8,818 sealed entries**, across 16 cohort, 30 deterministic and 11 fixture episodes.
- The full recorded 48/32/101/47 control suites were not all re-executed. This review ran the public baselines, analysis suite, targeted historical mutations and new probes.

The audits invoke cached builds and the independent certificate checker; no native proof episode or kernel replay was rerun. CVC4 dependency inspection required approved escalation after the sandbox blocked `ldd`. Production remains disabled with no checkpoint, activation receipt, progress floor or live ledger. No real credential was read or provider contacted. Only uncommitted review files were added.

Reproduction, using fresh output paths:

```sh
python3 -B experiments/r6/reviews/2026-09-23/r6_014_v3_review_probes.py repairs --output /tmp/r6-014-v3-repairs-new.json
python3 -B experiments/r6/reviews/2026-09-23/r6_014_v3_review_probes.py floor_recovery --output /tmp/r6-014-v3-floor-new.json
python3 -B experiments/r6/reviews/2026-09-23/r6_014_v3_review_probes.py deterministic --output /tmp/r6-014-v3-det-new.json
python3 -B experiments/r6/reviews/2026-09-23/r6_014_v3_review_probes.py live --output /tmp/r6-014-v3-live-new.json
python3 -B experiments/r6/reviews/2026-09-23/r6_014_v3_review_probes.py coverage --output /tmp/r6-014-v3-coverage-new.json
python3 -B experiments/r6/reviews/2026-09-23/r6_014_v3_review_recount.py --output /tmp/r6-014-v3-recount-new.json
```

Results are retained beside this review as `R6-014-V3-REVIEW-*.json`. The authority probes use the retained pricing capture at an explicitly supplied historical admissible time, as the canned controls do. The stated limitation about jointly restoring both the ledger and its floor is appropriate for this local-file design; no external rollback witness was assumed or tested.
