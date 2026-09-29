# R6-014 revision 4 review

Reviewed `6e993510` on 2026-09-24. **Approved at the canned-checkpoint scope; no findings.** Both revision 3 findings are closed. This is not a signature or spending authorization.

The deterministic auditor binds the decompressed solution to the retained verdict and sealed stdout digest, output size and receipt, and declaration names. Optional stdout comparison adds evidence where available. The fresh baseline accepts 539 cases with 12 of 12 stdout files compared. On copies, removing every export stdout accepts; substituting another site's solution in that same retained-only state rejects at `proof:solution_bound`. The zero-witness mutation now updates the nested `certificate_bound` copies as well. I reran it and confirmed rejection at `search:observations_bound`; the recorded detail and source inspection isolate the re-executed checker as the remaining objection.

The scan inventory guard rejects absolute, parent-traversal, non-normalized and symlink paths before reading their bytes. I reran all four controls; the three escapes record zero sentinel reads. I also reran the hook precondition against `ac546085`: all three old-auditor probes accept and read the sentinel exactly once. This establishes that the zero-read controls exercise the repaired boundary.

Fresh public audits:

| Population | Accepted cases |
|---|---:|
| Cohort v9 rehearsals | 665 |
| Synthetic live fixture | 550 |
| Deterministic arm and reference | 539 |

The independent recount verifies 57 runs, 1,786 event hashes and 8,818 retained sealed entries, with no mismatches. Cohort v9, deterministic and analysis v3 source locks still verify. The diff since `335521a5` contains only the unlocked auditor/control changes and review/report records; no locked source, native run or fixture changed.

The retained control populations match their source-defined names: 101 rehearsal, 51 live and 34 deterministic. Their auditor/program digests match the current files. These full populations were recounted from the supplied records; this review reran the targeted repair controls rather than repeating every historical mutation. The unchanged locked suites remain 48/8/19. Recomputing frozen analysis from the fresh live audit reproduces its recorded input and result exactly: denominators 15/11/10/1/6/4, no integrity stop and no operational pause.

Evidence is retained in `R6-014-V4-REVIEW-CHECKS.json`, the three `REVIEW-{LIVE,REHEARSAL,DETERMINISTIC}.json` outputs, the two targeted-control logs and `REVIEW-OLD-HOOK.json`. `r6_014_v4_review_recount.py` reproduces the recount and analysis comparison. No native episode or kernel replay was rerun; the audits perform cached builds and independent certificate checks. The deterministic audit and its targeted controls needed an unsandboxed retry because sandboxed `ldd` could not inspect the pinned solver.

Production remains disabled, with no checkpoint, activation receipt, progress floor or live ledger. No real credential was read and no provider call was made. The live-evaluation lock can now be prepared from the reviewed sources. Concrete operator scope approval, a fresh admissible pricing capture and signing remain separate prerequisites; capture 3 has expired.
