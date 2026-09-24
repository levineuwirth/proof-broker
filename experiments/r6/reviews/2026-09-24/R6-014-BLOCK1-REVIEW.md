# R6-014 block 1 — independent review

Reviewed `db20792e` on 2026-09-24. **The accepted block and frozen analysis reproduce. No acceptance-blocking finding.** No further collection is authorized by this review.

Fresh executions of both evaluation-lock verifiers pass: v2 verifies 69 files at `96ce9f6dd09a1cbd38be19ad133755e92a6c1e09d169a9db294c8302f180e26e`; v1 verifies 64 files. Git records v2 at `482bc5a9`, before the accepted audit and analysis records at `db20792e`. All changes since the collected-evidence commit `6a361a3e` are additions; its tracked evidence remains unchanged.

I reran the amended public auditor against `cohort-live-v9` with the retained bound operator scan. Its full result equals the committed accepted audit, including the exact 550-case fixture population. Its emitted analysis input equals the committed input. I then ran the locked analysis v3 on that fresh input and the signed policy: its full result also equals the committed analysis.

An additional recount verifies 510 event hashes and 3,130 retained sealed entries across all eleven runs, with no mismatches. The retained scan has 101,646 inventory entries and no disclosures; the auditor binds its receipts to all eleven runs. I did not rerun the credential-bearing scanner or compare a second report from the home directory.

The reported stage separation is reproduced: 11 returned witnesses, 10 verified certificates, 6 consumed and kernel-validated proofs, 4 verified certificates refused by the declared closer limitation, and l170 rejected by the verifier. Denominators remain 15/11/10/1/6/4. The whole-proof sensitivity counts are 5 without l070 and 2 without lift_cell. There is no integrity stop or operational pause. The cost arithmetic independently agrees: `13,560 × 2,500 + 5,478 × 15,000 = 116,070,000` nano-USD, or 116,070 micro-USD; the reservation is `11 × 102,400 = 1,126,400` micro-USD. This is provider-reported usage at frozen rates, not a bill.

The two additional end-to-end proofs relative to the deterministic arm are l096/l099, where that arm never invoked its backend. This supports the observed comparison of the two complete routes; it does not establish that the deterministic solver could not find those witnesses. Witness differences remain relative to the classification certificates, not a full deterministic witness set. All conclusions retain the single-block and post-collection-amendment qualifications.

One minor metadata correction: v2's lock `scope` and `live_evaluation_lock_v2.record()` inherit the phrase “before any signature.” For v2, the correct sequence is after collection and amendment approval, before the amended audit. The report and module introduction already state that chronology correctly. Record an erratum alongside the preserved lock; do not rewrite its bytes or imply that this changes acceptance.

The untracked root file `subprocess` is a 13,314,116-byte PostScript image. Its header identifies ImageMagick, creation time `2026-09-24T10:34:34+00:00`, and dimensions 1916 × 1143. `/usr/bin/import` resolves to ImageMagick's `magick` executable. An accidental Python line `import subprocess` executed by a shell is a plausible explanation for that filename and format, but I found no exact matching command in `.bash_history` and cannot attribute its creation. I read the header and computed its digest, but did not render, execute, alter or delete it. It was already present when the amendment review began.

Evidence: `R6-014-BLOCK1-REVIEW-CHECKS.json`; fresh public outputs are retained as `R6-014-BLOCK1-REVIEW-{AUDIT,INPUT,ANALYSIS}.json`. Verification invoked cached builds and certificate checks, with no new native episode, kernel replay, provider call or real credential read.
