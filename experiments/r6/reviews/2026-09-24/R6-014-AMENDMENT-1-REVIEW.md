# R6-014 amendment 1 — review

Reviewed `10c53c34` on 2026-09-24. **Approved as the documented post-collection directory-layout amendment. No findings.** This approval makes no claim about block 1's outcomes or integrity; the collected block was not audited and its analysis remains deferred.

The source diff is exactly the introductory documentation, `campaign_files`, and the replacement of the directory inventory/comparison statements. I independently compared the Python syntax trees after removing that helper and restoring those two statements: everything else matches the frozen auditor. The early rehearsal return is unchanged. The explicit expected set includes the differently named source lock; dot-delimited ownership rejects unexpected campaign files without treating `farkas-cohort-v90.json` as part of v9.

I reran the synthetic isolated baseline and all nine shared-directory controls. The baseline reproduces the frozen record's exact 550-case population. The shared directory and unrelated look-alike both accept with 550 cases. Missing floor/checkpoint, extra revision, policy-prefixed extra file, lock-prefixed extra file and altered retained revision reject at `revision:history_bound`; the altered activation receipt rejects at `ledger:continuous_across_revisions`.

I checked the supplied 51 live-control records against the original population and outcomes and verified their source digests. Those 51 controls were not independently rerun in this review. Neither the rehearsal audit nor its controls were rerun; the changed code is reached only in live mode.

The original evaluation lock verifies all 45 import-closure entries, 8 records and 12 reviewed sources. The commit diff from `6a361a3e` adds only the five amendment files: all pre-existing tracked blob identities are preserved, including the original lock, auditor, collection and rejection. The tracked working tree matches the reviewed commit. Preservation was checked through Git identities; no block outcome inspection was needed. The pre-existing untracked `subprocess` file was left untouched.

Evidence: `R6-014-AMENDMENT-1-REVIEW-CHECKS.json` and `R6-014-AMENDMENT-1-REVIEW-CONTROLS.log`. The latter is the fresh synthetic control run, with its digest recorded in the former. No native episode, credential read, provider call or collection analysis was performed.

Proceed with freezing and verifying `live-evaluation-v2`, retaining v1. Then audit the unchanged collection; run the frozen analysis only if that audit accepts. Any further production-only mismatch must retain its own rejection and receive separate review. The amendment remains a post-collection change in the eventual report, and no further transmission or spending is authorized.
