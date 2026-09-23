# R6-013 auditor revision 3 review

Reviewed commit: `74fbb16f`; previous review preserved at `326df886`.

Approved at the recorded canned-checkpoint scope. No blocking findings remain from the two preceding reviews. This is an audit closeout, not live authorization or a new proof-execution attestation.

The reconstruction-source repair closes the success/refusal asymmetry. `reconstruction:sources_bound` compares both input directories' exact file populations, instrumented sources, helpers and patches to the permitted site extraction. The check runs before closer attribution and before extension absence is inferred from the imports. The helper-to-`omega` substitution and the other-site source substitution now reject there; the successful-proof helper control rejects there too.

The library repair no longer relies on agreement among the submitted episodes as its authority. The inventory is pinned by digest, and its pairs are derived from the original command records in commit `7a82fed3`. I regenerated the complete inventory byte-for-byte, including its digest `562ad153446968c19434449f3fec4ab34f58e9166fe7f2aad45cf4b228e1bead`. I also independently extracted the system-library mount pairs from all 108 non-sender command records directly through Git objects, without the auditor's command-splitting function. All ten stage inventories and their run populations match. The current-host dependency comparison agrees for every stage; it remains an availability observation.

On fresh copies, the traversal mount repeated across every reconstruction rejects at the first run's command check. Adding a canonical library pair to every assembly command also rejects, as does removing a pair from one certificate-check command. The independent review additionally changes a temporary copy of the inventory itself and confirms that its digest gate rejects it.

The challenge qualification is preserved. Moving both replay paths to the characterized `/etc/…` location remains accepted, while moving the path inside the recorded root rejects. The machine-readable `challenge_claim` states that the temporary bytes were not retained and distinguishes the pinned driver's hash check from a retained-byte check. The audit's `scope` records cached tool builds and excludes native episodes and proof replays.

One non-blocking wording remnant: `cohort_v6_audit.py:891`, inside the `stage_commands` docstring, still calls the challenge “the verified temporary copy.” That sentence should match the narrowed path-only claim. The executable checks, returned scope, revision-3 module documentation and report already state the intended limitation correctly.

Verification:

- Fresh public audit: 665 cases accepted, including all ten new source checks.
- Recorded control suite: exact 101-name population checked against the source constants; one accepted baseline and 100 mutations at their expected rejection cases; the separate characterized challenge case is present and accepted. Program and auditor digests match. I did not rerun the full 101-control suite.
- Fresh targeted review: eight mutations, each preceded by an accepted 665-case audit on an unmutated copy. Seven reject at their intended cases and the challenge characterization remains accepted. These include the previous review's four probes and the four additional binding controls.
- Fresh retained-byte recount reproduces the prior record exactly: 45 runs, 1,553 event hashes and 11,785 retained seal entries across v4/v5/v6, with no mismatch; six v5/v6 proof exports and axiom deltas unchanged, and all fifteen v3/v4 preparation records unchanged.
- The repair commit changes seven non-locked paths. Earlier review records, locked implementations, policies and run artifacts remain unchanged.

Reproduction: [cohort_v6_v3_review.py](cohort_v6_v3_review.py), [R6-013-V3-REVIEW-PROBES.json](R6-013-V3-REVIEW-PROBES.json), [R6-013-V3-REVIEW-AUDIT.json](R6-013-V3-REVIEW-AUDIT.json), [R6-013-V3-REVIEW-RECOUNT.json](R6-013-V3-REVIEW-RECOUNT.json), and [R6-013-V3-REVIEW-LIBRARY-INVENTORY.json](R6-013-V3-REVIEW-LIBRARY-INVENTORY.json). Previous probe scripts were imported without editing their historical assertions or results.

Only review files were added. The auditor and inventory generator invoked cached exporter/checker builds. No native episode, proof replay, real-credential read, provider call, signing, commit or push was performed.
