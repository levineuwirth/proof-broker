# R6-013 auditor revision 2 review

Reviewed commit: `59450aff`; previous review preserved at `37789f08`.

The six original probes now reject at their intended cases. The receipt-binding, closer-label and historical-target repairs work. The original runs still pass a fresh 655-case audit and reproduce the previous retained-byte recount. Two P2 gaps remain in the audit of reconstruction inputs and in the new command checker. Neither result indicates that the original executions were wrong.

1. **P2 — Refused reconstruction does not bind the source contents at the reconstructed command paths.**

   `stage_commands` correctly requires this run's `input/` mount, but `reconstruction_common` does not compare that directory's source and helper to the permitted extraction. Those comparisons remain in `site_shared_checker`, which only successful proofs enter. `no_extension_registered` checks imports and dynamic-library arguments; it does not establish that the rest of the helper is the frozen helper.

   On a fresh copy of `l204-draw1`, replacing the helper's one call to `proof_broker_term [$adapter:ident]` with `omega`, then using the production finalizer to regenerate scan, terminal and seal, is accepted by all 655 cases. The auditor still calls it the pinned Nat closer's refusal. A second independent mutation replaces `input/Frozen.lean` with l070's instrumented source; this also passes all 655 cases.

   Move reconstruction source, helper and patch equality into a shared check applied to every path that reaches reconstruction, before attributing a refusal or deriving extension absence. Bind the exact site anchor and task identity as on the successful path. Do not require successful context output or a consumption receipt on a failed reconstruction. Add separate controls for the helper and source substitutions.

   Relevant code: `cohort_v6_audit.py`, `no_extension_registered` at line 1172, `site_shared_checker` at line 1226, and `reconstruction_common` at line 1269. The missing comparison is the extraction-source block currently inside the success-only checker.

2. **P2 — The system-library boundary is a lexical prefix test and can be escaped.**

   `stage_commands` lines 864–869 accept any number of `--ro-bind` triples if the host string starts with `/usr/lib/`, the guest starts with `/usr/lib/` or `/usr/lib64/`, and the whole block matches other runs of that stage. They do not normalize containment, establish that the entries are libraries, or bind the host/guest pairs to an independently established dependency closure.

   The probe inserts `--ro-bind /usr/lib/../../etc/hostname /usr/lib/review-extra-data` into the library block of all ten reconstruction commands, then finalizes those copies. The full auditor accepts all 655 cases. The source resolves outside the system-library directory, and the guest is an extra mount the pinned stage builder would not produce. Changing every instance deliberately exercises the fact that cross-run agreement alone cannot establish the first instance's validity. No altered command is executed and no hostname bytes are read by the probe.

   Validate canonical host and guest containment and the permitted source/destination relationship; reject directory mounts, traversal and extra entries. Bind the allowed dependency pairs to independent evidence, such as a reviewed inventory anchored to the original committed commands, or a verified dependency closure for the pinned binaries with an explicit availability qualification. Account for legitimate symlink pairs such as the loader and `libgmp`; literal host/guest equality would reject real commands. Keep the cross-run equality check as a further consistency check. Add a control that alters all copies of one stage so the first-observed block cannot become its own authority.

The challenge-path qualification also needs narrower wording. The auditor establishes that both replay commands name the same path, whose basename is `challenge.ndjson`, whose parent starts with `r6-campaign-challenge-`, and which is outside the recorded root. It does not recompute the bytes of that deleted temporary file. Setting both paths on l070 to `/etc/r6-campaign-challenge-review/challenge.ndjson` still passes all 655 cases. The pinned driver does hash its temporary challenge before replay, so that is a source-code property; it is not a retained-byte verification of the mounted temporary file. Describe these two claims separately. Historical bytes that were not retained cannot be recovered by an auditor change; stronger path-to-content evidence belongs in a future execution revision if required.

The build qualification should travel with the audit too. The report accurately says that `stage_tools` calls `run.build_tools`, but its docstring says “without building anything” and the output scope still says “no native execution.” `build_tools` writes cached source/configuration files and invokes `lake build` for the exporter and checker. This review observed successful cached builds, with no episode or Lean proof replay. Prefer “no native episode or proof replay; cached tool build invoked,” or separate path discovery from tool building. This is not a claim that any retained run changed.

Verification performed:

- Fresh public audit: accepted, 655 cases.
- Recorded 94-control suite: exact names compared with the module constants, one accepted baseline and 93 expected rejection cases, program and auditor digests match. The entire 94-case suite was not rerun in this review.
- Fresh independent probe run: each case starts with an accepted 655-case baseline on a fresh copy. All six original mutations now reject at the intended case. Four new probes are accepted: two source substitutions, the common library-block escape, and the challenge-path qualification probe.
- Fresh retained-byte recount: byte-for-byte equal to the previous recount record. Across v4/v5/v6, 45 runs, 1,553 event hashes and 11,785 retained seal entries recompute. The six v5/v6 proof exports and axiom deltas match; fifteen sites' v3/v4 preparation outputs match.
- The repair commit changes seven non-locked paths. Original review files, locked sources, policies and run directories are unchanged.

Reproductions: [cohort_v6_v2_review_probes.py](cohort_v6_v2_review_probes.py), [R6-013-V2-REVIEW-PROBES.json](R6-013-V2-REVIEW-PROBES.json). The probe script uses the production finalization helpers on temporary copies and does not alter the original review script's 628-case precondition. A first construction trial placed the extra mount outside the library block and was correctly rejected; the final retained run places it inside the block and reproduces the finding. Only the completed final run is used for the claims above.

Scope: source inspection, retained-artifact recomputation and mutation audits. The auditor invoked cached tool builds; no native episode, kernel replay, real-credential read, provider call, signing, commit or push was performed. New review files only; no auditor or frozen implementation changes.
