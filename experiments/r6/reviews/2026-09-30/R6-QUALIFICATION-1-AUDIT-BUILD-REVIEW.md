# R6 qualification 1 audit, build revision 1 — implementation review

Supplied by the reviewer in session on 2026-09-30, against build revision 1 (`8a8bbeae`). It is recorded verbatim below.

---

I would not lock this version yet. All six controls pass, but I found two P1 defects and two P2 gaps.

  1. [P1] The environment comparison accepts differences beyond annotations. experiments/r6/qualification-audit/Audit.lean:67 compares declaration kind, universe parameters, type and optional value. It omits recursor
     rules, constructor fields, inductive metadata and other declaration fields.

     I changed Nat.rec.rules[0].nfields from 0 to 1 in a copy of C2’s export. The tool accepted it as “equal up to annotations.” Normalize expressions throughout the complete ConstantInfo, including recursor-rule right-
     hand sides, then compare every remaining field. Add this mutation as a refusal control.

     The 4.32.2 incompatibility claim also needs rechecking. I built the tool separately on 4.32.2: all six controls pass, with exactly the same shared-constant counts as 4.32.0. They also pass with the fuller comparison
     above, which rejects the mutation. This does not establish compatibility for every R6 export, but it does not support rejecting 4.32.2 on the controls’ evidence. Its nested-inductive kernel fix is documented in the
     release notes (https://lean-lang.org/doc/reference/latest/releases/v4.32.2/).

  2. [P1] Residual binding does not gate classification. experiments/r6/qualification-audit/Audit.lean:348 records binding_matches_residual, but still emits the usual classifications. Giving unmodified C2 an incorrect
     residual produces binding_matches_residual: false alongside sufficient_but_context_referenced; the driver does not reject it.

     For real runs, a mismatch must prevent a bound sufficiency classification for either target. Synthetic controls can have an explicit mode without retained-residual binding.

  3. [P2] Dropping let definitions needs checked specialization back. I accept quantifying let-bound values as plain variables as a stronger, hypothesis-free test. However, experiments/r6/qualification-audit/Audit.lean:250
     calls that transformed statement “original,” and checks subsequent specialization against it. C5 succeeds over plain v, with no checked specialization restoring v := Classical.choose h.

     Treat definition dropping as an abstraction: retain the substitution and kernel-check the resulting proof against the original hpos type. This specialization can instantiate the universal theorem without running omega
     in the original context.

  4. [P2] The driver does not freeze or recheck all audit inputs. experiments/r6/qualification-audit/qualification_audit.py:128 omits the analysis file that selects the 48 slots. In a disposable test, changing that file
     left verify_lock() passing; the live-evaluation lock does not bind that analysis output either.

     Also, line 174 (experiments/r6/qualification-audit/qualification_audit.py:174) rechecks the locks but does not recheck the run seals and consumed artifacts after auditing. Freeze the selection input and retain the
     seal/artifact digests for verification before and after.

  C6’s revised mechanism and the explicit internal-hypothesis labels are acceptable. The copied fold matches the pinned source byte for byte.

  I reran all six controls, verified the live-evaluation lock’s 88 files, and confirmed refusal without a lock. Probe artifacts are under /tmp; I changed no repository files, created no production lock, and read no R6
  proof exports during this review.
