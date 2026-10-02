# R6-016 harness revision 1 — implementation review

Supplied by the reviewer in session on 2026-10-02, against harness revision 1 (`634d4194`). It is recorded verbatim below.

---

 Not ready to lock. I found one P1 and three P2 issues.

  1. P1 — Missing axiom evidence passes the unchanged gate. In axiom_gates (experiments/r6/r6-016/analysis.py:199), a delta of {} passes because .get('added') returns None. My direct probe supplied kernel reports containing Classical.choice and empty deltas for both   
     targets; both gates passed. Recompute the deltas against the frozen original targets, require complete fields, and reject disagreement with the verdict. Test the actual function: the current analysis scenarios substitute a stand-in.

  2. P2 — The diagnosis target is self-asserted. check_diagnosis (experiments/r6/r6-016/analysis.py:305) compares the command's target with record.local, rather than the frozen slot's local theorem. Changing both to Wrong.local still produces complete_success in the   
     synthetic analysis. Require the target from v2's locked selection.

  3. P2 — Diagnosis recomputation accepts inconsistent evidence. classify (experiments/r6/r6-016/diagnose_l070.py:107) accepts an established meta-level equality even when the recorded kernel attempt is unsuccessful. That probe becomes printed_only and passes analysis.
     Require kernel confirmation and reject this inconsistency. Also check contradictions before returning identical: syntactic equality plus an established counterexample currently returns identical.

  4. P2 — Resource exhaustion is not consistently recorded. counterexample (experiments/r6/r6-016/diagnosis/Diagnose.lean:173) discards exceptions and reports "no decision procedure". Earlier operations can escape altogether: a deliberately reduced recursion limit made
     the synthetic 0 ≠ 1 attempt throw instead of returning an outcome. Wrap the complete attempt and preserve resource exceptions as resource_exhausted, with the limit recorded.

  The review probes are in this script (/tmp/r6-016-review-probes.py); the resource probe is here (/tmp/R6016DiagnosisResourceProbe.lean).

  The three implementation choices are acceptable: 12 expected control-5 passes, the extra control-9 preparation hypotheses, and the disclosed export-environment limits. Failed diagnosis attempts must remain unresolved; a site-environment diagnosis can remain separate.

  The harness, analysis and binding suites passed. All five synthetic diagnosis reports reproduced exactly, and the dry lock reproduced 38 Python files, 23 data files, eight binaries and 108 sources. No retained certificate was read, l070 draw 5's export was untouched,
  and the working tree remains clean.
