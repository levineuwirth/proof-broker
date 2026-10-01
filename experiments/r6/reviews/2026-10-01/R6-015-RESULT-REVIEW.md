# R6-015 result — review

Supplied by the reviewer in session on 2026-10-01, against the R6-015 record as committed at `6eb23f29`. It is recorded verbatim
below.

---

Reviewed experiments/r6/R6-015.md. The reported partial result is supported; no result-changing findings.

  I reproduced the frozen analysis exactly, including lock verification and all 108 runs’ binding and seal checks:

  • All 36 retained certificates produced kernel-accepted proofs.
  • 18 consumed and validated: l178 and l204, both sources.
  • Controls 2 and 8 fell short for the documented reasons.
  • All 24 injected invalid mutations failed at the required final step; all ten expected regression passes held.
  • All 74 produced proofs have empty local hypothesis dependencies; 57 pass both audit targets.

  I also missed the distinction between allowed axioms and unchanged axioms in the build review. The frozen acceptance criterion correctly excludes the affected proofs.

  Keep this result and its definitions fixed. The axiom-preserving route and l175 audit amendment require separate review; l070 remains an open normalization diagnosis. The disclosed diagnosis-list gap does not alter the accounting.    

  No essay change or follow-up implementation is needed for this review. The working tree remains unchanged.
