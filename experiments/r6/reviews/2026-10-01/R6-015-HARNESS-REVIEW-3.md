# R6-015 replay harness, revision 3 — review (approval)

Supplied by the reviewer in session on 2026-10-01, against harness revision 3 (`9cd28f68`). It is recorded verbatim below.

---

 Approved: harness revision 3 at 9cd28f68. The remaining P2 is resolved; no further findings.

  Verification:

  • All twelve committed binding probes were refused; well-formed runs bound.
  • Control 8 failed the unfinished proof and passed the well-formed proof.
  • Five additional probes confirmed rejection of duplicate, misplaced or child-sourced terminal events, a child-sourced start, and a wrong terminal digest.
  • Both rehearsal records passed seal, provenance and termination checks, and were correctly refused as planned episodes.

  Proceed with step 3: mutation sets, validity labels, control-5 maps and the plan, followed by the frozen analysis program and lock review.

  No retained certificate was replayed during this review. No lock was created, and the working tree is unchanged.
