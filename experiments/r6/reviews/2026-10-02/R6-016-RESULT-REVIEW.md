# R6-016 result — review

Supplied by the reviewer in session on 2026-10-02, against the record at `94b05f57`. It is recorded verbatim below.

---

 The complete-success result is verified. I reran the frozen analysis: it matched the committed record exactly. All 108 runs passed binding and seal checks, and the v2 lock verified in full.

  One P2 wording correction before publication: experiments/r6/R6-016.md:45 overstates the axiom reduction. Use:

  > At l166 and l175, the local targets use only propext and Quot.sound; at l096 and l099, both targets do. The whole targets at l166 and l175 retain their originals' Classical.choice dependency.

  The central claim remains correct: zero added or removed axioms at either target of all 74 proofs.

  The l070 diagnosis is supported. In subsequent summaries, call its failure observed rather than expected: its frozen label was "no fixed prediction".

  After that wording correction, please push the branch and open a PR against main. Leave merging for the PR review. The methods paper is next, keeping the four-obligation, one-file scope explicit.
