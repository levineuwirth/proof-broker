# R6-016 proposal and qualification audit amendment 1, revision 1 — review

Supplied by the reviewer in session on 2026-10-02, against both proposals as committed at `ac5f7fec`. It is recorded verbatim below.

---

Not yet approved for implementation. The normalizer choice checks out, but three proposal details need revision.

  1. P1 — Rule B still guesses parameter identities. The parameter-list rule (experiments/r6/R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-PROPOSAL.md:55) filters the fold context rather than establishing correspondence with the declaration’s telescope. I     
     reproduced a valid synthetic proof whose parameters are x, h, hn, but whose fold context is x, _q, h, hn because an applied lambda introduces _q. Taking the first three eligible binders maps h to argument 2 instead of argument 1, reporting the   
     wrong whole-declaration hypothesis.

     Track the verified declaration parameters explicitly through the type and proof; refuse an unverified correspondence. Extend R5 with an interleaved internal binder.

  2. P2 — An unsuccessful equality proof must remain unresolved. The diagnosis classifications (experiments/r6/R6-016-PROPOSAL.md:145) need an explicit equality_not_established outcome. Failure of omega and ring normalization does not establish       
     arithmetic inequality. Record each attempt and distinguish refusal, resource failure and unsuccessful proof. Reserve mathematical distinctness for independently checked evidence, or define distinct strictly as a syntactic observation.

  3. P2 — Renaming needs a global injectivity check. Rule A’s conditions (experiments/r6/R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-PROPOSAL.md:42) do not exclude two originals mapping to the same fresh search name. Require unique source identities,        
     distinct destinations and correspondence to the sealed rows’ indices and original binders. Add controls for duplicate destinations and a wrong binder index.

  I independently confirmed on 4.32.0 that posOfLinearNum has exactly propext and Quot.sound, and the cast/product identity closes by rfl. The l175 correction, separately locked applications, fixed audit fallback and post-replay diagnosis order are   
  sound design choices.

  No retained certificate was replayed, and the working tree is unchanged.
