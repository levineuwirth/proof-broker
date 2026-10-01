# R6-016 proposal and qualification audit amendment 1, revision 2 — review

Supplied by the reviewer in session on 2026-10-02, against both proposals as committed at `4fd9278f`. It is recorded verbatim below.

---

R6-016’s proposal findings are resolved. The audit amendment has one remaining P2, so implementation should wait for that correction.

  Rule B’s walk cannot satisfy R7 as written. The walk (experiments/r6/R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-PROPOSAL.md:72) requires each type-side ∀ to meet a value-side λ. In the interleaved _q example, after introducing x and the matching let, the 
  next type constructor is ∀ h, while the value is an application:

  (fun (_q : True) => fun h hn => …) True.intro

  I reproduced this on 4.32.0, both with and without the intervening let. The specified walk returns parameters_unverified after one parameter; R7 (experiments/r6/R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-PROPOSAL.md:117) requires it to be locatable.      

  Freeze an explicit rule for traversing value-side applied lambdas while leaving the type telescope stationary. Their binders must remain internal, with their argument definitions retained for dependency traversal. Then resume matching declaration   
  parameters. State the permitted forms precisely so R9’s eta-reduced value remains refused.

  The renaming correspondence and injectivity repair, stronger regression comparison, and unresolved-equality classification address the earlier findings. No additional findings there.

  No retained certificate was replayed; only temporary synthetic checks ran. The working tree is unchanged.
