# R6-015 proposal, revision 4 — review (approval for implementation)

Supplied by the reviewer in session on 2026-10-01, against revision 4 (`46ac8901`). It is recorded verbatim below.

---

I approve revision 4’s design for implementation. The three choices are reasonable:

  • Control 8 can require Check 1 without Check 2, alongside successful kernel validation. Freeze an explicit predicate: binding is matches_residual, both targets are locatable, and both contain an explicit empty hypothesis list.
    Errors, refusals and missing fields must fail. Don’t require the audit’s certificate_alone classification—it also requires Check 2.

  • Reusing the frozen Audit program under R6-015’s own lock is appropriate. Freeze its executable/source digests, toolchain, driver and new inputs there. Keep qualification-audit-v1 unchanged.

  • Deterministic expectations can be resolved in step 3. Record map identities, matches to audited learned maps, and expectation labels before locking.

  One [P2] wording correction remains at route step 3 (experiments/r6/R6-015-PROPOSAL.md:133) and the draw-5 expectation (experiments/r6/R6-015-PROPOSAL.md:194): the audit found distinct atoms that print identically; it did not
  establish that cast-of-product versus product-of-casts caused the split. The synthetic requirement is sound, but its sufficiency to repair that map remains unknown. Suggested wording:

  > Cast/product normalization is a required synthetic case. l070 draw 5 remains without a fixed prediction pending diagnosis or replay.

  Printing the residual from the export resolves naming consistency; retain the separate seal, target and certificate bindings.

  I confirmed the learned map counts and shared-fold calls. I changed nothing and performed no candidate replay.
