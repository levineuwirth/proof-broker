# R6-015 proposal review, and methods-paper pitch review

Supplied by the reviewer in session on 2026-09-30, against the uncommitted R6-015 proposal (revision 1, committed alongside this
record as reviewed) and the methods-paper pitch (`~/apocrypha/Passus/Proof Broker methods paper (2026-09-30).md`). It is recorded
verbatim below. The reviewer's synthetic probe was left at `/tmp/r6-015-review-fold.lean` and is not retained here.

---

I support taking the methods-paper pitch forward, but R6-015 needs changes before freezing. The code diagnosis and offline scope are sound; the main problem is whether the proposed route actually enforces the claimed consumption boundary.

1. [P1] The existing fold does not enforce “literal positivity only.”
   Proposal, line 81 (R6-015-PROPOSAL.md:81) describes omega as operating only between numerals. In the implementation (/home/jeans/Repos/research/proof-broker/lean-bridge/ProofBroker/Tactic.lean:3273), its subgoal is 0 < sum, with symbolic expressions and the original hypotheses still available.

   I reproduced the consequence using an unchanged copy of the fold on synthetic goals: for h : x ≤ y ⊢ x ≤ y, changing the coefficients from (h:1, neg_goal:1) to (h:1, neg_goal:2) still closes. The latter combination does not cancel its variables; contextual omega supplies the missing argument.

   Require hypothesis-free normalization of the weighted sum followed by a closed numerical positivity check. This finding concerns consumption attribution, not kernel soundness or acceptance of invalid certificates through R6’s independent checker.

2. [P1] Mutation does not necessarily invalidate a witness, and rejection must be tested at the closer.
   The controls (R6-015-PROPOSAL.md:98) leave the mutations underspecified. At l166, deterministic hrec is z = z + ↑Zmax * 0. Dropping that entry produces the valid learned witness; changing its coefficient also need not invalidate anything.

   Freeze exact mutations whose invalidity is independently established. Then test both checker rejection and deliberate injection into the closer; otherwise rejection by the checker says nothing about consumption. Include validity-preserving mutations as positive controls.

3. [P2] “Every claim can be checked by an outside party” exceeds the published evidence.
   The pitch’s central claim (/home/jeans/apocrypha/Passus/Proof Broker methods paper (2026-09-30).md:21) needs a stated trust boundary. Outsiders can reproduce analysis, check artifact bindings, and reconcile recorded reservations and releases. Without the credential, they cannot independently repeat the real-credential scan or recompute its secret-dependent commitment. Those remain operator attestations bound to artifacts.

   Likewise, ledger reconciliation establishes recorded commitments, not the provider’s actual bill; the synthesis explicitly distinguishes those quantities. Replace the universal claim with something like: “The protocol makes its recorded decisions independently auditable and states which claims retain operator or provider trust.” That is still a strong methods contribution.

4. [P2] The witness count needs an explicit equivalence relation.
   The units section (R6-015-PROPOSAL.md:31) mixes raw identity with equivalence under scaling. My recount found:
    • Four learned coefficient maps across the 32 accepted proposals.
    • Six coefficient maps across both sources.
    • Five classes modulo positive scaling.

   Also, l175 has four coefficient-list orderings across its eight draws, so “the same raw witness” is inaccurate. State the normalization rule and retain all six maps in the controls. The extra l166 map exercises a redundant equation; it does not supply a distinct mathematical argument.

5. [P2] Success would establish sufficiency of the revised reconstruction route, not selection alone.
   The outcome interpretation (R6-015-PROPOSAL.md:135) attributes complete success specifically to closer selection, but the intervention also changes fact assertion and casting—and should now constrain the fold. Either add a selection-only comparison or conclude that the refusal was removable by the specified reconstruction changes. Define complete success across both sources, including both l166 witnesses.

The methods pitch answers the “schema alone” objection well enough to justify the proposed precedent pass. Its strongest evidence is the documented failures, rejected revisions, and preserved amendment history. Real expenditure establishes deployment relevance; it does not itself establish methodological novelty. Keep novelty provisional and retain the explicit post-collection-amendment qualification.

I checked the tagged code, retained witness records, and amendment/scan records, and ran the synthetic fold probe (/tmp/r6-015-review-fold.lean). I did not replay retained certificates through a candidate closer, perform a new precedent search, or change either draft or branch.
