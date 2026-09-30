# R6 qualification 1 — what "consumed" means

Recorded 2026-09-30, after finding P1 of the [R6-015 proposal review](reviews/2026-09-30/R6-015-PROPOSAL-REVIEW.md), and revised
after [its own review](reviews/2026-09-30/R6-QUALIFICATION-1-REVIEW.md). R6 is closed.
This note qualifies the **description** of one stage. **Nothing in R6's runs, records, locks, analysis, audit or counts changes.**

## The finding

Both R6 closers consume a certificate through the same fold, `closeViaTermModeFalse`:
- **What the fold builds:** the weighted sum `s` of the certificate's multipliers over the named hypotheses, and a proof of `s ≤ 0`.
- **How it closes:** it discharges `0 < s` with `omega` through `closeOmegaSubgoal`.
- **Where that step runs:** in the goal's full context. `s` is symbolic, and every hypothesis is in scope.

The code is `lean-bridge/ProofBroker/Tactic.lean`, lines 3206, 3228–3286 and 3275–3279. The file is byte-identical at the pinned
revision `e627efe` that R6's episodes built, and at the `r6` tag. R6's overlay instruments the step without changing it:
`instrument.py` wraps it in `residual_started` / `residual_finished` events.

**The consequence,** from the review's synthetic probe on an unchanged copy of the fold: a combination whose variables do not cancel
can still close, with contextual `omega` supplying the missing argument. For `h : x ≤ y ⊢ x ≤ y`, the multipliers (`h` 1,
`neg_goal` 2) close as well as the valid (`h` 1, `neg_goal` 1).

## What it does not affect

- **Kernel soundness.** Every accepted proof was checked by the kernel on the whole declaration, with the axioms unchanged.
- **Acceptance of invalid certificates.** Every certificate that reached a closer had first been verified by R6's independent checker,
  which requires exact cancellation over the emitted rows.
- **The results.** 88 of 88 slots sent with a response; 80 of 80 certificate-feasible slots verified; 48 of 88 slots whole-validated,
  which is 6 of 15 obligations. The analysis, the audit, both amendments and every lock stand as recorded.

## What "consumed" means in R6

**Precisely:** the selected closer folded this independently verified certificate, building the weighted sum from its multipliers over
the named hypotheses, and the kernel accepted the resulting proof.

**It does not establish** that the certificate's multipliers alone discharged the contradiction. The fold's final step could draw on
the goal's hypotheses. The receipts do not establish whether it relied on them, and that dependency has not been audited across all
48 proofs. It is auditable: the full proof term of every one of the 48 proofs is retained (`solution.ndjson.gz`, a `lean4export`
export), and the receipts lack only dependency attribution.

**The data was accurate; the prose overstated.**
- Each consumption receipt records `residual_closer: omega` and `derivation_replayed: false`.
- Each proof run's chain records the residual goal verbatim. At l069 draw 1 it is
  `0 < 1 * (↑x.val + 1 - ↑(2 ^ 24)) + 1 * (↑z.val + 1 - ↑(2 * Zmax)) + 1 * (↑(2 ^ 24 + 2 * Zmax) - ↑(x.val + z.val))`.
  Under the cast identities that sum is the constant 2, but that is one example, not a test of all 48.

What overstated the step is these descriptions, retained unchanged as written:
- `R6-013.md` §3: "…ending in `omega` on the literal positivity subgoal";
- the `consumption_overlay.py` docstring: "(`omega` on the literal positivity subgoal only)";
- the `closeViaTermModeFalse` docstring in `Tactic.lean`: "a literal-coefficient polynomial-identity check, narrower than a goal-side
  omega call";
- `R6-SYNTHESIS.md`, "a pinned closer consumes it". It gains one dated sentence pointing here.

**The locked and sealed sources are not edited.** That covers `R6-013.md`, the overlay, `Tactic.lean` at its pins, and the "consumed"
column of the frozen analysis. Editing them would break R6's locks and seals, and a qualification is not an invalidation.

## Whether the stronger claim holds

**It is open, and two offline checks bear on it.**
1. **A dependency audit of the 48 retained proof terms.** Does the subproof of `0 < s` in each proof refer to any of the goal's
   hypotheses? This answers the question for R6's proofs directly, with no new episode.
2. **R6-015's regression control** ([proposal](R6-015-PROPOSAL.md), control 5) replays R6's proved certificates through a
   hypothesis-free final step.
   - **Passing** establishes that the certificate suffices under the new route.
   - **Failing** establishes nothing about R6's proofs by itself, and requires diagnosis. The cause could be incomplete cast
     normalization, an implementation defect, or contextual dependence, and only the first check can settle the last.

Until the dependency audit is done, R6 claims only the qualified meaning above. A passing control 5 would show that the
certificates suffice. It would not show how R6's own proofs were built.

## Addendum

*2026-10-01:* the audit of the final step is recorded in [addendum 1](R6-QUALIFICATION-1-ADDENDUM-1.md). The stronger reading holds
for 24 of the 48 proofs (l069, l071, l078). l070 drew on context at every draw. l096 and l099 are unbound and not classified.
