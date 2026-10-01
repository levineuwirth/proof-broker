# R6-015 — the frozen analysis, control 3, and the lock, for review

Recorded 2026-10-01. It follows [step 3's approval](reviews/2026-10-01/R6-015-STEP-3-REVIEW-2.md) at `10f0daaf`. It completes
[the proposal's](R6-015-PROPOSAL.md) step 4 preparation: the analysis program, frozen; control 3, run under the lock; control 7,
cited; and the lock's contents.

**Status:**
- **No lock exists, and nothing has been replayed.**
- **The analysis has run only on stand-in evidence**, in its tests.
- **Control 3 ran once as a dry run**, with the lock check stubbed out
  ([record, labelled as such](reviews/2026-10-01/R6-015-CONTROL-3-DRY-RUN.json)). It is a synthetic probe with no retained
  certificate, and its result is not control 3's.

## Step 5's order, all under the lock

1. `replay_campaign.py run`: the 108 planned episodes, each sealed.
2. `control3.py`: the review's synthetic probe.
3. `replay_campaign.py control8`: the audit program on every proof.
4. `analysis.py`: the frozen analysis.

Each step verifies the lock before and after.

## The analysis (`r6-015/analysis.py`)

**Inputs, all bound.**
- **Every planned run** must bind to the plan through `replay_campaign.bound`, the binding approved with harness revision 3. A run
  that does not bind stops the analysis.
- **The control-3 and control-8 records** must name this lock.
- **The step-3 record** (revision 2) and **R6-014's analysis** are bound as lock data.

**Consumed and validated, for one episode** (the proposal's acceptance):
- the outcome is a proof;
- the receipt names this certificate, the closer and the constrained final step;
- the local and whole kernel replays accepted;
- **acceptance 4:** no axiom added, and every axiom among `propext`, `Classical.choice` and `Quot.sound`;
- control 8's predicate is met.

**Failure stages,** from the verdict's bound evidence only. A failed reconstruction is classified by its first bridge error line,
against a frozen table of the bridge's own messages at `476fab31`, in order:
1. certificate decoding;
2. the packet binding (the fresh-reification guard);
3. the bridge's gate;
4. the specialization gate;
5. selection;
6. fact assertion (casts and opaque atoms included);
7. the constrained final step (does not cancel, not positive, reaches hypotheses, kernel rejected the step);
8. the fold.

Anything else is `unclassified`. A kernel rejection is `kernel` and a checker rejection is `checker`. Harness outcomes require
diagnosis and are not route results.

**Units:** every result is given per obligation (4), per map (6) and per class (5), by source, never merged. The program refuses
unless the measurement is exactly 36 episodes in 6 maps and 5 classes.

**The outcome,** by the proposal's definitions:
- **complete success:** all 36 retained certificates consumed and validated, and controls 1, 2, 3, 4, 6 and 8 as frozen;
- **none:** no retained certificate consumed and validated;
- **partial:** anything else, with the failures located per obligation, map and class.

**The controls:**

| control | evaluated as |
|---|---|
| 1 (24 injected invalid mutations) | rejected by the independent checker, the gate bypass recorded naming this certificate, and not proved. The stage where the closer failed is reported |
| 2 (25 valid mutations) | consumed and validated |
| 3 (synthetic probe) | `control3.py`'s record: the checker rejects the probe; the constrained route fails with the sum not cancelling; the pinned fold closes it through `omega` (the documented difference, never consumption) |
| 4 (l170) | the eight retained proposals rejected by the checker; the injected one rejected and not proved |
| 5 (14 regression entries) | each against its stated label. A pass means consumed and validated with R6-014's closer named (`term_mode_nat` at l069 to l078, `term_mode_int` at l096 and l099). An `expected pass` that fails is listed for diagnosis. **Control 5 is not part of the outcome's definition**, as revision 5 says |
| 6 (selection guard) | on every episode that reached selection: a `Nat` comparison takes `term_mode_nat`, and any other takes `term_mode_int` |
| 7 (cited) | R6-014's reference route closed all four obligations through `gated_omega`. It is reported, never counted |
| 8 | the control-8 record passes, and every proof was audited |

## Control 3 (`r6-015/control3.py`)

`h : x ≤ y ⊢ x ≤ y` with (`h` 1, `neg_goal` 2), through R6's own helpers on the replay bridge, as the synthetic rehearsal ran. The
checker rejects it, so both runs are injected. In the dry run, as frozen:
- **the checker rejected the certificate,** with weighted sum `−x + y + 2`;
- **the constrained route** selected `term_mode_int` and failed: the weighted sum does not cancel;
- **the pinned route** closed it, with R6's receipt (`residual_closer: omega`): the documented difference.

## Tests (`r6-015/test_analysis.py`)

- **`classify`** was checked against real bridge error lines: the rehearsal's (does not cancel, the bridge gate, the pinned ℕ
  refusal), the messages the bridge tests pin, and R6-014's own retained refusal line from l166 draw 1. Each lands in its stage.
- **`analyse`** was run end to end on the real 108-episode plan with stand-in evidence. The scenarios:
  - everything as frozen gives complete success, all controls passing, and 10 of 10 expected-pass entries met;
  - l166's eight learned certificates failing at fact assertion gives partial, located as l166 learned 0 of 8 at `fact_assertion`;
  - all 36 failing gives none;
  - a failed valid mutation fails control 2, so the outcome is partial;
  - a proved invalid mutation fails control 1;
  - a selection violation fails control 6;
  - a control-5 closer mismatch is listed for diagnosis, and the outcome is unaffected;
  - a control-8 failure makes the outcome partial;
  - a proof missing from control 8 stops the analysis;
  - a failed control 3 makes the outcome partial.
- **The binding and mutation tests** pass after the lock changes.

## The lock (`replay_lock.lock_record`, schema 3)

Computed as a dry run, not written. It binds:
- **34 Python files:** the episode, campaign, control-3, analysis and supervisor closure;
- **18 data files:**
  - the capture helper, the schemas, the checker and assembler sources, the vendor lock;
  - R6's census, site, fixture and qualification-audit locks;
  - **step 3's record (revision 2) and `mutations.py`**, which must name this plan and each other, with the record's episodes equal
    to the plan's;
  - R6-014's analysis and the qualification audit's record;
  - the three test files;
- **6 binaries:** the compiler, the exporter, the kernel checker, the glue library, the audit program and R6's exporter path;
- **the bridge revision** `476fab31`, and the instrumented `Tactic.lean` and its patch;
- **the plan,** and the seal and consumed artifact of all 108 sources.

## For review

1. **Control 1's criterion.** Rejection, the recorded bypass and no proof count as the closer failing, wherever it fails. The stage
   is reported. A failure before the constrained final step (at fact assertion, say) would pass control 1 without exercising the
   final step. Should control 1 instead require the constrained final step's stage?
2. **The outcome excludes control 5,** per revision 5.
3. **Acceptance 4:** no axiom added, and all within the allowed three. Removals are reported, not failures.
4. **A harness outcome** (an unobserved receipt, say) counts as not consumed, so the outcome would be partial, with the episode
   listed for diagnosis.

## After approval

1. Write the lock (`replay_campaign.py lock --plan r6-015/plan.json`) and commit it.
2. Run step 5 in the order above: 108 episodes, about two to three hours, offline.
3. Record R6-015.
