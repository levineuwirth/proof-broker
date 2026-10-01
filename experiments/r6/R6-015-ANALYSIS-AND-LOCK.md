# R6-015 — the frozen analysis, control 3, and the lock, for review

**Revision 3**, 2026-10-01. It responds to [the review of revision 2](reviews/2026-10-01/R6-015-ANALYSIS-AND-LOCK-REVIEW-2.md), which
found two remaining P2 gaps. Revision 2 (`6f674b8a`) responded to
[the review of revision 1](reviews/2026-10-01/R6-015-ANALYSIS-AND-LOCK-REVIEW.md), which found two P1 defects and one P2. Revision 1
is `a335a054`. It follows [step 3's approval](reviews/2026-10-01/R6-015-STEP-3-REVIEW-2.md)
at `10f0daaf`. It completes
[the proposal's](R6-015-PROPOSAL.md) step 4 preparation: the analysis program, frozen; control 3, run under the lock; control 7,
cited; and the lock's contents.

**Status:**
- **No lock exists, and nothing has been replayed.**
- **The analysis has run only on stand-in evidence**, in its tests.
- **Control 3 ran once as a dry run**, with the lock check stubbed out
  ([record, labelled as such](reviews/2026-10-01/R6-015-CONTROL-3-DRY-RUN.json)). It is a synthetic probe with no retained
  certificate, and its result is not control 3's.

## What changed in revision 3

1. **The after-check revalidates the sealed files, not only the seal file.** After the analysis, every run's retained files are
   checked against its unchanged seal (`replay_campaign.sealed`, the event chain included, no unsealed file). That covers its
   export, residual, events, kernel reports and records. A file changed beneath an unchanged seal stops the analysis.
2. **Execution metadata must be complete and agree.**
   - **Control 3's exits must be integers:** nonzero on the constrained route, zero on the pinned one. A missing or boolean exit
     fails `evaluate`.
   - **Control 8's recorded command** must be exactly the locked program, in real mode, on the planned site's local and whole
     targets, with the frozen environment (`PATH`, the 4.32.2 `LEAN_SYSROOT`). Its exit code must be an integer agreeing with the
     report's.
   - **Each run's residual command** gets the same check. It must be the locked program in `--synthetic` mode, on the same targets
     and environment, exit 0, under `qualification-audit-v1`, reading this export.

   Both real rehearsal runs' residual commands meet these conditions, and revalidating their sealed files succeeds.

**The new tests:**
- an export changed after the control checks, beneath an unchanged seal, is rejected;
- a missing constrained exit, and a boolean pinned exit, are rejected as contradicting control 3's record;
- control-8 commands naming synthetic mode, another executable, wrong targets, another toolchain, exit 1, or no exit code are each
  rejected;
- residual commands with exit 1, without `--synthetic`, on another export, or under another audit lock are each rejected;
- a refused report under unchanged flags is rejected by the command's disagreeing exit and, with the exit made to agree, by the
  recomputed predicate.

## What changed in revision 2

1. **P1: the negative controls require the constrained final step's own failure.**
   - **Control 1:** every injected invalid mutation must be rejected by the checker, with its bypass recorded naming this
     certificate, and the constrained closer must fail in its final step **because the sum does not cancel**.
   - **Control 4:** the injected l170 proposal must fail there **as not positive**.
   - An earlier refusal, an unclassified failure or a harness failure fails these controls and is listed for diagnosis.
2. **P1: the control records are evidence, not verdicts.** Every predicate is recomputed.
   - **Control 8's record** must cover exactly the plan. Each entry must be bound to the current run: its seal and verdict digests,
     and for a proof the export (packed, and unpacked as audited) and the residual. The audit must have used the locked program on
     that export and residual. The predicate is recomputed from the retained report.
   - **Control 3's record** must be the frozen probe, run under this lock and bridge by the locked programs (its sources' digests
     against the lock), and not a dry run. Its predicate is recomputed from its results by `control3.evaluate`, which `control3.py`
     itself now uses.
   - **A record whose flags disagree with the recomputation is rejected.**
   - **Every consumed input, and every run's seal, is rechecked after the analysis.**
   - `control8` now records those digests per entry, and `control3.py` records its schema, sources and probe.
3. **P2: the overall outcome includes control 5's predictions.**
   - **The measurement** (the 36 retained certificates) is reported on its own.
   - **Overall complete success** also requires control 5's ten expected-pass entries to pass. The four entries without a
     prediction stay diagnostic only.
   - The analysis states the reasons for any outcome short of complete success.
4. **Axiom deltas, removals included, are retained per episode.** A bound harness failure is not consumption, requires diagnosis,
   and cannot satisfy a negative control.

The tests now cover each of the review's probes:
- **Control 8:** a refused audit report beneath unchanged flags is rejected; the 33 non-proof entries missing is rejected; one proof
  missing is rejected; a stale seal digest is rejected; an audit of another export is rejected.
- **Negative controls:** all the injected episodes ending in harness failure fail controls 1 and 4; the injected episodes refused at
  fact assertion fail control 1; l170 failing as "does not cancel" fails control 4.
- **Control 3:** a contradictory record, a dry run and foreign sources are each rejected.
- **Control 5:** a failed expected pass makes the outcome partial; a failed diagnostic-only entry leaves complete success intact.

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
- **The control-3 and control-8 records** are verified and recomputed, as above.
- **The step-3 record** (revision 2) and **R6-014's analysis** are bound as lock data.
- **Everything consumed** is rechecked afterwards.

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

**The measurement** (the 36 retained certificates) is reported on its own, per obligation, map and class.

**The overall outcome,** by the proposal's definitions, in which every control behaves as frozen:
- **complete success:** all 36 consumed and validated; controls 1, 2, 3, 4, 6 and 8 as frozen; and control 5's ten expected-pass
  entries passing;
- **none:** none of the 36 consumed and validated;
- **partial:** anything else, with the reasons stated and the failures located per obligation, map and class.

**The controls:**

| control | evaluated as |
|---|---|
| 1 (24 injected invalid mutations) | rejected by the independent checker, the gate bypass recorded naming this certificate, and **the constrained closer failing in its final step: the sum does not cancel** |
| 2 (25 valid mutations) | consumed and validated |
| 3 (synthetic probe) | `control3.py`'s record, verified and recomputed: the checker rejects the probe; the constrained route fails with the sum not cancelling; the pinned fold closes it through `omega` (the documented difference, never consumption) |
| 4 (l170) | the eight retained proposals rejected by the checker; the injected one rejected, its bypass recorded, and **failing in the final step as not positive** |
| 5 (14 regression entries) | each against its stated label. A pass means consumed and validated with R6-014's closer named (`term_mode_nat` at l069 to l078, `term_mode_int` at l096 and l099). **The ten expected-pass entries are part of the overall outcome**; the four without a prediction are diagnostic only |
| 6 (selection guard) | on every episode that reached selection: a `Nat` comparison takes `term_mode_nat`, and any other takes `term_mode_int` |
| 7 (cited) | R6-014's reference route closed all four obligations through `gated_omega`. It is reported, never counted |
| 8 | recomputed from the control-8 record's retained reports, every entry bound to its current run, with exact plan coverage |

## Control 3 (`r6-015/control3.py`)

`h : x ≤ y ⊢ x ≤ y` with (`h` 1, `neg_goal` 2), through R6's own helpers on the replay bridge, as the synthetic rehearsal ran. The
checker rejects it, so both runs are injected. In the dry run, as frozen:
- **the checker rejected the certificate,** with weighted sum `−x + y + 2`;
- **the constrained route** selected `term_mode_int` and failed: the weighted sum does not cancel;
- **the pinned route** closed it, with R6's receipt (`residual_closer: omega`): the documented difference.

## Tests (`r6-015/test_analysis.py`)

- **`classify`** was checked against real bridge error lines: the rehearsal's (does not cancel, the bridge gate, the pinned ℕ
  refusal), the messages the bridge tests pin, and R6-014's own retained refusal line from l166 draw 1. Each lands in its stage.
- **`analyse`** was run end to end on the real 108-episode plan with stand-in evidence: runs, verdicts, events and digests, and
  control-3 and control-8 records shaped as the programs write them. The scenarios:
  - everything as frozen gives complete success, all controls passing, 10 of 10 expected-pass entries, and 4 diagnostic-only;
  - l166's eight learned certificates failing at fact assertion gives partial, located as l166 learned 0 of 8 at `fact_assertion`;
  - all 36 failing gives none;
  - a failed valid mutation fails control 2;
  - a proved invalid mutation fails control 1;
  - a selection violation fails control 6;
  - a consistently recorded control-8 failure gives partial, with 35 of 36;
  - a consistently recorded failed control 3 gives partial;
  - and each of the review's probes, as listed above.
- **The binding and mutation tests** pass after these changes.
- **Control 3's reworked program** ran once more as a dry run, to scratch only: its record now carries its schema, sources and
  probe, and `evaluate` finds nothing unmet.

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

## Decided in review

1. **Control 1** requires the constrained final step's own failure: "does not cancel". The injected l170 proposal requires "not
   positive".
2. **Control 5's ten expected passes are part of the overall outcome.** The measurement is reported on its own.
3. **Acceptance 4:** no axiom added, and all within the allowed three. Removals are acceptable, and their deltas are retained.
4. **A bound harness failure** is not consumption, requires diagnosis, and cannot satisfy a negative control.

## After approval

1. Write the lock (`replay_campaign.py lock --plan r6-015/plan.json`) and commit it.
2. Run step 5 in the order above: 108 episodes, about two to three hours, offline.
3. Record R6-015.
