# R6-016 — harness, controls, diagnosis and analysis, for implementation review

**Harness revision 1**, 2026-10-02. It is step 4 of [the proposal, revision 2](R6-016-PROPOSAL.md) (section 7): R6-015's harness,
copied, with R6-016's bridge revision, control 9, the l070 diagnosis program and the analysis changes, rehearsed on synthetic
goals only. The bridge (`64585867`) was [approved](reviews/2026-10-02/R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-BUILD-REVIEW.md) with
build revision 2. `qualification-audit-v2` is locked (`c42906ed…`), and addendum 2 is recorded, so control 8's program and control
5's classifications are both fixed before this lock.

**Status:**
- **Nothing is locked, and nothing of R6-016's has been replayed.** Without the lock, every planned episode is refused at its
  boundary, and every pinned one always.
- **No retained certificate or export was read** for this revision. The dry lock hashed the 108 planned sources' seals and
  consumed artifacts, as R6-015's did. R6's l070 draw 5 export was not touched.
- **The rehearsals all pass** (below), each recorded and labelled as pre-lock.
- **Tests:** `test_harness.py` (6), `test_analysis.py` (2, with every R6-015 probe and R6-016's new ones) and `test_binding.py`
  (14 probes) pass.

## How to read the change

**R6-015's modules were copied unchanged into `r6-016/` first** (`468d0131`). Against that commit, `git diff` shows exactly R6-016's
changes; the new files are `labels.py`, `control9.py`, `diagnose_l070.py`, `diagnosis/Diagnose.lean` and `test_harness.py`.
R6-015's files, lock and runs are untouched.

| module | what changes from R6-015's |
|---|---|
| `replay_bridge.py` | the bridge revision (`64585867`), the build directory and package name. **The observations are R6-015's, byte for byte** (`test_harness.py` compares them with R6-015's module), and apply to the new `Tactic.lean` |
| `replay_lock.py` | R6-016's lock. **No pinned episode is admitted** (`REHEARSALS` is empty). Both audit programs are bound: v2's, which runs, and v1's, by digest and as v2's lock records it. The closure gains control 9, the diagnosis, the labels; the data gain v2's lock and the records the labels read, the diagnosis source, R6-016's tests, and v1's driver (v2's driver loads it from its path, outside `sys.modules`) |
| `replay_episode.py` | the schema (`r6-016-replay-1`), the provenance directory, and **the residual printed by v2's program** |
| `replay_campaign.py` | **control 8 runs v2's program**, under the same frozen predicate, and verifies v2's lock in full (program, sources, toolchains' contents, controls' environment) before and after |
| `control3.py` | the lock, bridge, work directory and schema; a labelled `--dry-run`. The probe, expectations and `evaluate` are R6-015's |
| `analysis.py` | section 6's changes (below) |
| `rehearse_synthetic.py`, tests | the same cases and probes, on R6-016's modules; the new probes below |

**The plan is R6-015's** (`r6-015/plan.json`, 108 episodes) with its step-3 record, unchanged. The runs go to `r6-016-runs/`.

## Control 5's labels (`labels.py`, [record](reviews/2026-10-02/R6-016-CONTROL-5-LABELS.json))

The proposal: "computed by R6-015's frozen rule from the qualification audit's classifications as recorded at R6-016's lock:
addendum 1, and the amendment's addendum 2 if it exists by then."

- **The entries** are R6-015's step-3 record's 16 rows, unchanged. Only classifications and labels are recomputed.
- **The classifications** are addendum 1's, and addendum 2's for the 16 slots addendum 1 left unbound. Addendum 2's record is
  checked: v2's, under its lock, gated on the passing regression record (the approved `regression_passed`).
- **The rule** is R6-015's `expectation`. Its first clause names l096 and l099, with the reason "not classified by the audit";
  it is applied as that condition, over classifications.
- **A regression check:** wherever every classification comes from addendum 1, the label must equal R6-015's. It does at every
  such entry.
- **Result: 12 expected passes,** R6-015's 10 and l096's and l099's learned maps (all 16 slots `sufficient_but_context_referenced`).
  Two entries stay diagnostic only (l070 draw 5, `no_fixed_prediction`; l071's deterministic map, `no_expectation`); two are not
  retained.

## Control 9 (`control9.py`, [dry run](reviews/2026-10-02/R6-016-CONTROL-9-DRY-RUN.json))

Synthetic goals, through R6's own preparation and reconstruction helpers on the replay bridge, as control 3 runs: R6's driver
assembles each packet, R6's checker verifies it, and a case the checker rejects runs injected.

| case | goal and witness | checker | expectation | dry run |
|---|---|---|---|---|
| 9a | the mixed-carrier goal (`hn`, `hz`, `neg_goal`) | accepts | closes; `posOfLinearNum` has exactly `propext`, `Quot.sound`; the theorem's axioms are among its `omega` proof's, which avoids `Classical.choice` | closes; all three `[propext, Quot.sound]` |
| 9b | `h : x * y ≤ 5`, `hc : y * x ≤ x * y` ⊢ `y * x ≤ 5`; (`h` 1, `neg_goal` 1) | rejects | does not cancel | `-1 * (y * x) + 1 * (x * y) + 1` |
| 9c | the same product, same order | accepts | closes | closes |
| 9c | `↑a * ↑b ≤ z` ⊢ `↑(a * b) ≤ z` | **rejects** | closes | closes, injected |
| 9d | `3 * (a − b)` (`neg_goal` 3); `a * 0`; `↑(Zmax * 2 ^ 16)` against `65536 * Zmax` | accept | close | close |
| 9e | `m < m + n + 1`, `neg_goal` alone | rejects | does not cancel | `1 * (↑n) + 1` |
| 9e | the same with `_pb_nonneg_n` | accepts | closes | closes |
| 9f | a cast instance taking `tag` (the build review's case), with `h'` | accepts | reaches hypotheses `[tag]` | reaches hypotheses `[tag]` |

- **Every failing case** must reach the constrained closer, selected on the constrained route, and fail in its final step with the
  frozen reason; **every closing case** must exit 0 with the constrained receipt.
- **9b and 9f carry one extra hypothesis** (`hc`, `h'`). R6's preparation helper closes its goal with `omega`, which cannot prove
  either goal alone; the first dry run stopped there. The witness does not use the hypothesis, so the case tests the same thing.
- **The checker verdicts are frozen from the dry runs.** One is worth noting: R6's checker treats `↑(a * b)` and `↑a * ↑b` as
  two atoms and rejects 9c's cast case, which the constrained route closes, injected.

## The l070 diagnosis (`diagnose_l070.py`, `diagnosis/Diagnose.lean`, [rehearsal](reviews/2026-10-02/R6-016-DIAGNOSIS-REHEARSAL.json))

**The program reads the export exactly as the locked audit does.** It imports `AuditCore`: v2's `Audit.lean`, byte for byte, cut
before its `main`. The build checks the file against v2's lock and that the cut is a prefix. The atoms are the audit's
(`atomsOf`), in the local target's single fold.

**It runs under the R6-016 lock, after the replay,** on `cohort-live-v9/l070-draw5/solution.ndjson.gz`, checked against its
seal and v2's locked selection, with `live-evaluation-v3` verified before and after.

**The attempts, in the proposal's order:**
1. printed: default (equal, by selection) and `pp.all`;
2. syntactic: equality after instantiating metavariables, equality up to metadata, the first differing subterm (path, both sides
   under `pp.all`);
3. definitional: `isDefEq` at reducible, instances and default transparency, each without and with `zetaDelta`; and the kernel's
   `rfl`, closed over the pair's variables. **A meta-level attempt counts as established only when the kernel accepts the same
   `rfl`**;
4. arithmetic: `intros; omega` and, separately, `intros; grobner` (core's `grind` restricted to its commutative-ring solver), on
   the closed statement in an empty context, each proof kernel-checked;
5. a counterexample: every ℕ or ℤ variable at 0 to 3, definitions unfolded, `decide` kernel-checked; another type, a proof term,
   or more than six variables refuses.

**Outcomes** are `established`, `refused`, `resource_exhausted` (400,000 heartbeats per attempt, counted from its start; the
kernel's own limits) or `unsuccessful`. **The classification** is computed in Python from established evidence only, in the
proposal's order, and recomputed by the analysis. Equality and a counterexample both established would contradict the kernel and
is reported as `contradictory_evidence`.

**The rehearsal** (synthetic exports, each frozen):

| case | pair | classification | basis |
|---|---|---|---|
| `d_instance` | `x * y` against a product through a `@[reducible]` instance | printed only | default transparency, confirmed by the kernel |
| `d_adding` | against an instance that adds | distinct | kernel-checked counterexample at x = 1, y = 0 |
| `d_swapped` | against an instance that swaps the factors | not established | arithmetically equal, but nothing sees through the instance |
| `d_cast` | `↑x * y` against a cast `fun n => Int.ofNat (0 + n)` | not established | the same |
| `d_opaque` | `@g ℕ 0` against `@g ℤ 0`, `g` opaque | not established | nothing applies |

**Three limits of reading an export, found in the rehearsal and stated for the record:**
1. **R6's pinned exporter erases metadata** (`exportMData` is off), so no export carries any: `identical` cannot arise from a
   pair. `classify`'s branch is unit-tested.
2. **An export carries declarations, not attributes.** Outside `Init`, an `@[instance]` or `@[reducible]` definition is a plain
   definition in the replayed environment. The meta-level attempts below default transparency, and the tactics, therefore see
   less than in R6's environment: `d_cast`'s cast is `@[reducible]` in its source, and `grobner` proves the equality there, but
   not from the export. **Default transparency and the kernel are unaffected,** so `printed_only` (kernel-confirmed) is sound;
   a failure below default is not evidence about R6's environment.
3. **The counterexample's domain is ℕ and ℤ.** l070's variables are `ZMod P` values (from the site's frozen context, which the
   harness reads), so at a pair over them the attempt will refuse. No `arithmetically_equal` pair could be built synthetically
   either (2. above); that branch is unit-tested.

## The analysis (`analysis.py`)

**R6-015's frozen analysis, with section 6's changes:**
- **The axiom gates, separately**, per episode and per target: the allowlist (from the kernel's report) and unchanged (from the
  run's delta against the frozen expected targets). Consumed and validated needs both. The tallies count proofs failing each.
- **Control 9** verified and recomputed as control 3 is: schema, lock, bridge, locked sources, the frozen cases and witnesses,
  not a dry run, `evaluate` recomputed. Complete success now needs controls 1, 2, 3, 4, 6, 8 and 9.
- **Control 8** against v2: the record's audit lock, and each run's residual command under v2's lock.
- **The diagnosis's record**, by identity, provenance (the locked tool and sources, v2's `Audit.lean`), its command, the sealed
  export's digests (checked again afterwards), and its classifications recomputed. Reported; it counts toward nothing.
- **Control 5** from R6-016's labels, verified again: 12 expected passes.
- **Failures after a proof** are listed per episode with their gate (`kernel`, `allowlist`, `unchanged`, `control_8`) and
  require diagnosis.

The failure-stage table is R6-015's: the bridge's messages at `64585867` are those at `476fab31`, checked line by line, and
`test_classify` now also uses R6-016's own lines from the control-9 dry run.

**New probes** (`test_analysis.py`): a proof failing the unchanged gate alone (`Classical.choice` added at the whole target) and
one failing the allowlist alone are not consumed and are listed with that gate; a control-8 failure is listed; an l096 expected
pass failing makes the outcome partial; control 9's contradictory, dry-run, altered-case and foreign-source records are rejected,
and a consistently failed control 9 makes the outcome partial; the diagnosis's every class is recomputed, and a contradicted
classification, another export, a failed exit, another tool or an unlocated report are rejected.

## The rehearsals (pre-lock, synthetic only)

| rehearsal | result |
|---|---|
| [synthetic harness](reviews/2026-10-02/R6-016-HARNESS-REHEARSAL-SYNTHETIC.json) | R6-015's four cases, as frozen: the valid case closes with the constrained receipt, its residual is printed by v2's program and control 8 passes; the bridge gate refuses the invalid certificate; injected, it fails "does not cancel"; the pinned ℕ closer refuses the `Int` goal |
| [control 3, dry run](reviews/2026-10-02/R6-016-CONTROL-3-DRY-RUN.json) | as frozen: rejected by the checker; the constrained route fails "does not cancel"; the pinned fold closes it through `omega` |
| [control 9, dry run](reviews/2026-10-02/R6-016-CONTROL-9-DRY-RUN.json) | all ten cases as frozen |
| [diagnosis](reviews/2026-10-02/R6-016-DIAGNOSIS-REHEARSAL.json) | all five cases as frozen |

## The lock (dry run), `r6-016-replay-v1`

Computed, not written: 38 Python files (the closure), 23 data files, 8 binaries (the compiler, R6's exporter, the checker, the glue,
both audit programs, the diagnosis program), bridge `64585867` with its instrumented `Tactic.lean` and patch, the control-5 labels,
R6-015's plan, and the seals and consumed artifacts of its 108 sources. Writing it refuses unless the step-3 record names the plan
and `mutations.py`, the labels verify, and both audit programs match their locks.

## For the implementation review

1. **Control 5's rule over classifications**, giving 12 expected passes (above).
2. **Control 9's two extra hypotheses** and its checker verdicts, frozen from the dry runs.
3. **The diagnosis:** the audit's atoms; kernel confirmation for meta-level defeq; the three limits of an export. If the
   attribute limit matters for the question, the alternative is a diagnosis run in the site's own environment. That would be a
   change to the approved section 4, which says the program reads the export; it is not done.
4. **No pinned rehearsal.** R6-015 had two approved; R6-016 admits none and rehearses on synthetic goals only.
5. **The residual is printed by v2's program**, as control 8 then audits with it; v1's program is bound and does not run.

## Next, after approval

1. Write the lock (`replay_campaign.py lock --plan r6-015/plan.json`) and commit it.
2. Replay the 108 episodes into `r6-016-runs/`, about two hours, offline; then control 3, control 9, control 8, the l070
   diagnosis and the analysis, each under the lock.
3. Record R6-016.
