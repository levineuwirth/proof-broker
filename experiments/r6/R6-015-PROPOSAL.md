# R6-015 proposal — consuming the refused certificates, offline

Status: research-design proposal, **revision 3**, 2026-09-30, against `1f694b65` (tag `r6`). Revision 2 responded to
[the review of revision 1](reviews/2026-09-30/R6-015-PROPOSAL-REVIEW.md), which found two P1 and three P2 issues. Revision 3 corrects
what a failed regression control may be taken to show, per [the review of R6 qualification 1](reviews/2026-09-30/R6-QUALIFICATION-1-REVIEW.md). It is not frozen,
not implemented, and not an amendment to R6-014. R6-014's result stands as recorded ([synthesis](R6-SYNTHESIS.md)).
- **No provider, credential, reservation or spending** is involved at any stage.
- No R6 run, record, policy or lock is changed.

## The question

**Can a closer, suited to their goals and constrained to consume the certificate, construct kernel-validated proofs from the
certificates R6 retained at the four obligations its pinned ℕ closer refused: l166, l175, l178 and l204?**

"Consume" is the point, and revision 1 did not pin it down. A proof counts only if the certificate's multipliers alone discharge
the contradiction. No tactic may draw on the goal's context to repair a combination that does not cancel. The fold R6 used does not
enforce this; see "The fold must enforce consumption".

## Why this is the question R6 leaves

In R6-014 these four obligations received verified witnesses at every draw: 32 slots. The pinned closer refused every one with
`nat_closer_int_goal`.

The reference route (`site_cvc4_default_closer_v1`) closed all four through `gated_omega`. That route re-runs `omega` on the original
goal once a certificate is accepted. It shows the obligations are provable, which was never in doubt, since each is an `omega` site
in the original file. It does not show that a retained certificate is usable.

R6 therefore measured a boundary without locating it.

## Units, and the equivalence relation

Three notions of "the same witness", used separately throughout:
- **Raw proposal:** the ordered coefficient list exactly as retained.
- **Coefficient map:** hypothesis name → integer multiplier, with order ignored and zero entries dropped.
- **Witness class:** a coefficient map modulo positive scaling, normalized by dividing by the gcd of the absolute multipliers.

| obligation | family | learned: 8 proposals | deterministic (frozen arm, `recovery_finished` receipt) | same class? |
|---|---|---|---|---|
| l166 | `cell_value_neutral` | 1 ordering, 1 map: `hlt` 1, `neg_goal` 1 | `hrec` −3, `hlt` 1, `neg_goal` 1 | no, syntactically; `hrec` is redundant (below) |
| l175 | `cell_value_neutral` | **4 orderings**, 1 map: `hrec` −1, `hz0` 1, `this` 1, `neg_goal` 1 | the same ×3 | yes |
| l178 | `cell_value_neutral` | 1 ordering, 1 map: `this` 1, `this_1` 1, `neg_goal` 1 | identical map | yes |
| l204 | `Row.s1_noninc` | 1 ordering, 1 map: `hab` 1, `neg_goal` 1 | identical map | yes |

**Counts:**
- learned, across the 32 accepted proposals: **7 raw orderings, 4 coefficient maps, 4 classes**;
- both sources: **6 coefficient maps, 5 classes**;
- **4 obligations, in 2 families.**

At l166, the deterministic arm's extra entry is `hrec : z = z + ↑Zmax * 0`. Its emitted row has no terms and constant 0, so the −3
multiplier contributes nothing. It is a distinct map and a distinct class syntactically, but **not a distinct mathematical
argument**. Dropping it yields the learned map.

A negative multiplier appears only on an equation. Multipliers on inequalities are nonnegative, as a Farkas certificate requires.

Every retained certificate is replayed as retained: 32 learned and 4 deterministic. Results are reported per obligation (4), per
map (6) and per class (5), never merging the units.

## The refusal, from the pinned code

At the `r6` tag, `lean-bridge/ProofBroker/Tactic.lean`:
- **Mode selection.** `natModeOf` (line 2102) puts an extraction in ℕ mode when any free variable has type `Nat`, or any ℕ atom
  payload exists.
- **The ℕ closer.** In ℕ mode, term mode calls `closeNatViaTermMode` (line 3456). Its goal matcher, `matchNatGoal?` (line 3382),
  accepts only comparisons at `Nat`.
- **The four goals** are comparisons at `Int` whose extractions contain ℕ variables. At l175, for example, the goal is `↑Zmax ≤ v`,
  with `Zmax v0 : Nat` and `v z zhigh : Int`, so ℕ mode is selected and the matcher refuses.
- **The ℤ closer.** `closeViaTermMode` (line 3357) accepts `Int` comparisons, but it is not reached in ℕ mode. ℕ mode's fact
  assertion, `assertNatWitnessFacts` (line 3407), accepts only `_pb_nonneg_*` names or ℕ-shaped local hypotheses. At l175 every
  hypothesis the witness names is already at `Int` in the extraction.

The R6 episodes build the bridge from the pinned revision `e627efe` with the frozen overlay (`policies/site-broker-v1.json` binds
the overlay sources by digest). R6-015 therefore needs a **new pinned bridge revision and a new harness version**. R6's pins and
locks stay as they are, and must still verify at the `r6` tag.

## The fold must enforce consumption

The review found this (P1) and reproduced it. **The existing fold does not check literal positivity between numerals.**
- `closeViaTermModeFalse` (line 3228) builds the weighted sum `s` and a proof of `s ≤ 0`.
- It then discharges `0 < s` by `omega` through `closeOmegaSubgoal` (lines 3206 and 3275–3279).
- That subgoal is created in the goal's full context: `s` is symbolic, and every hypothesis is in scope.

Its docstring's "narrower than a goal-side omega call" overstates what the code enforces. The review's synthetic probe, an unchanged
copy of the fold, shows the consequence. For `h : x ≤ y ⊢ x ≤ y`, the valid multipliers (`h` 1, `neg_goal` 1) and the invalid
(`h` 1, `neg_goal` 2) **both close**. The second does not cancel its variables, and contextual `omega` supplies the missing argument.

**R6-015's route therefore replaces the final step.** The weighted sum is normalized **hypothesis-free**: ring normalization of the
linear combination, with no local hypothesis available. The implementation may clear the context or use a reflective normalizer.
The result must be a **numeral**. Its positivity is then checked by **closed evaluation**, `decide` on a literal.
- If the variables do not cancel, the closer **fails**.
- If the numeral is not positive, it fails.

Nothing else discharges the contradiction.

## What this finding means for R6

The finding concerns **consumption attribution**. It does not concern kernel soundness, or the acceptance of invalid certificates:
- R6's independent checker verified every certificate it passed to a closer, and that check is exact cancellation;
- the 48 proofs are sound, and their combinations are valid.

But R6-013 §3 and the synthesis describe the closers as consuming the witness through a fold "ending in `omega` on the literal
positivity subgoal", and the ladder's "consumed" stage rests on that. In R6, "consumed" therefore means *the closer folded this
verified certificate and the kernel accepted the result*. It does not mean *the certificate alone discharged the contradiction*,
because the closer did not enforce that.

The qualification is recorded in [R6 qualification 1](R6-QUALIFICATION-1.md). R6-015's regression control (below) tests whether
R6's proved certificates also *suffice* under the constrained fold. How R6's own proofs were built is settled only by a dependency
audit of their retained proof terms.

## The proposed route

It is specified, reviewed and frozen before any retained certificate is replayed:
1. **Select by the goal's comparison carrier.** An `Int` comparison takes the existing ℤ wrappers (`intLeViaLt` / `intLtViaLe`),
   even when the extraction contains ℕ variables. A `Nat` comparison keeps the ℕ path's selection.
2. **Assert every witness-named fact at `Int`:**
   - a local hypothesis already at `Int`, as it stands;
   - a ℕ-shaped hypothesis, through the existing `natCast*` shims;
   - an IR `_pb_nonneg_*` fact, through `natCastNonneg`;
   - any other name is an error. The closer fails closed.
3. **Fold with the witness's multipliers,** as `closeViaTermModeFalse` does. Then apply the **constrained final step** from the
   previous section in place of contextual `omega`.

**Forbidden:** `omega`, `decide`, `simp` or any other tactic on the goal, on its hypotheses, or on any subgoal with hypotheses in
scope. There is no fallback.

## Acceptance

The predicates are R6's, strengthened only in the final step:
1. the independent checker verifies the certificate, re-checked from the retained record;
2. the selected closer's consumption receipt names this certificate, this closer and the constrained final step;
3. local and whole-declaration kernel replays succeed;
4. the axioms are unchanged: only `propext`, `Classical.choice` and `Quot.sound`.

## Controls

Every mutation is fixed in advance, and **its validity is established independently**, before any closer runs. Two checks are made,
and both must agree:
- **exact rational arithmetic** over the retained emitted rows: does the weighted sum cancel every variable and leave a false
  constant comparison?
- **R6's independent checker.**

**1. Invalid mutations,** tested at two points. For each of the 6 coefficient maps, the frozen invalid set is:
- `neg_goal` doubled, the review's pattern;
- one load-bearing inequality multiplier doubled, where the arithmetic confirms that it breaks cancellation;
- one load-bearing hypothesis dropped;
- an unrelated in-scope inequality added with multiplier 1, where the arithmetic confirms that it breaks cancellation.

Each is tested at both points:
- **(a) checker rejection;**
- **(b) deliberate injection into the closer,** bypassing the checker.

The closer must fail on every one. Checker rejection alone says nothing about consumption.

**2. Validity-preserving mutations, as positive controls:**
- the whole map scaled by 2 and by 3;
- entries reordered;
- a zero-multiplier entry added;
- at l166, the redundant `hrec` entry dropped from the deterministic map, which yields the learned map.

The arithmetic confirms each stays valid. Each is injected into the closer, and each must succeed, with a receipt and kernel
acceptance.

**3. The review's synthetic probe:** `h : x ≤ y ⊢ x ≤ y` with (`h` 1, `neg_goal` 2). It must **fail** under the constrained fold.
Its closing under the pinned fold is recorded as the documented difference.

**4. Negative control.** l170's rows are satisfiable, so no certificate exists. Its retained proposals are rejected by the checker.
A well-formed but invalid witness injected into the closer at l170 must fail.

**5. Regression, and the R6 check.** The six proved obligations (l069, l070, l071, l078 at ℕ; l096, l099 at ℤ):
- each distinct map retained for them is replayed through the constrained fold;
- each must close, with its original closer named.

This measures whether R6's consumed certificates pass a hypothesis-free check. **Passing** establishes that the certificate suffices under
the new route. **Failing** requires diagnosis and is not, by itself, evidence that R6's proof relied on its context. The constrained fold may change proof terms, so
byte-identity with R6's exports is not required. Axioms must be unchanged.

**6. Selection guard.** A `Nat` comparison in a mixed context still takes the ℕ closer. An `Int` comparison with no ℕ variables
takes the ℤ closer.

**7. Separate control, not pooled.** The reference route's `gated_omega` closures are cited from R6-014 as the provability
baseline. They are never counted as consumption.

## Freezing and order

1. **Review this revision.**
2. **Implement** the selection rule, the fact assertion and the constrained final step in a new bridge revision, with unit tests on
   **synthetic** mixed-carrier goals. These are written from this specification: an `Int` goal over ℕ casts, with `Int` and ℕ
   hypotheses and an opaque `Int` atom, and with the review's probe included.
   - The four sites' shapes define the requirement and may be studied.
   - The retained certificates are **not** replayed through any candidate closer before the lock.
   - Review.
3. **Compute the mutation sets and their validity labels** (exact arithmetic, and the checker) from the retained rows. Record them.
4. **Lock** the bridge revision, the replay harness, the mutation sets, the controls and the analysis, as a new R6-015 lock, before
   any retained certificate is replayed.
5. **Replay offline** as sealed site-harness episodes with receipts:
   - the 32 learned and 4 deterministic certificates;
   - the mutation sets;
   - the controls.
6. **Audit and analyse** with frozen programs: per obligation, per map and per class, by source.
7. **Record** the result.

## What each outcome would mean

- **Complete success.** All **6 coefficient maps**, both sources and all four obligations, including **both l166 maps**, are
  consumed and validated under the constrained fold, and every control behaves as frozen. This establishes that **the refusal was
  removable by the specified reconstruction changes**: selection by goal carrier, ℤ fact assertion, and a hypothesis-free final step.
  - It does **not** attribute success to selection alone. No selection-only arm is planned. If review wants one, it can only be
    descriptive, because the unconstrained fold cannot attribute consumption.
  - The deterministic arm's certificates are in the same classes at three sites, and valid at the fourth, so **both arms are expected
    to move together**. The learned arm's marginal gain over the deterministic arm is expected to remain l096 and l099.
  - R6-015 tests the reconstruction boundary, not the model's value.
- **Partial.** The failures are classified from bound evidence as:
  - selection;
  - fact assertion, including casts and opaque atoms;
  - the fold;
  - the constrained final step;
  - the kernel.

  The result is a located boundary, reported per obligation, map and class.
- **None.** The gap is more than these changes, and the record says where.
- **Regression control 5 fails for an R6-proved certificate.** This requires diagnosis. The cause could be incomplete cast
  normalization in the constrained step, an implementation defect, or dependence of R6's proof on its contextual step. Only an audit
  of R6's retained proof term (`solution.ndjson.gz`) can establish the last; see [qualification 1](R6-QUALIFICATION-1.md).

In every case, R6-014's result is unchanged. R6-015 is reported separately, under its own route, and never pooled with R6's
numbers.

## Scope and cost

- **Offline and CPU only.** Kernel replays at R6's scale: seconds to minutes per episode. The mutation sets add tens of episodes.
- **No provider, credential, reservation, ledger entry or spending.**
- **New files and a new bridge revision only.** R6's runs, records, policies and locks are untouched: `live-evaluation-v1/v2/v3`,
  `analysis-v3`, `cohort-harness-v9` and `site-broker-v1`.
- **Generality.** A positive result speaks to these four obligations, in two families of one file. A claim about closers in
  general needs a second consumer.
