# R6-015 proposal — consuming the refused certificates, offline

Status: research-design proposal, 2026-09-30, against `1f694b65` (tag `r6`). It is not frozen, not implemented, and not an amendment
to R6-014. R6-014's result stands as recorded ([synthesis](R6-SYNTHESIS.md)).
- **No provider, credential, reservation or spending** is involved at any stage.
- No R6 run, record, policy or lock is changed.

## The question

**Can an appropriate closer construct kernel-validated proofs from the certificates R6 retained at the four obligations its pinned ℕ
closer refused: l166, l175, l178 and l204?**

The question is about *consumption*: whether the verified witness becomes the proof. It is not about re-proving the goal by other
means.

## Why this is the question R6 leaves

In R6-014 these four obligations received verified witnesses at every draw: 32 slots. The pinned closer refused every one with
`nat_closer_int_goal`.

The reference route (`site_cvc4_default_closer_v1`) closed all four through `gated_omega`. That route re-runs `omega` on the original
goal once a certificate is accepted (`lean-bridge/ProofBroker/Tactic.lean`: "omega re-proves the ORIGINAL goal"). It shows the
obligations are provable, which was never in doubt, since each is an `omega` site in the original file. It does not show that a
retained certificate is usable.

R6 therefore measured a boundary without locating it. Is "closer-unreachable" a property of these obligations, of their
certificates, or only of which closer was selected?

## What is actually being tested

**Units.** Four obligations.
- **Learned certificates:** the 32 slots hold **4 distinct witnesses**. Each site returned the same raw witness at all eight draws.
- **Deterministic certificates:** the frozen deterministic arm recovered one certificate per site
  (`census-runs/deterministic-v1/site_cvc4_term_mode_v1/<site>/events.ndjson`, receipt `recovery_finished`). It is an independent
  source.

| obligation | family | learned witness (all 8 draws) | deterministic witness | same up to positive scaling? |
|---|---|---|---|---|
| l166 | `cell_value_neutral` | `hlt` 1, `neg_goal` 1 | `hrec` −3, `hlt` 1, `neg_goal` 1 | no |
| l175 | `cell_value_neutral` | `hrec` −1, `hz0` 1, `this` 1, `neg_goal` 1 | `hrec` −3, `hz0` 3, `this` 3, `neg_goal` 3 | yes (×3) |
| l178 | `cell_value_neutral` | `this` 1, `this_1` 1, `neg_goal` 1 | the same | yes |
| l204 | `Row.s1_noninc` | `hab` 1, `neg_goal` 1 | the same | yes |

The evidence is therefore at most **4 obligations, in 2 families, and 5 distinct witnesses**: the four learned, plus the
deterministic arm's different witness at l166. Every result is reported in those units, beside the 36 certificate replays: 32
learned and 4 deterministic.

A negative multiplier appears only on an equation (`hrec` is `v = z + ↑Zmax * zhigh` at l175). Multipliers on inequalities are
nonnegative, as a Farkas certificate requires.

## The refusal, from the pinned code

At the `r6` tag, `lean-bridge/ProofBroker/Tactic.lean`:
- **Mode selection.** `natModeOf` (line 2102) puts an extraction in ℕ mode when any free variable has type `Nat`, or any ℕ atom
  payload exists.
- **The ℕ closer.** In ℕ mode, term mode calls `closeNatViaTermMode` (line 3456). Its goal matcher, `matchNatGoal?` (line 3382),
  accepts only comparisons at `Nat`.
- **The four goals** are comparisons at `Int` whose extractions contain ℕ variables. At l175, for example, the goal is `↑Zmax ≤ v`,
  with `Zmax v0 : Nat` and `v z zhigh : Int`, so ℕ mode is selected and the matcher refuses.
- **The ℤ closer.** `closeViaTermMode` (line 3357) accepts `Int` comparisons, but it is not reached in ℕ mode. ℕ mode's fact
  assertion, `assertNatWitnessFacts` (line 3407), accepts only `_pb_nonneg_*` names or ℕ-shaped local hypotheses, which it casts.
  At l175 every hypothesis the witness names (`hrec`, `hz0`, `this`) is already at `Int` in the extraction.

The current code has no path for a ℤ goal in a mixed-carrier context.

The R6 episodes build the bridge from the pinned revision `e627efe` with the frozen overlay (`policies/site-broker-v1.json` binds
the overlay sources by digest). R6-015 therefore needs a **new pinned bridge revision and a new harness version**. R6's pins and
locks stay as they are, and must still verify at the `r6` tag.

## The proposed route

**The route is specified, reviewed and frozen before any retained certificate is replayed.** It is a mixed-carrier term-mode
closer:
1. **Select by the goal's comparison carrier.** An `Int` comparison takes the existing ℤ wrappers (`intLeViaLt` / `intLtViaLe`),
   even when the extraction contains ℕ variables. A `Nat` comparison keeps the ℕ path unchanged.
2. **Assert every witness-named fact at `Int`:**
   - a local hypothesis already at `Int`, as it stands;
   - a ℕ-shaped hypothesis, through the existing `natCast*` shims;
   - an IR `_pb_nonneg_*` fact, through `natCastNonneg`;
   - any other name is an error. The closer fails closed; it never guesses.
3. **Fold with the witness's multipliers** through the existing `closeViaTermModeFalse`. This is the same fold both R6 closers use,
   ending in `omega` only on the literal positivity subgoal between numerals.

**Forbidden:** `omega`, `decide`, `simp` or any other tactic on the goal or on its hypotheses, and any fallback.

The route is correct only if it **consumes the witness or fails**. The controls below make that checkable.

## Acceptance

The predicates are R6's, unchanged:
1. the independent checker verifies the certificate (re-checked from the retained record);
2. the selected closer's consumption receipt names this certificate and this closer, by the R6-013 receipt standard;
3. local and whole-declaration kernel replays succeed;
4. the axioms are unchanged: only `propext`, `Classical.choice` and `Quot.sound`.

## Controls

1. **Load-bearing witness.** For each distinct witness, the closer must **fail, never close**, under each of:
   - one multiplier altered;
   - an inequality multiplier made negative;
   - a named hypothesis dropped;
   - an extra hypothesis added with a nonzero multiplier that breaks the combination.

   This distinguishes consumption from re-proof.
2. **Negative control.** l170's rows are satisfiable, so no certificate exists. Its retained proposals are rejected by the checker
   before any closer. A well-formed but invalid witness forced into the new closer at l170 must fail.
3. **Regression.** The six proved obligations (l069, l070, l071, l078 at ℕ; l096, l099 at ℤ) must close under the new selection
   rule with their original closers named, and their proof exports must be byte-identical to R6's where the route is unchanged.
4. **Selection guard.** A `Nat` comparison in a mixed context still takes the ℕ closer. An `Int` comparison with no ℕ variables
   takes the ℤ closer exactly as today.
5. **Separate control, not pooled.** The reference route's `gated_omega` closures are cited from R6-014 as the provability
   baseline. They are never counted as consumption.

## Freezing and order

1. **Review this proposal.**
2. **Implement** the closer and the selection rule in a new bridge revision, with unit tests on **synthetic** mixed-carrier goals.
   These are written from this specification: an `Int` goal over ℕ casts, with `Int` and ℕ hypotheses and an opaque `Int` atom.
   - The four sites' *shapes* define the requirement and may be studied.
   - The retained certificates are **not** replayed through any candidate closer before the lock.
   - Review.
3. **Lock** the bridge revision, the replay harness, the controls and the analysis, as a new R6-015 lock, before any retained
   certificate is replayed.
4. **Replay offline** each of the 36 certificates through the frozen route, as sealed site-harness episodes with receipts:
   - one replay per retained learned certificate (32);
   - one replay per deterministic certificate (4);
   - the controls.
5. **Audit and analyse** with frozen programs:
   - per obligation (4) and per distinct witness (5);
   - per certificate (36), by source.
6. **Record** the result.

## What each outcome would mean

- **All four obligations consumed and validated.** "Closer-unreachable" in R6 was a property of closer selection at the `r6` tag,
  not of the obligations or their certificates.
  - The deterministic arm's certificates verified at the same four sites, so **both arms are expected to move together**. The
    learned arm's marginal gain over the deterministic arm is expected to remain l096 and l099.
  - R6-015 tests the reconstruction boundary, not the learned arm's value.
- **Some consumed.** The failures are classified from bound evidence as:
  - selection;
  - fact assertion, including casts and opaque atoms;
  - the fold;
  - the kernel.

  The result is a located boundary.
- **None consumed.** The gap is more than selection, and the record says where.

In every case, R6-014's result is unchanged. R6-015 is reported separately, under its own route, and never pooled with R6's
numbers.

## Scope and cost

- **Offline and CPU only.** Kernel replays at R6's measured scale: seconds to minutes per episode.
- **No provider, credential, reservation, ledger entry or spending.**
- **New files and a new bridge revision only.** R6's runs, records, policies and locks are untouched: `live-evaluation-v1/v2/v3`,
  `analysis-v3`, `cohort-harness-v9` and `site-broker-v1`.
- **Generality.** A positive result speaks to these four obligations, in two families of one file. A claim about closers in
  general needs a second consumer.
