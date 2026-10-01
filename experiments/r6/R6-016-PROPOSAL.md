# R6-016 proposal — an axiom-preserving final step for the refused certificates

Status: research-design proposal, **revision 2**, 2026-10-02, against `main` at `3eb438a5`, for review. It responds to
[the review of revision 1](reviews/2026-10-02/R6-016-AND-AUDIT-AMENDMENT-1-REVIEW.md) (`ac5f7fec`), whose P2 for this proposal
concerned the diagnosis: an unsuccessful equality proof stays unresolved (section 4). The review confirmed the normalizer choice:
`posOfLinearNum` has exactly `propext` and `Quot.sound`, and the cast/product identity closes by `rfl`. It is not implemented, not
locked and not run.
- **It does not amend** [R6-015](R6-015.md), the [qualification audit](R6-QUALIFICATION-1-ADDENDUM-1.md) or R6-014. Their results
  and definitions stay as recorded.
- **The audit amendment it uses for control 8** is proposed separately, in
  [R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-PROPOSAL.md](R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-PROPOSAL.md). That amendment is reviewed
  and locked on its own.
- **Approval of both drafts precedes implementation and replay.**
- **No provider, credential, reservation or spending** is involved at any stage.

## The question

**Under R6's full acceptance, can the constrained route consume the 36 certificates retained at l166, l175, l178 and l204, once
its final step no longer adds an axiom?** R6's full acceptance means two checks:
- every axiom is in the allowlist;
- no axiom is added to any target.

R6-015 answered the first part of this question. All 36 became kernel-accepted proofs, and l178 and l204 were consumed and
validated. Two things stopped l166 and l175:
- **acceptance 4.** The final step's normalizer (`Lean.Grind.CommRing`) adds `Classical.choice`, and those obligations' original
  proofs avoid it;
- **control 8 at l175.** The audit program could not locate the whole target.

R6-016 changes the first. The second is the separate audit amendment's. Either outcome is reportable: the boundary is removed, or
what remains is documented exactly. The methods paper does not depend on which.

## What changes, and what does not

**Only the final step's normalizer and its proof term change.** Everything else is R6-015's, as approved:
- selection by the goal's carrier;
- fact assertion at `Int`;
- the fold;
- the two gates on the returned term (no hypothesis reached; the kernel accepts it, closed);
- the option, the receipt and the injection bypass;
- the harness pattern, the step-3 mutation sets and labels, and the plan's 108 episodes.

**R6-015's files and lock stay intact.** R6-016 gets a new bridge revision, its own directory (`experiments/r6/r6-016/`, copies of
R6-015's modules with the changes below) and its own lock.

## 1. The final proof term, frozen

A new theorem in `ProofBroker.TermMode`, replacing `posOfNormNum` on the constrained route:

```lean
theorem posOfLinearNum (ctx : Int.Linear.Context) (e : Int.Linear.Expr) (c : Int)
    (h : e.norm = .num c) (hc : 0 < c) : 0 < e.denote ctx := by
  rw [← Int.Linear.Expr.denote_norm, h]; exact hc
```

**The returned positivity term** is `@id (0 < s) (posOfLinearNum ctx e c (Eq.refl (Int.Linear.Poly.num c)) (decide-proof of 0 < c))`,
where:
- `s` is the fold's sum;
- `e` reifies `s` over the atoms in `ctx`;
- `c` is the numeral `e.norm` evaluates to.

The kernel evaluates `e.norm` to check `Eq.refl`. The fold is `farkasContradictN s sumProof hpos`, unchanged. The gates check
exactly this term, as in R6-015.

**This was spiked on synthetic goals before drafting**, on Lean 4.32.0:
- `posOfLinearNum` depends on `propext` and `Quot.sound` only. Core's `Int.Linear.Expr.denote_norm` does too, while
  `Lean.Grind.CommRing.Expr.denote_toPoly` adds `Classical.choice`;
- the kernel evaluates `e.norm` by `rfl`;
- a cast of a product and a product of casts are accepted as one atom by definitional unfolding;
- `x * y` and `y * x` are rejected as one atom.

## 2. The axiom gates, checked separately

1. **The allowlist:** every target's axioms are among `propext`, `Classical.choice` and `Quot.sound`.
2. **Unchanged:** no axiom is added, against the site's frozen expected targets, local and whole. Each target's delta is reported.

**Consumed and validated** requires both, as in R6-015. The analysis reports the two gates separately, per episode and per target.

**The pre-lock gates:**
- `#print axioms` of `posOfLinearNum` must be exactly `propext, Quot.sound`. The bridge tests pin this.
- Every other lemma the route uses must depend on no axiom beyond `propext` and `Quot.sound`. These were checked before drafting:
  - the `TermMode` wrappers, shims and fold lemmas;
  - core's `Int.ofNat_le`, `Int.lt_of_not_ge`, `Int.mul_nonpos_of_nonneg_of_nonpos`, `Int.add_nonpos`, `Decidable.byContradiction`
    and `of_decide_eq_true`.

  The bridge tests will pin them too. **A correction comes with this:** `TermMode.lean`'s docstrings call these lemmas axiom-free.
  On 4.32.0 most depend on `propext`, and `notLe*ToLe0` also on `Quot.sound`. The new revision corrects the docstrings.

**The prediction: no axiom delta at any site.** Every planned site's original axioms include `propext` and `Quot.sound`
(`tasks/census-v1/*/expected.json`):

| sites | original axioms, local / whole | predicted delta |
|---|---|---|
| l069, l070, l071, l078, l178, l204 | all three / all three | none |
| l096, l099 | `propext`, `Quot.sound` / the same | none |
| l166, l170, l175 | `propext`, `Quot.sound` / all three | none |

## 3. Atom identity, frozen

The sum is reified into `Int.Linear.Expr`: `num`, `var`, `add`, `sub`, `neg`, `mulL k`, `mulR k`.

1. **Linear structure.** `+`, `−` and negation at `Int` are interpreted. So are numerals, including negative ones, and `^` with a
   numeral base and a numeral exponent, which evaluates to a numeral. A product with a numeral on either side becomes `mulL` or
   `mulR`.
2. **Casts.** A cast of a ℕ term (`Nat.cast`, `NatCast.natCast`, `Int.ofNat`) is pushed through ℕ `+`, ℕ numerals, `Nat.succ`, ℕ
   `*` with a numeral factor, and ℕ `^` with numeral base and exponent. Truncated subtraction, division and every other ℕ term stay
   under the cast, as atoms.
3. **Products of two non-numeral factors are atoms.**
   - A cast of a ℕ product is first rewritten, at the meta level only, as the product of the casts in the same order. The kernel
     accepts `↑(a * b)` as `↑a * ↑b` by unfolding.
   - Two product atoms are the same atom only if they are definitionally equal at instance transparency, factors in the same
     order. **There is no commutativity**, so `↑a * ↑b` and `↑b * ↑a` are distinct, and no associativity.
4. **Every other term is an atom.** Two atoms are the same if they are definitionally equal at instance transparency, which
   unfolds instances and `@[reducible]` definitions.
5. **Every identification is rechecked** by the kernel gate before the closer returns.

**Per-map predictions.** These were made by reading R6-015's recorded residuals, its already published results, not by running
anything new.

| map (both sources unless noted) | non-numeral products in the sum | prediction |
|---|---|---|
| l166, learned; l166, deterministic | none (the deterministic map has `↑Zmax * 0`, a numeral product) | normalizes; consumed and validated |
| l175, learned; l175, deterministic | `↑Zmax * zhigh`, twice, in the same order | normalizes, **provided** the two occurrences are definitionally equal at instance transparency (R6-015's ring normalizer identified their factors). This is one of two places where losing commutativity or associativity could matter; R6-015's residuals show the same order |
| l178, l204 | none | normalizes; consumed and validated |
| l069; l071 (both maps and the deterministic one); l070, draws 1–4 and 6–8, and its deterministic map | numeral products only (`2 * Zmax`, `Zmax * 2 ^ 16`, `2 ^ 24`) | normalizes |
| l078 | `Zmax * zhigh.val` under casts, in the same order | normalizes, with the same proviso as l175 |
| l070, draw 5's map | `↑Zmax * ↑zhigh.val`, twice, printed identically, but distinct even at instance transparency in R6-015 | **no fixed prediction**; see section 4 |
| l096, l099 | none | normalizes |
| l170 (control 4) | none (`hzh0` and `neg_goal`) | the sum is the constant 0, "not positive", as frozen |

**Whether l175 counts** also needs the audit amendment's control 8. Its acceptance-4 prediction above is independent of that.

## 4. A bounded diagnosis of l070 draw 5

**A frozen program, run under R6-016's lock after the replay,** so that it cannot inform the atom rules. It reads one input: R6's
retained l070 draw 5 export (`cohort-live-v9/l070-draw5/solution.ndjson.gz`, bound by `live-evaluation-v3`), in which the
qualification audit first saw the split.

**It locates every pair of atoms** in the export's `0 < s` that print identically under the default options but are not
syntactically equal. For each pair it records every attempt, in order:
1. **printed similarity:** equality under the default printer, and under `pp.all`;
2. **syntactic identity:** `Expr` equality after instantiating metavariables, and equality up to metadata. Where they differ, the
   first differing subterm: its path, and both sides under `pp.all`;
3. **definitional equality:** at reducible, instance and default transparency (zeta-delta reported), and in the kernel, checked by
   adding `a = b := rfl` closed over its variables;
4. **arithmetic equality:** a hypothesis-free proof of `a = b` in an empty context, by `omega` and, separately, by ring
   normalization, each kernel-checked. This is diagnosis, so any normalizer may be used, and none of it enters the route;
5. **a counterexample:** the free variables are instantiated at the numerals 0 to 3, and each instance of `a ≠ b` is decided by
   closed evaluation, kernel-checked.

**Every attempt in 3 to 5 records one of these outcomes:**
- `established` (a kernel-accepted proof);
- `refused` (the tactic or the kernel rejected the statement as outside what it handles, with its message);
- `resource_exhausted` (heartbeats or time, with the limit);
- `unsuccessful` (the attempt ran to completion without a proof).

Only `established` counts as evidence. A failed proof is not a proof of the opposite.

**The output** is one classification per pair, from established evidence only:
- `identical`: syntactically equal;
- `printed_only`: syntactically different, definitionally equal at the first transparency reported, or in the kernel;
- `arithmetically_equal`: not established definitionally equal, with an established proof of `a = b`;
- `distinct`: an established, kernel-checked counterexample;
- `equality_not_established`: none of the above. This is unresolved, and not a claim that the terms differ.

**"Syntactically distinct" is only an observation** in item 2, never a classification of mathematical distinctness.

The result is recorded with R6-016's. Any route change it suggests is a separate proposal.

## 5. Controls

**Inherited from R6-015,** with the same plan, frozen expectations and definitions:
1. the 24 injected invalid mutations: rejected by the checker, and failing in the final step because the sum does not cancel;
2. the 25 valid mutations: consumed and validated;
3. the review's synthetic probe;
4. l170: the checked proposals rejected, the injected one "not positive";
5. the 14 regression entries;
6. selection;
7. the reference route, cited.

**Control 8** uses the amended audit program (`qualification-audit-v2`, once approved and locked) in real mode, under the same
frozen predicate. **If the amendment is not approved,** control 8 uses `qualification-audit-v1`, and l175's whole target is expected
to stay unlocatable. That is stated now, not chosen later.

**Control 5's labels** are computed by R6-015's frozen rule from the qualification audit's classifications as recorded at R6-016's
lock: addendum 1, and the amendment's addendum 2 if it exists by then. The rule is stated now, before either runs.

**New: control 9, the normalizer,** synthetic and run under the lock through R6's helpers, as control 3 is:
- **9a, the axiom gate:** `posOfLinearNum` depends on exactly `propext` and `Quot.sound`. A synthetic proof through the route, at a
  goal whose `omega` proof avoids `Classical.choice`, adds no axiom.
- **9b, no commutativity:** a certificate whose cancellation needs `x * y = y * x` fails, the sum not cancelling.
- **9c, product identity:** the same product in the same order cancels, and `↑(a * b)` against `↑a * ↑b` cancels.
- **9d, numeral products:** `c * (a − b)`, `a * 0` and `Zmax * 2 ^ 16` normalize.
- **9e, ℕ nonnegativity is not used:** `m < m + n + 1` with `neg_goal` alone fails; with `_pb_nonneg_n` it closes.
- **9f, a hypothesis reached through the sum is still refused:** the build review's cast instance.

**The amended audit's own controls** (renaming, parameters through `let`, and C1 to C9 again) belong to the amendment.

## 6. The analysis

**R6-015's frozen analysis, with these changes:**
- the axiom gates reported separately (section 2);
- control 9 verified and recomputed, as control 3 is;
- control 8 against the program the lock names;
- the diagnosis's record verified by identity, provenance and recomputation.

**The outcome definitions are R6-015's:**
- **complete success** needs all 36 consumed and validated, controls 1, 2, 3, 4, 6, 8 and 9 as frozen, and control 5's expected
  passes;
- **none** means no retained certificate consumed and validated;
- **partial** is anything else, with the reasons stated.

**Failures after a proof** (acceptance or audit) are listed for diagnosis, which closes the gap R6-015's record disclosed.

## 7. Order

1. **Review** this proposal and the audit amendment.
2. **Implement** the bridge revision: `posOfLinearNum`, the `Int.Linear` reifier with the atom rules, and the docstring correction.
   The tests are synthetic, including control 9's cases and the axiom pins. Review.
3. **The audit amendment** follows its own order: build, controls, lock `qualification-audit-v2`, its applications.
4. **The R6-016 harness:** R6-015's, copied, with the bridge revision, control 9, the diagnosis program and the analysis changes.
   Rehearsed on synthetic goals only. Review.
5. **Lock** `r6-016-replay-v1`: the plan, the step-3 record, the labels, the programs and both audit programs' digests.
6. **Replay** the 108 episodes; then control 3, control 9, control 8, the l070 diagnosis and the analysis; then record R6-016.

## What each outcome would mean

- **Complete success.** R6's refusal at the four obligations is removable under R6's full acceptance: selection by goal carrier,
  fact assertion at `Int`, and a hypothesis-free, axiom-preserving final step.
- **Partial or none.** The record locates what remains, per obligation, map and class. Candidates include:
  - product identity at l175 or l078;
  - the l070 split;
  - the audit's locatability;
  - something not yet seen.

**In every case,** R6-014 and R6-015 are unchanged. R6-016 is reported on its own, never pooled.

## Scope and cost

- **Offline and CPU only.** About two hours of replay, as R6-015 took.
- **New files and a new bridge revision only.** R6's and R6-015's runs, records and locks are untouched.
- **Generality.** As for R6-015: four obligations, in two families of one file.
