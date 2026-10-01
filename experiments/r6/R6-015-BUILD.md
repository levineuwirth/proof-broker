# R6-015 — build, for implementation review

**Build revision 2**, 2026-10-01. It responds to [the implementation review of revision 1](reviews/2026-10-01/R6-015-BUILD-REVIEW.md),
which found one P2 defect. It accepted the five implementation choices, with one documentation request and two requirements on
the harness. Revision 1 is `4bcf4a18`. This is step 2 of [the proposal, revision 5](R6-015-PROPOSAL.md), whose design was
[approved for implementation](reviews/2026-10-01/R6-015-PROPOSAL-REVISION-4-REVIEW.md).

**Status:**
- **The bridge revision is `476fab31`.** It is `aa32cf21` (revision 1's) with the repair below.
- **Nothing is locked, and no retained certificate has been replayed.** None was read for this build. The mutation sets
  (step 3) are not computed.
- **Tests.**
  - The synthetic tests pass, with the new regression.
  - The existing `Test.Tactic` and `Test.TacticStress` pass on the new revision, with live solvers.
  - `Test.TacticMathlib` and the corpus walker suite were not run. Their paths are untouched, but that is unverified.
- **Control 8 was exercised again on synthetic proofs**, at `476fab31`
  ([record, revision 2](reviews/2026-10-01/R6-015-SYNTHETIC-AUDIT-PRELOCK-2.json)). The seven constrained pairs pass, and the two
  pinned contrast pairs fail. [Revision 1's record](reviews/2026-10-01/R6-015-SYNTHETIC-AUDIT-PRELOCK.json) is superseded, not
  invalid.
- `qualification-audit-v1` and `live-evaluation-v3` verify. R6's observation overlay (`site_broker.lean_edits`) applies to
  `476fab31`'s `Tactic.lean` unchanged.

## What changed

**P2: the gates checked a different term from the one returned.** Revision 1 checked `proof`, then returned
`mkExpectedTypeHint proof ty`, that is `@id (0 < sum) proof`. The annotation carries `sum`, which can reach a hypothesis that
`proof` does not. The review's case is a cast instance taking a hypothesis, `castViaHyp (_h : True) := instNatCastInt`:
- the reifier canonicalized the cast;
- the returned term referred to `tag` through its type;
- the locked audit reported `tag` at both targets, so control 8 failed.

**The repair** (`476fab31`):
- The typed term `hpos` is built first.
- The hypothesis gate and the kernel gate both check exactly `hpos`.
- `hpos` is returned unchanged, and the fold uses it as given: `mkApp3 farkasContradictN sum sumProof hpos`, with no
  re-elaboration.
- A hypothesis reached only through the sum now fails closed.

**The regression** is in `Test/TermModeConstrained.lean`: the review's goal, with `castViaHyp tag`, fails with
`the positivity proof reaches hypotheses [tag]`. The same goal with the standard cast closes.

**The production route was checked too, outside the committed tests.** With `proofBroker.term.constrained` set:
- the review's reproducer under `proof_broker_term [cvc4]` now fails closed with the same message;
- the plain goal closes, with the constrained route's axioms.

**Documentation.** Instance transparency is now described precisely, in `constrainedAtom` and below: it unfolds instances, and
also every `@[reducible]` definition.

## What was built

**An option, `proofBroker.term.constrained`, off by default.** With it off, every path is unchanged: the new behaviour sits behind
default-valued flags, and `runTermModeOnGoal` gains one branch. With it on, `runTermModeOnGoal` calls `closeConstrained` after the
certificate gate, the specialization check and the trace guard, all as before.

1. **Selection** (`closeConstrained`), by the goal's comparison carrier:
   - an `Int` comparison takes the ℤ closer, even in an extraction with ℕ variables (`closeMixedViaTermMode`);
   - a `Nat` comparison, or a `False` goal, in such an extraction keeps the ℕ closer;
   - Tier 2 case splits, polymorphic-α extractions and extension fragments **fail closed**.
2. **Fact assertion** (`assertNatWitnessFacts`, with `intAsIs`):
   - a local `Int` hypothesis is asserted as it stands;
   - a ℕ-shaped one goes through the `natCast*` shims;
   - an IR `_pb_nonneg_*` fact goes through `natCastNonneg`;
   - any other name is an error.
3. **The constrained final step** (`constrainedPositivity`, in place of `closeOmegaSubgoal`). The weighted sum is reified into
   core's `Lean.Grind.CommRing.Expr` over its atoms.
   - Core's normalizer must reduce it to a numeral, and `decide` must show the numeral positive.
   - The proof is `@id (0 < s) (TermMode.posOfNormNum ctx e c rfl (decide …))`, by reflection. The kernel evaluates the
     normalization.
   - Before returning, the closer fails closed twice, on exactly the term it returns:
     - the term must reach **no hypothesis**, following local definitions, as the audit's Check 1 does;
     - the kernel must accept it, closed over the variables it reaches.
   - The fold keeps the shape `farkasContradictN s sumProof hpos`, with `hpos`'s type literally `0 < s`.
4. **Atoms** are identified up to definitional equality at **instance transparency**, which unfolds instances and also every
   `@[reducible]` definition.
   - A cast to `Int` is pushed through ℕ `+`, `*`, literal powers and numerals, so a cast of a product and a product of casts are
     one monomial.
   - Truncated subtraction, division and other terms are atoms.
   - Any identification is rechecked by the kernel.
5. **A test-only tactic, `term_closer_test`**, injects a witness straight into the closers, bypassing dispatch and the checker
   (controls 1b and 3). It prepares and reifies the goal as `proof_broker_term` does, and logs the selected closer.

## Synthetic tests (`lean-bridge/Test/TermModeConstrained.lean`)

Every goal is written from the specification. `#guard_msgs` pins each selection and each failure message.

| case | constrained route |
|---|---|
| the required mixed-carrier case: an `Int` goal over ℕ casts, `Int` and ℕ hypotheses, an opaque `Int` atom (`z / 3`) | closes, `term_mode_int` |
| the same scaled ×2 and ×3, reordered, and with a zero entry | closes |
| `neg_goal` doubled; one multiplier doubled; one hypothesis dropped; an unrelated inequality added | each fails: the sum does not cancel, and the message gives the residual |
| **the required cast/product case**, in both directions | closes |
| the review's probe (`h` 1, `neg_goal` 2) | fails; **the pinned fold closes it** |
| `m < m + n + 1` with `neg_goal` alone | fails (residual `↑n + 1`); **the pinned fold closes it, from `n`'s nonnegativity**. With `_pb_nonneg_n` it closes |
| the ℕ closer with an `Int` hypothesis as it stands | closes, `term_mode_nat`; without the nonnegativity fact it fails |
| a combination summing to 0 | fails: not positive |
| selection guard (control 6): a `Nat` comparison in a mixed context, and an `Int` comparison with no ℕ variables | `term_mode_nat`, and `term_mode_int` |
| an unknown witness name | fails closed |
| **a cast instance taking a hypothesis** (the build review's case) | fails closed: reaches `tag`. The standard cast closes |
| axioms of one constrained proof, and of one pinned | pinned (below) |

## Control 8, on synthetic proofs

`r6-015/synthetic_audit.py` does the following:
- builds the bridge from `476fab31` in git, with Lean 4.32.0, and builds `r6-015/R6015AuditSynthetic.lean` against it;
- exports each local/whole pair with R6's pinned exporter;
- runs the audit program of `qualification-audit-v1` in `--synthetic` mode. Its digest, and the exporter's, are checked against
  that lock.

The predicate is revision 5's. Binding is `not_applicable_synthetic` in this mode.

| pair | route | local / whole classification | control 8 |
|---|---|---|---|
| c1–c7: mixed, scaled, cast/product both ways, ℕ with a nonnegativity fact, ℕ with an `Int` hypothesis, ℤ with unused hypotheses | constrained | `certificate_alone` / `certificate_alone` | **pass** |
| p1: the review's probe | pinned | `sufficiency_not_established`; refers to `h`, `neg_goal` | fails, as expected |
| p2: `m < m + n + 1`, `neg_goal` alone | pinned | `sufficient_but_context_referenced`; refers to `neg_goal` | fails, as expected |

**p2 shows the gap that revision 5 anticipates.** The audit's Check 2 establishes a sum that the constrained step refuses: `omega`
uses `n`'s nonnegativity. Check 2 is not part of control 8.

Every export's shared constants matched `Init`, core's ring normalizer included. The build review's case has no pair here: under
the repair, the constrained closer refuses it, so there is no proof to export.

## Axioms

- **The constrained route's proofs** depend on `propext`, `Classical.choice` and `Quot.sound`, through the normalizer's soundness
  proof (`posOfNormNum`).
- **The pinned fold's proofs** depend on `propext` and `Quot.sound`, through `omega`.

Both are within acceptance 4. The tests pin both.

**A correction, made in revision 1.** `8a64acde`'s docstrings implied that the pinned fold's proofs are axiom-free. `aa32cf21`
states the axioms as they are.

## Accepted in review, and what the harness must do

**The five choices were accepted:**
1. an option, not a new tactic;
2. atom identity at instance transparency;
3. the mixed path reporting `term_mode_int`;
4. `Int` facts on the constrained ℕ and `False` path;
5. the closer's own kernel check.

**The harness must:**
- **freeze the option setting**;
- **name the constrained final step explicitly in every receipt**;
- print each residual from the exported term, not from the closer's renamed context (`renameLocalsForSmt`), for control 8's
  binding.

## Not yet built

- **The replay harness:** sealed site-harness episodes on the new revision, with the requirements above.
- The mutation sets and labels (step 3), and the lock (step 4).

## Files

- `lean-bridge/ProofBroker/Tactic.lean`, `lean-bridge/ProofBroker/TermMode.lean`, `lean-bridge/Test/TermModeConstrained.lean`,
  and the test root in `lean-bridge/lakefile.lean` (`8a64acde`, `aa32cf21`, `476fab31`).
- `experiments/r6/r6-015/R6015AuditSynthetic.lean` and `synthetic_audit.py`, with the
  [record, revision 2](reviews/2026-10-01/R6-015-SYNTHETIC-AUDIT-PRELOCK-2.json).
