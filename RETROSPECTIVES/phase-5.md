# Phase 5 retrospective (term-mode parity)

Phase 5 closed with term-mode reconstruction shipped end-to-end on both
bridges for the full Tier 1 + Tier 2 Farkas cert vocabulary: comparison
goals (≤ / < / ≥ / > / =), all four inequality hypothesis shapes plus
their negations, equality hypotheses with signed coefficients, rational
coefficients, arity-N premises in the Farkas combination, and arity-N
disjunctions in the Tier 2 case-split path. The architectural claim from
`delta.md` — *cert IS the proof, not just a certificate that one exists*
— held across every widening: every solver-emitted Farkas multiplier,
every coefficient, every signed-Eq direction flows through into the proof
term Lean/Rocq actually elaborates. No `omega` / `linarith` / `lia` / `lra`
call is made on the original goal in any term-mode path; the only narrow
tactic call is on the polynomial-identity strict-positivity subgoal (a
literal-coefficient sum that decides trivially).

The phase consumed what `delta.md §2.6` had budgeted for polish and
cross-platform distribution; that work is carried forward to Phase 6.
*("Phase 6" here and below is the distribution meaning of the label —
Phase 6-D in `spec/roadmap-v1.1.md` §2, as of 2026-09-05.)*

## Easier than expected

**Wrapper-then-False-fold unification.** Six special-cased comparison-
goal helpers (Z Le/Lt with the +1 trick, R Le with strict-aware `cng`,
R Lt standard, R Lt with strict `a1`) collapsed into a single uniform
path: apply a small wrapper to convert the comparison goal to `False`,
introduce `neg_goal` as a regular hypothesis, recurse into the
arity-N False-fold. The wrapper helpers (`z_le_via_lt`,
`r_lt_via_le`, etc.) are five-line proofs each, all axiom-free at the
universe's baseline. After the unification, ~150 lines of
`close_term_goal` + `goal_proof_shape` + `neg_norm_*` dispatch tables
deleted on Rocq, with a parallel cleanup on Lean; arity-N comparison
goals came almost free, since the False-fold was already arity-N. The
shape was opaque until I tried it — none of the arity-2 helpers
obviously generalized — but afterward the closer is substantially
simpler. Landed in `d9bc6e6` (Rocq) / `16db0b5` (Lean).

**Cert vocabulary widening had no schema cost.** Rational coefficients,
signed-Eq, Not hypotheses, arity-N case-split — none required
IR-schema or witness-format changes. Every widening was bridge-side.
The SDK already accepted rationals, allowed any-sign coefficients on
Eq, compiled Not hypotheses via dedicated `compile_hypothesis` arms,
and flattened nested `Or` via `Alethe_farkas.disjuncts_of`. The
bridges' `normalize_hypothesis` had been the only bottleneck on each.
The IR's design — surface forms map directly to compiled forms — kept
paying off here, and the SDK-readiness-ahead-of-bridge-widening
pattern repeated for every feature in the phase.

**SDK helper `clear_denominators_list`.** Rational support reduced to
a 35-line SDK helper (compute LCM of denominators, scale through)
plus calling it from three bridge parsers (Rocq's `parse_witness`,
Lean Int's `parseFarkasCoefficients`, Lean Mathlib's
`parseWitnessCoefficients`). Soundness argument is one sentence:
multiplying every Farkas coefficient by a positive integer preserves
each premise's compiled non-positivity, scales the residual K by the
same factor (sign preserved), and leaves strictness untouched. No new
trust axioms, no new closer logic, no new contradiction lemma.
Allowlist gained four helper entries + four test theorems.

## Harder than expected

**Rocq's `destruct` requires nested `OrAndIntroPattern`.** I assumed
`destruct H as [c | c | c]` would work on right-associated
`A \/ (B \/ C)` by analogy with Lean's `rcases`. Empirical probe (a
one-line Coq script) proved otherwise: Rocq's intro-pattern parser
treats each `Or` node as strictly binary and rejects flat patterns
with `"Expects a disjunctive pattern with 2 branches"`. Fix:
generate nested patterns recursively — `[case | [case | [case | case]]]`
for arity-4. Cost one build iteration on `367b534`. The Lean-vs-Rocq
asymmetry here is worth recording — prior intuition that the two
proof systems handle the same intro-pattern grammar fails on this
exact shape, and nothing in either reference points it out.

**Strict-aware Farkas fold over R.** Z's +1 trick folds strict
inequalities into Le-form at normalization time, so the False-fold
stays Le-only on Z. R has no discrete domain to lift into — strict
premises must thread through the fold to the contradiction step. The
R-side fold tracks strictness state through every accumulation step,
picking from four `add_*` combinators (Le+Le, Le+Lt, Lt+Le, Lt+Lt)
per step, dispatching at the end to `r_farkas_contradict_n_strict`
(allows K = 0) versus the standard `r_farkas_contradict_n` (requires
K > 0). Three commits to land on Rocq (`85a42cb`, `c1d34ea`, part of
`2bf8829`) plus the Lean port in `8447273`. Each combinator is two
lines; the orchestration of the four-way strict-state cross product
on every fold step is what cost the time. The strict-aware path also
forced a `r_zero_nonneg` helper (for the K = 0 case — `r_pos_is_nonneg`
requires a positive Z literal) and a `require_strict` flag threaded
through `compute_residual`.

**`farkas_contradict_n_strict` requires K ≥ 0, not K > 0.** Subtle
invariant on the strict-aware path: when any premise is strict
(Lt with positive coefficient), the linear sum is strictly negative,
so even K = 0 suffices for contradiction. I missed this on the first
strict-< landing and tried to discharge a K = 0 sum with the
loose-only `r_farkas_contradict_n`. Bug surfaced as `"residual K=0
must be positive (cert verifier should have caught this earlier)"` —
the verifier was right; the closer was treating the loose-K invariant
as universal. Fix lifted the `require_strict` flag through
`compute_residual` so the closer can permit K = 0 when at least one
premise is strict.

**Lean dynamic-syntax construction for `rcases`.** Generating an
arity-N rcases pattern (`hCase | hCase | ... | hCase`) hit Lean's
`rcasesPatMed = sepBy1(rcasesPat, " | ")` grammar. Recursive TSyntax
quotation works for binary `|` splices but I couldn't make it work for
variable-length sepBy1 in `MacroM` / `TacticM`. Fell back to
`Lean.Parser.runParserCategory` on a string-formatted tactic, which
works but feels indirect — the string-then-parse round-trip isn't
Lean-idiomatic. There's likely a more direct way via
`Lean.Syntax.SepArray` or macro-level sepBy1 splicing; I didn't find
it under the time budget. Recorded so the next dynamic-pattern case
in this codebase can consider both routes.

**Eq goal split + extension mvar instantiation.** Post-`apply
le_antisymm` (the Mathlib version, delegated through the
`tier1EqSplit` ReifierExt slot), the subgoal's type carried unresolved
typeclass metavariables for the `LE` instance. `matchRealGoal?`'s
`α.isConstOf ``Real` check failed against the mvar before
instantiation, and the symptom was the perfectly cryptic
`"non-False Real goal must have shape ... got n ≤ 5"` — the printed
goal *looks* Real-typed. Fix: `Lean.instantiateMVars` in the closer
entry to pin `α` to `Real`. Recorded inline in `8447273` because the
symptom would have been a long-debug-loop without that breadcrumb.

**Mathlib `le_antisymm` doesn't resolve from core's Mathlib-free
scope.** Core `ProofBroker.Tactic` is intentionally Mathlib-free —
projects that only need LIA shouldn't pay Mathlib's build cost — so
embedding `le_antisymm` directly in a core syntax quotation surfaced
as `` le_antisymm✝ `` (an unresolved hygienic identifier) at
elaboration time. Fix: added a `tier1EqSplit : TacticM Unit` slot to
the `ReifierExt` record. Core calls into the extension when the goal's
type matches the extension's `reifyType`; Mathlib provides
`lraEqSplit` with the import in scope. Same pattern as the existing
`tier1FarkasCloser` and `tier2CaseSplitCloser` slots, but I didn't
notice the need until the eq-split landing tried to share Int's
`Int.le_antisymm` path verbatim.

## Assumptions that held up

**Bridge parity scaling.** Rocq and Lean term-mode implementations
stayed in lockstep through every widening. The cadence was always
land-on-Rocq-first (the proven sandbox, with the OCaml-side closer
having more direct access to the IR), then mirror on Lean. The
algorithmic complexity was always universe-shape-driven — Z's discrete
domain enables the +1 trick; R's continuity requires
strict-preserving normalization. Once that universe asymmetry was
wired (the `lt_to_lt0` / `gt_to_lt0` + `mul_pos_neg` + `add_*` family
on the R universe record), every subsequent widening was mechanical
on both bridges with the same code shape. Occasionally a Lean-specific
wrinkle surfaced (the dynamic-syntax case above, the eq-split mvar
case), but they were never algorithmic.

**Cert IS the proof.** Every solver-emitted Farkas multiplier flows
through into the elaborated proof term. The trust footprint stayed at
each universe's intrinsic axioms across all 21-ish term-mode commits:
Z paths axiom-free or `[propext, Quot.sound]` from omega's
discharge of the literal-coefficient strict-positivity check; R paths
carry `ClassicalDedekindReals.sig_forall_dec` +
`FunctionalExtensionality.functional_extensionality_dep` on Rocq's
Stdlib `Reals`, or `[propext, Classical.choice, Quot.sound]` on
Mathlib's `Real`. Allowlist grew from 60-ish at Phase 4 close to 150
at Phase 5 close — but no theorem grew its axiom dependency. The
discipline of writing helpers with explicit term-mode proofs rather
than reaching for the decision procedure paid off here: when a helper
needed an axiom it became visible immediately rather than being
absorbed under a tactic.

**Universe-polymorphic OCaml closer (Rocq).** The `universe` record
in `term_mode.ml` started Phase 5 with Z + R fields for arithmetic
ops, and grew through the phase: strict-aware fold building blocks
(`mul_pos_neg`, `add_le_lt`, `add_lt_le`, `add_neg`,
`farkas_contradict_n_strict`), `eq_to_le0` / `eq_to_le0_flipped`,
`not_*_to_*0` family (four), `not_strict_inner_produces_lt` flag.
The pattern of "add fields to the record, populate per-universe,
dispatch via the closer's `u : universe` parameter" stayed clean
through every widening. No special-cased `u.name = "Z" | "R"`
branching was needed inside `normalize_hypothesis` or
`close_term_false` — the universe record carries the
universe-specific decisions and the closer is genuinely polymorphic.

**SDK readiness ahead of bridge widening.** Every term-mode feature
in this phase had the SDK side ready before I touched the bridge:
rational coefs (Farkas verifier accepts since Phase 3), Eq with signed
coefs (no sign check on the Eq branch), Not hypotheses (Not-arms in
`compile_hypothesis`), arity-N case-split (`disjuncts_of` flattens
nested Or; `extract_case_split` is index-based). The bridges were
always the bottleneck. The lesson, if any: the IR / verifier surface
is sticky once landed, and bridges can be widened iteratively against
a stable SDK without round-tripping schema decisions. The
Phase 0 / Phase 1 work to make the SDK boundary-design-durable paid
its bill here.

## What I'd do differently

**Probe Rocq's `destruct` pattern grammar before coding the
generator.** Thirty seconds in a Coq REPL would have proven that flat
patterns on nested `Or` don't work. I generated the flat pattern,
built, and only then learned the truth from a parser error. Cost one
build iteration on `367b534`. Generalizable form: when generalizing a
tactic pattern to handle arity-N, probe arity-3 by hand on both
proof systems before writing dynamic-pattern code. Intro-pattern
grammars are not portable between Lean and Rocq for nested
inductive types, and the asymmetry isn't obvious until you hit it.

**Move `r_zero_nonneg` and the strict-aware K = 0 plumbing into the
first strict-< landing, not the third.** I tracked the K = 0 case
additively over `85a42cb` (the False-goal strict landing) → `c1d34ea`
(LRA Lt-goal with strict a1) → `8447273` (Lean Mathlib port). The
pattern — strict premise + cng strict (or c1 strict) + K may be zero
— was visible from the first strict-< landing; I just didn't
generalize. A more systematic first pass would have landed all three
K = 0 cases at once. The pattern of "strict premise produces strict
sum, K need not be positive" is a single abstract claim; recognizing
it on the first encounter rather than the third would have saved two
follow-up commits.

## Carried forward

Term-mode reach widening took the calendar slot `delta.md §2.6` had
budgeted for polish + cross-platform distribution. The Phase 5 work
has shifted that scope to Phase 6:

- **Cross-platform OCaml runtime distribution.** The original Phase 5
  scope per `delta.md §2.6`. The distribution bundle scaffold from
  Phase 0 is the foundation; per-platform builds + signed bundles for
  macOS + package manager integration is real packaging work that
  Phase 5's term-mode push displaced.
- **Arity-N case-split end-to-end fixture.** The bridge implementation
  in `367b534` is mechanically correct (mirrors the SDK's already-N-
  ready `disjuncts_of` + `extract_case_split` + index-based ordering)
  but cvc5 doesn't emit arity-3+ case-split alethe proofs for the LRA
  goal shapes I tried — it falls back to Tier 0 oracle. A hand-crafted
  SDK fixture (synthetic alethe proof string with three subproofs each
  closing one disjunct) would exercise the closer's arity-N path end-
  to-end; the bridge-level regression today covers only arity-2
  through the existing case-split test. *(Since done: the synthetic
  arity-3 SDK fixture landed in `d273741`.)*
- **Dead-code cleanup.** The arity-2-specific comparison-goal helpers
  (`farkasGoalLe2`, `farkasGoalLt2` on Lean Int; `rFarkasGoalLe2`,
  `rFarkasGoalLt2`, `rFarkasGoalLt2StrictA1` on Lean Mathlib; the
  matching Rocq Z + R variants) are unreachable after the wrapper-then-
  False unification in `d9bc6e6` / `16db0b5`. Removing them shrinks
  the trust footprint (allowlist drops ~10 entries) and reduces
  confusion about which helpers are load-bearing. *(Since done:
  `6ca2c5a`.)*
- **Multi-variable rational-coefficient tests.** The rational widening's
  bridge-level tests (`pb_lra_term_rational_axiom_free` on both
  bridges) trigger the LCD = 1 short-circuit — solvers in practice
  emit integers for the goal shapes I crafted. A synthetic SDK test
  with genuinely-rational coefficients (e.g. `1/2`, `1/3`, `1/6`) and
  a Farkas combination that demonstrably routes through
  `Linear_arith.clear_denominators_list`'s scaling path would validate
  the new path more directly. The current bridge-level coverage is
  regression-only. *(Since done: `032a407`, the multi-variable
  rational Farkas test through `clear_denominators_list`.)*
- **Reifier widening for unsupported solver-emitted shapes.** Audit
  completed in the post-Phase-5 cleanup arc: the speculatively-named
  gaps (division literal as `App` node, conditional expressions,
  mixed Int/Real coercions) are not exercised by any solver emission
  in our fixture set. All real cvc5 / z3 proofs we hold today route
  through paths the reifier handles — rationals as `"n/d"` strings,
  standard arithmetic ops, plain integer and real literals. The
  audit's main finding is the meta-finding: this carried-forward
  item was speculative scaffolding for a *predicted* class of gaps,
  not *observed* breakage. Defensive guard landed: `compile_hypothesis`
  now surfaces "conditional expression (ite) in operand — Farkas
  requires linear arithmetic" instead of the generic "non-linear
  arithmetic operand" when an `ite` appears, so the day a solver
  does emit one the diagnostic points at the actual blocker. Further
  widening deferred until a real emission surfaces a real gap. The
  bigger design question — whether the universe-polymorphic record
  idiom generalizes beyond LIA + LRA, or whether QF_BV / QF_UF need
  their own closers — remains open and is the right anchor for
  Phase 7 if non-arithmetic theories enter scope. *(As of 2026-09-05:
  "Phase 7" was never a phase — the question is carried as an open
  question in `spec/roadmap-v1.1.md` §5.)*
- **Lean dynamic-syntax idiom for variable-length sepBy1.** Resolved
  in the post-Phase-5 cleanup arc. The string + `runParserCategory`
  round-trip in `closeViaCaseSplitReal` (LRA case-split closer) is
  replaced with the canonical TSyntax splice form
  `$[$pats]|*`: build an `Array (TSyntax `rcasesPat)` of the right
  length (one `hCase`-named pattern per disjunct), splice into the
  `rcases ... with` tactic via quotation. The Phase 5 comment in
  this code path claimed "recursive TSyntax quotation hits trouble
  with the Med category's sepBy1 shape" — the trouble was using the
  wrong category name in the inner quotation, not the splice
  mechanism itself. Net: 7 lines of string-assembly + parser
  invocation + explicit error case becomes 4 lines of direct AST
  construction. No runtime parse, no error-path to handle.
- **`fragment_of_logic` consolidation.** Carried forward from Phase 4,
  resolved in the post-Phase-5 cleanup arc. The Phase 4 fix consolidated
  the SMT-LIB-string → bare-fragment map (`Smtlib.fragment_of_logic`);
  the remaining gap was at IR-build time — each of the three SMT adapters
  shipped its own 5-line `pick_fragment` doing an incomplete Real-vs-LIA
  detection that ignored the bridge's pre-classified
  `logic_classification.first_order_fragment`. Removed all three copies
  and routed the dispatchers through `Farkas.effective_fragment`, which
  already honors the bridge's classification and adds a Real-subterm
  safety net. Surfaced (and fixed) one downstream consequence:
  `Refinement.run` was hyper-conservative about fragment names —
  errored on UF/BV instead of treating them as no-substitution
  fragments. Added an explicit no-substitution-fragments whitelist and
  a test that asserts the pass-through. Phase 4's prediction that "the
  next adapter add will pay for it" was right: the broken classifier
  was masked by every adapter independently downgrading to LIA, so
  the gap was latent until forced.
