# Phase 6 — walker scale profile

The walker's per-rule vocabulary is complete (31 rules, Lean ⇄ Rocq at
parity) and the corpus replays 15/15 on the quantifier-free + quantifier
fragment. The open question this phase answers is *cost*: how does
walker reconstruction scale, and where does the time go? The corpus had
spanned 5–120 steps; this phase adds the ~600-step pigeonhole as a
deliberate scale point and turns the structural cost predictors into a
committed, gated profile (`tools/profile_walker.py`, `corpus/profile.json`).

## The cost model

Reconstruction cost splits cleanly into two structural quantities, both
read straight off the committed trace:

* **Arithmetic leaves** (`la_generic` / `la_mult_neg` / `hole` /
  `rare_rewrite`) — each is discharged by an independent decision-
  procedure call (Rocq `lia`, Lean `omega`, with a `propext`-iff
  fallback for the Prop-equality holes). These dominate wall-clock.
* **Steps** — each non-leaf step assembles one kernel sub-term
  (resolution cascades, congruence, the boolean cluster). Individually
  cheap, but the count sets the size of the term the kernel re-checks.

So reconstruction is roughly `O(#leaves × solver-cost) + O(#steps ×
term-build)`, with the leaf term dominant: the leaves are where a real
decision procedure runs, everything else is bounded kernel plumbing.

## The profile

`tools/profile_walker.py` (committed baseline `corpus/profile.json`,
CI-gated by `--check`) reports, per unsat corpus trace, the structural
predictors sorted by size. The current gradient:

```
  goal                  steps  leaves  subpf  resol  rules
  prop_demorgan             5       0      0      2      3
  lia_irrefl                7       2      0      2      5
  lia_disjunction          11       2      0      3      6
  prop_eq_trans            13       2      0      2      7
  uf_cong                  13       2      0      2      7
  uf_trans                 13       2      0      2      7
  lia_sum_bound            18       5      0      4      6
  uf_exists_witness        23       4      1      6     12
  lia_eq_from_bounds       26       4      0      6     10
  uf_forall_inst           26       4      3      7     14
  lia_false_from_bounds    39      12      0      9     15
  lia_weaken_bound         40      12      0      9     15
  lia_strict_trans         66      21      0     11     15
  uf_lia_mix              120      19      3     30     24
  lia_pigeonhole3         636     118     10    140     24
```

`lia_pigeonhole3` is ~5× the next goal by steps and ~6× by arithmetic
leaves (118 vs 19) — a clean stress point well separated from the rest
of the corpus. The profile is the deterministic, solver-free proxy for
reconstruction cost; the ground-truth wall-clock is the CI replay (Rocq
`CorpusReplay.v` under `coqc`, Lean `ProofBroker.Test` under `lake`),
where the leaves actually run.

## Two gaps the scale point exposed

Pushing the corpus to 636 steps surfaced two issues the smaller goals
never reached. Profiling earned its keep by finding them.

**(1) `False`-conclusion assume — fixed.** Every prior corpus goal had a
non-`False` conclusion, so the walker's `falseOrByContra` wrapper always
ran, introducing the negated goal as a hypothesis that cvc5's
negated-goal `assume` then matched. `lia_pigeonhole3`'s conclusion *is*
`False`: no wrapper runs, and cvc5's `(assume _ (not false))` had no
hypothesis to match against — the walker errored on a literal it should
have proved trivially. `¬False ≡ False → False` is the identity; both
bridges' assume-seeding now special-case `(not false)` to that proof
(the same term `elabFalseStep` / `elab_false_step` already gave the
`false` *rule*). Covered end-to-end by the new `lia_false_from_bounds`
corpus goal (a small `False`-conclusion replay), and a focused
`*_axiom_free` theorem on the Lean side.

**(2) Resolution shape gap at scale — recorded.** With (1) fixed,
`lia_pigeonhole3` reconstructs through 600+ steps and then stalls at the
top-level `n`-ary resolution: it yields an un-contracted duplicate
literal (`(a − b ≥ 0) ∨ (a − b ≥ 0)`) instead of the empty clause. The
walker's pairwise-resolution cancellation order diverges from cvc5's
intended one for this premise structure — a shape gap, not a missing
rule (all 24 of pigeonhole's rules are supported and the other 23 corpus
goals resolve fine). The goal is committed `replay_skip` (statically
walkable, dynamically shape-gapped — the coverage classifier's existing
third state), so it stays in the profile and the static gate while being
excluded from the `coqc` replay. Closing the gap is a focused follow-up:
the symptom points at the resolvent dedup / cancellation-order logic in
the `n`-ary resolution path, exercised by a minimised version of this
final step.

## Measurement note

Walker reconstruction cannot be timed via standalone `lake env lean` /
`coqtop`: the tactic calls the SDK over FFI, which is only linked into
the package build. So the profile commits the *structural* predictors
(deterministic, reviewable, regression-gated) rather than wall-clock
numbers (build-environment-dependent, non-deterministic in CI). The
arithmetic-leaf count is the predictor that matters: it is what the
per-leaf decision-procedure calls scale with, and it is the number to
watch when a refreshed cvc5 or a new goal changes the profile.
