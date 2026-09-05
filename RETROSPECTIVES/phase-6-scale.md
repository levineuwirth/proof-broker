# Phase 6 — walker scale profile

*(As of 2026-09-05: this retrospective is the close-of-work snapshot
of the walker scale profile (PR #78, 2026-06-16); the rule and corpus
counts in it are that snapshot's, and the current ones are the README
status table's. "Phase 6" here is the walker-scale usage of the label
— `spec/roadmap-v1.1.md` §2 resolves it against the distribution usage.
The walker's production path (the SDK mint gate equal to the walkers'
rule set, UF/UFLIA routed to it, live-strict suites on both bridges)
was closed in R1, `delta.md §5.2` and `§5.8`.)*

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
where the leaves actually run. The scale point reconstructs end-to-end
on both bridges: corpus dynamic replay is **16/16**.

## Three bugs the scale point exposed — all fixed

Pushing the corpus to 636 steps surfaced three issues the smaller goals
never reached, none a missing rule (all 24 of pigeonhole's rules are
supported, and the other goals replay). Profiling earned its keep by
finding them; each is a small, principled fix.

**(1) `False`-conclusion assume.** Every prior corpus goal had a
non-`False` conclusion, so the walker's `falseOrByContra` wrapper always
ran, introducing the negated goal as a hypothesis that cvc5's
negated-goal `assume` then matched. `lia_pigeonhole3`'s conclusion *is*
`False`: no wrapper runs, and cvc5's `(assume _ (not false))` had no
hypothesis to match — the walker errored on a literal it should prove
trivially. `¬False ≡ False → False` is the identity; both bridges'
assume-seeding now special-case `(not false)` to that proof (the same
term the `false` *rule* already used). Also covered by the small
`lia_false_from_bounds` corpus goal.

**(2) Resolution resolvent dedup.** Alethe clauses are sets, but the
walkers' `binaryResolve` / `binary_resolve` concatenated the two
premises' leftovers without deduping. A literal surviving in *both*
premises then appeared twice in the resolvent, and a later premise's
single complement cancelled only one copy — leaving the un-resolvable
`(a − b ≥ 0) ∨ (a − b ≥ 0)` at pigeonhole's final `n`-ary resolution.
Both walkers now dedup the resolvent (first-occurrence order) and inject
each surviving literal at its *looked-up* position, so both copies of a
duplicate land on its single slot. Latent until a goal's resolution
chain actually shared a literal across premises — which only pigeonhole
did.

**(3) Local assumes leaking into omega leaves (Lean).** The flat walk
binds every subproof's assumes through one `withLocalDeclsD`, so all of
them are in scope at every leaf. `omega`, handed the full local context,
would pull a local assume from an *unrelated* subproof into an
arithmetic leaf's proof; that subproof's discharge never abstracts it,
and the fvar leaked into the final term (the kernel's "declaration has
free variables"). But an arithmetic leaf is an unconditionally-valid
clause that must not depend on subproof-local assumptions. The Lean
omega-discharge now excludes the local-assume fvars from the hypotheses
it passes `omega`, scoping leaves to the goal context — matching the
Rocq side, whose `leaf_env` (goal + bind vars, no local assumes) already
enforced this. Surfaced only once a dedup'd resolvent (fix 2) let
reconstruction reach the offending leaf, and only with pigeonhole's
nested-subproof structure.

## Measurement note

Walker reconstruction cannot be timed via standalone `lake env lean` /
`coqtop`: the tactic calls the SDK over FFI, which is only linked into
the package build. So the profile commits the *structural* predictors
(deterministic, reviewable, regression-gated) rather than wall-clock
numbers (build-environment-dependent, non-deterministic in CI). The
arithmetic-leaf count is the predictor that matters: it is what the
per-leaf decision-procedure calls scale with, and it is the number to
watch when a refreshed cvc5 or a new goal changes the profile.
