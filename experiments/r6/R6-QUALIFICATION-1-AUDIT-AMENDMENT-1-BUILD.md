# R6 qualification 1 audit, amendment 1 — build, for implementation review

**Build revision 4** of the audit program, 2026-10-02. It responds to
[the implementation review of revision 3](reviews/2026-10-02/R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-BUILD-REVIEW.md), which found
one P1 and four P2 issues and accepted readings a, b and d, and c's scope subject to finding 3. Revision 3 is `65e7c8bd`. This
implements [amendment 1, revision 3](R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-PROPOSAL.md), approved for implementation at
`3b9d0795`. The files are in [`qualification-audit-v2/`](qualification-audit-v2/). **`qualification-audit/` and the
`qualification-audit-v1` lock are not touched:** the v2 driver imports v1's driver, for its control expectations and its
`Nat.rec` mutation, and v1's generator, for the pinned fold and C1–C6, both unchanged.

**What changed in revision 4:**
1. **P1, a hidden fold.** The whole value must again contain exactly one fold, searched from an empty context as revision 2 did.
   The walk now records everything it passes over: binder types, `let` types and values, and applied-lambda arguments. If the
   body and those together do not hold exactly one fold, the parameters are unverified. **Control R10** puts a second fold in an
   applied lambda's argument: the local is not locatable ("2 fold applications"), and the parameters are unverified ("the walked
   context holds 2 fold applications, the whole value 2").
2. **P2, an applied lambda's definition.** Its binder is now a local definition (`withLetDecl`), and binder types and declaration
   `let`s are compared with `zetaDelta`, so a later binder's type may depend on it. **Control R7d** is the review's case:
   `(fun q => fun (h : 0 < q) (hn : q ≤ 5) => …) x` against `h : 0 < x`, `hn : x ≤ 5`. Three parameters; `h` maps through
   parameter 1 and `hn` through parameter 2.
3. **P2, the collision exemption** is removed. A search name that names any other binder of the fold's context refuses, renamed
   or not. **Control R4b** is the swap (`x` → `c'`, `c'` → `x`): `rename_unverified`, "search name c' already names another
   binder".
4. **P2, the regression gate.** `addendum2` and `l175` now require `--regression RECORD`, and refuse unless:
   - the record is a regression record, written under the current lock's digest;
   - its results cover exactly the 32 selected slots;
   - its verdict, **recomputed from its own results** against the lock's v1 expectations, has no difference, and its flags agree
     (`reproduced` true, `differences` empty).

   The gate is checked before the first audit and again after the last, and the record's digest is written into the
   application's output.
5. **P2, the toolchains' contents.** The lock now binds, and every verification recomputes:
   - **both toolchains, as trees:** every file by relative path and content, 14,710 each, with the toolchain's path. This covers
     the compiler, the runtime, and the `Init` and `Lean` environment that the tool imports and the controls compile against;
   - **the bridge modules the controls import,** closed under their own imports, each bound by content. The imports are read from
     each `.olean`'s header by the controls' toolchain. The closure is one module: `ProofBroker.TermMode`, which imports only
     `Init`. An import found neither in the bridge nor in the controls' toolchain refuses.

   About 9 seconds per verification.

**Also changed:** under a lock, `controls` verifies it before and after, and its record carries the lock's digest (null before
locking) and the toolchain contents.

**Two per-finding tests, without a lock** (`qualification-audit-v2/test_gates.py`, twelve cases, passing):
- **the regression gate:** a passing record is accepted, and its digest returned. Each of these refuses:
  - another application;
  - another lock;
  - a missing slot, and an extra one;
  - a classification difference, and a mapping difference, in results whose flags say passed;
  - a failed report;
  - flags that contradict passing results.
- **the toolchain binding:** the tree digest changes with a file's content, its name, or an added file. The bridge closure's
  digest changes with `TermMode.olean`'s content, and a missing import refuses.

**Status:**
- **Nothing is locked, and no retained export has been audited** by the amended program.
- **The controls pass under the build**, nothing locked
  ([record, revision 2](reviews/2026-10-02/R6-QUALIFICATION-1-AUDIT-V2-CONTROLS-PRELOCK-2.json);
  [revision 3's](reviews/2026-10-02/R6-QUALIFICATION-1-AUDIT-V2-CONTROLS-PRELOCK.json) is superseded):
  - C1–C9 meet `qualification-audit-v1`'s frozen expectations;
  - R1–R10 meet the amendment's.
- **The tool's digest is `444f7ac0…`.**
- **The lock record was computed as a dry run** and not written. It selects exactly 32 regression, 16 addendum-2 and 17 l175
  slots. Computing it hashes the selected artifacts and the toolchains, and reads the l096/l099 runs' sealed rename rows. No
  export was read.

## What was built

**Rule B, the walk** (`walk` in `Audit.lean`). It implements the frozen forms in order:
1. the end;
2. an applied lambda, internal, the type staying. Its binder is a local definition of its argument;
3. a parameter, `∀` against `λ` with definitionally equal binder types (local definitions unfolded);
4. a declaration `let`, matched by type and value;
5. a value-only `let`, internal;
6. anything else gives `parameters_unverified`.

The walk's continuation runs in the context it built, so the fold is found with the parameters' own variables:
- the whole value must hold exactly one fold, and so must the walked context (the body and everything the walk passed over);
  otherwise the parameters are unverified;
- parameters are mapped to the whole declaration by variable identity;
- applied-lambda arguments are kept as definitions for the dependency traversal;
- the report gains a `parameters` field: established, count, or the reason.

**Rule A, the renaming** (`verifyRenaming`, and `--rename=FILE`). The input is the run's rename rows and the site's frozen context.
- Every row is verified before anything is renamed:
  - **correspondence:** the index names an included telescope entry with the original name, and the walked binder at that position
    carries it;
  - **unique sources:** no two rows name the same index or reach the same binder;
  - **distinct destinations;**
  - **global injectivity:** no search name names any other binder of the fold's context, renamed or not, and the names in the goal
    stay pairwise distinct.
- The renaming is applied by binder identity, through the local context's user names, only for printing.
- **The binding values are** `matches_residual`, `matches_residual_after_renaming`, `rename_unverified` and `residual_mismatch`. Only
  the first two allow a sufficiency classification. The report's `binding_detail` keeps the renamed print and the rows, or the
  failure.

**Everything else is build revision 2's,** unchanged: the environment comparison, the replay, Checks 1 and 2, the
generalizations, and the classifications.

## The controls

| control | result |
|---|---|
| C1–C9 | v1's expectations, all met, including C1's, C4's and C5's parameter paths, now established by the walk |
| R1 | `matches_residual_after_renaming`; renamed print `0 < 1 * (x - c_) + 1 * (c_ + 1 - x)`; classified at both targets |
| R2 | `residual_mismatch` (print with `d_`); both targets unbound |
| R3 | `rename_unverified`: two rows name the same index |
| R4 | `rename_unverified`: the search name `x` already names another binder |
| R4b, new | `rename_unverified`: the swap; the search name `c'` already names another binder |
| R5 | `rename_unverified`: two rows share a search name |
| R6 | `rename_unverified`: at row 3's index, the frozen context names `h` |
| R7, with the declaration `let` | three parameters; `h` maps through argument 1 and `hn` through argument 2; `_q` internal |
| R7, without the `let` | the same |
| R7b | the same, with `_r` internal |
| R7d, new | three parameters, through a dependent applied-lambda binder; `h` through argument 1, `hn` through argument 2 |
| R8 | two parameters; the whole is not locatable (`1 references; arity #[3] for 2 parameters`) |
| R9 | `parameters_unverified`: the value does not have the form its type requires (an eta-reduced constant) |
| R9b | `parameters_unverified`: a declaration `let` does not match the value's |
| R10, new | two folds, one in an applied lambda's argument: the local is not locatable, and the parameters are unverified |

## The lock (dry run), and the applications

**`qualification-audit-v2` would bind:**
- the amended program and the controls' digests;
- the sources: v2's (`test_gates.py` included), and the v1 driver and generator it imports;
- the exporter;
- both toolchains' contents, and the bridge module the controls import;
- the digests of `qualification-audit-v1`'s lock, of its audit record, and of `r6-015-replay-v1`;
- the three applications' selections:
  1. **regression:** R6's 32 classified slots, each with v1's classifications and whole-target mapping, to be reproduced;
  2. **addendum 2:** R6's 16 slots at l096 and l099. Each carries its three sealed rename rows (`c'` → `c_`, `h1'` → `h1_`,
     `h2'` → `h2_`, at indices 4, 8 and 9), verified against the run's seal, and the site's frozen context;
  3. **l175:** R6-015's 17 proofs at l175, each with the residual its run printed from its export, verified against its seal.

**Every application refuses without the lock and verifies it again after,** with `live-evaluation-v3` for R6's runs and
`r6-015-replay-v1` for R6-015's.
- **The regression** writes every difference, in a classification or a mapping, and exits non-zero if any exists.
- **Addendum 2 and the l175 record** require the passing regression record, and are separate records. Addendum 1 and R6-015
  stay as they are.

## For the implementation review

**Accepted in review of revision 3:**
- a. When the walk fails, the local target is still audited from the whole value's fold, and only the whole target is refused.
  Revision 4 adds one such case: the walked context not holding exactly the one fold.
- b. A failed rename verification labels both targets `unbound_residual_mismatch`; the binding field says `rename_unverified`.
- c. Global injectivity is checked over the variables in `hpos`'s type, and against every binder of the fold's context. The
  exemption is removed (finding 3).
- d. R9's local target has no fold, so it is not locatable; the control checks `parameters_unverified`.

**New, for this review:**
- e. **The regression gate reads the record, and does not re-run it.** Its verdict is recomputed from the stored results. The
  regression is not itself gated on a passing controls record under the lock; the amendment's order runs the controls first.
  The same gate can be added there if you want it.
- f. **Only the controls' imported bridge module is bound,** not the bridge's whole build directory. Rebuilding other bridge
  modules, as the R6-016 harness will, does not disturb the lock; changing `TermMode.olean` does.

## Next

1. **After approval:** lock `qualification-audit-v2`, run the controls again under the lock, then the applications in the
   amendment's order (regression, addendum 2, l175).
2. **Record** addendum 2, the l175 record and the R6-015 erratum.
3. **Meanwhile, the R6-016 harness and analysis**, for their own review.
