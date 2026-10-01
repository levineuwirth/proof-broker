# R6 qualification 1 audit, amendment 1 — build, for implementation review

**Build revision 3** of the audit program, 2026-10-02. It implements
[amendment 1, revision 3](R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-PROPOSAL.md), approved for implementation at `3b9d0795`. The
files are in [`qualification-audit-v2/`](qualification-audit-v2/). **`qualification-audit/` and the `qualification-audit-v1` lock
are not touched:** the v2 driver imports v1's driver, for its control expectations and its `Nat.rec` mutation, and v1's generator,
for the pinned fold and C1–C6, both unchanged.

**Status:**
- **Nothing is locked, and no retained export has been audited** by the amended program.
- **The controls pass under the build**, nothing locked ([record](reviews/2026-10-02/R6-QUALIFICATION-1-AUDIT-V2-CONTROLS-PRELOCK.json)):
  - C1–C9 meet `qualification-audit-v1`'s frozen expectations;
  - R1–R9b meet the amendment's.
- **The lock record was computed as a dry run** and not written. Computing it hashes the selected artifacts and reads the
  l096/l099 runs' sealed rename rows. No export was read.

## What was built

**Rule B, the walk** (`walk` in `Audit.lean`). It implements the frozen forms in order:
1. the end;
2. an applied lambda, internal, the type staying;
3. a parameter, `∀` against `λ` with definitionally equal binder types;
4. a declaration `let`, matched by type and value;
5. a value-only `let`, internal;
6. anything else gives `parameters_unverified`.

The walk's continuation runs in the context it built, so the fold is found with the parameters' own variables:
- parameters are mapped to the whole declaration by variable identity;
- applied-lambda arguments are kept as definitions for the dependency traversal;
- the report gains a `parameters` field: established, count, or the reason.

**Rule A, the renaming** (`verifyRenaming`, and `--rename=FILE`). The input is the run's rename rows and the site's frozen context.
- Every row is verified before anything is renamed:
  - **correspondence:** the index names an included telescope entry with the original name, and the walked binder at that position
    carries it;
  - **unique sources:** no two rows name the same index or reach the same binder;
  - **distinct destinations;**
  - **global injectivity:** no search name names another binder of the fold's context, and the names in the goal stay pairwise
    distinct.
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
| R5 | `rename_unverified`: two rows share a search name |
| R6 | `rename_unverified`: at row 3's index, the frozen context names `h` |
| R7, with the declaration `let` | three parameters; `h` maps through argument 1 and `hn` through argument 2; `_q` internal |
| R7, without the `let` | the same |
| R7b | the same, with `_r` internal |
| R8 | two parameters; the whole is not locatable (`1 references; arity #[3] for 2 parameters`) |
| R9 | `parameters_unverified`: the value does not have the form its type requires (an eta-reduced constant) |
| R9b | `parameters_unverified`: a declaration `let` does not match the value's |

## The lock (dry run), and the applications

**`qualification-audit-v2` would bind:**
- the amended program and the controls' digests;
- the sources: v2's, and the v1 driver and generator it imports;
- the exporter and both toolchains;
- the digests of `qualification-audit-v1`'s lock, of its audit record, and of `r6-015-replay-v1`;
- the three applications' selections:
  1. **regression:** R6's 32 classified slots, each with v1's classifications and whole-target mapping, to be reproduced;
  2. **addendum 2:** R6's 16 slots at l096 and l099. Each carries its three sealed rename rows (`c'` → `c_`, `h1'` → `h1_`,
     `h2'` → `h2_`, at indices 4, 8 and 9), verified against the run's seal, and the site's frozen context;
  3. **l175:** R6-015's 17 proofs at l175, each with the residual its run printed from its export, verified against its seal.

**Every application refuses without the lock and verifies it again after,** with `live-evaluation-v3` for R6's runs and
`r6-015-replay-v1` for R6-015's.
- **The regression** writes every difference, in a classification or a mapping, and exits non-zero if any exists.
- **Addendum 2 and the l175 record** are separate records. Addendum 1 and R6-015 stay as they are.

## For the implementation review

1. **When the walk fails,** the local target is still audited from the whole value, as v1 did, and only the whole target is
   refused. The amendment says the whole target is not locatable, and is silent on the local.
2. **A failed rename verification** labels both targets with v1's unbound label (`unbound_residual_mismatch`). The binding field
   says `rename_unverified`.
3. **Global injectivity** is checked over the variables that occur in `hpos`'s type, and against every binder of the fold's
   context.
4. **R9's local target has no fold.** Its value is a constant, so the local is not locatable and no whole result is reported. The
   control checks `parameters_unverified`.

## Next

1. **After approval:** lock `qualification-audit-v2`, run the controls again under the lock, then the applications in the
   amendment's order (regression, addendum 2, l175).
2. **Record** addendum 2, the l175 record and the R6-015 erratum.
3. **Meanwhile, the R6-016 harness and analysis**, for their own review.
