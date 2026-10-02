# R6 qualification 1 audit, amendment 1 — build, for implementation review

**Build revision 5** of the audit program, 2026-10-02. It responds to
[the implementation review of revision 4](reviews/2026-10-02/R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-BUILD-REVIEW-2.md). That review
passed revision 4's three Lean-side repairs, found two P2 issues in the driver, and accepted readings e and f subject to them.
Revision 4 is `acc9432d`; revision 3 is `65e7c8bd`, and [its review](reviews/2026-10-02/R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-BUILD-REVIEW.md)
found the five issues revision 4 repaired. This implements [amendment 1, revision 3](R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-PROPOSAL.md),
approved for implementation at `3b9d0795`. The files are in [`qualification-audit-v2/`](qualification-audit-v2/).
**`qualification-audit/` and the `qualification-audit-v1` lock are not touched:** the v2 driver imports v1's driver, for its
control expectations and its `Nat.rec` mutation, and v1's generator, for the pinned fold and C1–C6, both unchanged.

**What changed in revision 5** (the driver only; `Audit.lean`, the controls and the tool's digest are unchanged):
1. **P2, the reports behind the regression's verdict.** Every report is now validated before it is compared
   (`report_invalid`). A valid report has:
   - an exit that is the integer 0 (a boolean is refused);
   - no error and no refusal;
   - real mode, on Lean 4.32.2, the version the lock names;
   - the residual bound: `matches_residual`, or `matches_residual_after_renaming` only where the slot carries a rename (no
     regression slot does);
   - both targets locatable.

   An invalid slot is recorded under `invalid` and is not compared. **The verdict is one function** (`regression_verdict`): the
   regression writes it, and the gate recomputes it from the record's own reports. The record passes only if `invalid` and
   `differences` are both empty and `reproduced` is true. All 32 of v1's regression slots satisfy the validation: real mode, Lean
   4.32.2, `matches_residual`, both targets locatable.
2. **P2, the import search order.** The controls' environment is now resolved as Lean resolves it (`controls_environment`),
   checked against the 4.32.0 source (`initSearchPath`, `SearchPath.findWithExt`):
   - **The order:** `LEAN_PATH`'s entries as given (the bridge's library, then the controls' directory), then the toolchain's
     library. The build takes its `LEAN_PATH` from the same function, so the two cannot drift.
   - **Lean's rule:** a module resolves in the first directory that holds its *root package*, as a directory or an `.olean`, and
     is looked for there only. The resolver follows that rule, so a missing module is not found further down the path.
   - **No shadows:** no root package of the toolchain (`Init`, `Lake`, `LakeMain`, `Lean`, `LeanChecker`, `LeanIR`, `Leanc`,
     `Std`) may be held by the bridge's or the controls' directory. Whatever resolves to the toolchain is therefore bound by its
     tree, including the toolchain modules' own imports.
   - **The closure starts from the exported module,** `R6AuditControlsV2`, which must resolve to the controls' directory, and
     whose `.olean` must import what its source does. It is four modules: `Init` and `Lean` from the toolchain,
     `ProofBroker.TermMode` from the bridge, and the controls from their directory.
   - **What is bound:** each non-toolchain module by every part an import may read (`.olean`, `.olean.server`,
     `.olean.private`, and `.ir`), present or absent. Its imports, read from its `.olean`, are followed.

**The gate tests** (`qualification-audit-v2/test_gates.py`) are now 31, all passing. They add:
- **for finding 1:** each of these, in results whose classifications and mappings match, is invalid, reported as invalid and not
  as a difference, and refused at the gate:
  - exit 1, `false` or `true`, or no exit;
  - a refusal, or an error;
  - synthetic mode, or Lean 4.32.0;
  - `residual_mismatch`, or a renamed binding without a rename;
  - either target not locatable;
  - no audit.

  A record whose `invalid` is non-empty, or missing, is refused too.
- **for finding 2:** each of these refuses:
  - a bridge-side `Init.olean`, or `Lean/` directory;
  - a controls-side `Init/` directory, or `Std.olean`;
  - the controls' module shadowed by a bridge-side copy.

  A part added beside an `.olean` changes the binding. Lean's no-fallthrough rule is pinned: an empty `ProofBroker/` in the bridge
  hides a `ProofBroker/TermMode.olean` in the controls' directory, and the closure refuses.

**Revision 4's repairs, which passed re-review:**
1. **The hidden fold (P1):** the whole value must hold exactly one fold, and so must the walked context (control R10).
2. **The applied lambda's definition (P2):** a local definition, compared with `zetaDelta` (control R7d).
3. **The collision exemption (P2):** removed (control R4b, the swap).
4. **The regression gate (P2):** `addendum2` and `l175` require `--regression RECORD`, checked before the first audit and again
   after the last, and record its digest.
5. **The toolchains' contents (P2):** both toolchains are bound as trees, every file by relative path and content, 14,710 each,
   with the toolchain's path.

Under a lock, `controls` verifies it before and after, and its record carries the lock's digest (null before locking) and the
toolchain contents.

**Status:**
- **Nothing is locked, and no retained export has been audited** by the amended program.
- **The controls pass under the build**, nothing locked
  ([record, revision 3](reviews/2026-10-02/R6-QUALIFICATION-1-AUDIT-V2-CONTROLS-PRELOCK-3.json)). Revision 2's
  ([`-PRELOCK-2`](reviews/2026-10-02/R6-QUALIFICATION-1-AUDIT-V2-CONTROLS-PRELOCK-2.json)) and revision 1's
  ([`-PRELOCK`](reviews/2026-10-02/R6-QUALIFICATION-1-AUDIT-V2-CONTROLS-PRELOCK.json)) are superseded.
  - C1–C9 meet `qualification-audit-v1`'s frozen expectations;
  - R1–R10 meet the amendment's;
  - the exports, and every report, are identical to revision 2's record.
- **The tool's digest is `444f7ac0…`, as in revision 4.** The controls' `.olean` was rebuilt byte-identical.
- **The lock record was computed as a dry run** and not written. It selects exactly 32 regression, 16 addendum-2 and 17 l175
  slots. Computing it hashes the selected artifacts, the toolchains and the controls' environment, and reads the l096/l099 runs'
  sealed rename rows. No export was read.

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
- both toolchains' contents, and the controls' environment as Lean resolves it;
- the digests of `qualification-audit-v1`'s lock, of its audit record, and of `r6-015-replay-v1`;
- the three applications' selections:
  1. **regression:** R6's 32 classified slots, each with v1's classifications and whole-target mapping, to be reproduced;
  2. **addendum 2:** R6's 16 slots at l096 and l099. Each carries its three sealed rename rows (`c'` → `c_`, `h1'` → `h1_`,
     `h2'` → `h2_`, at indices 4, 8 and 9), verified against the run's seal, and the site's frozen context;
  3. **l175:** R6-015's 17 proofs at l175, each with the residual its run printed from its export, verified against its seal.

**Every application refuses without the lock and verifies it again after,** with `live-evaluation-v3` for R6's runs and
`r6-015-replay-v1` for R6-015's.
- **The regression** validates every report, writes every invalid report and every difference, in a classification or a
  mapping, and exits non-zero if any exists.
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

**Accepted in review of revision 4, subject to its findings:**
- e. The regression gate reads the record, and does not re-run it. Its verdict is recomputed from the record's reports, now
  validated. The controls-first order remains required; it is the order of the steps, not a gate.
- f. Only the controls' imported closure is bound, not the bridge's whole build directory. It is now resolved in Lean's search
  order.

**New, for this review:**
- g. **The validation applies to the regression only.** For addendum 2 and l175, an unbound or non-locatable target is a
  finding, and is recorded as the audit reports it.
- h. **The tool's own environment** is its toolchain's library alone: the tool runs with no `LEAN_PATH`, so the tree binds it.
- i. **`.ir` is bound conservatively.** I did not establish that an import reads it. The 4.32.0 source reads `.olean`, and also
  `.olean.server` and `.olean.private` for a `module`. Neither non-toolchain module, the bridge's or the controls', has any part but `.olean`.

## Next

1. **After approval:** lock `qualification-audit-v2`, run the controls again under the lock, then the applications in the
   amendment's order (regression, addendum 2, l175).
2. **Record** addendum 2, the l175 record and the R6-015 erratum.
3. **Meanwhile, the R6-016 harness and analysis**, for their own review.
