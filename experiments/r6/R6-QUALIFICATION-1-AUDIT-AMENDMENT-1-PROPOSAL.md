# R6 qualification 1 audit — amendment 1, proposal

Status: proposal, **revision 1**, 2026-10-01, against `main` at `3eb438a5`, for review. It amends the audit program locked as
`qualification-audit-v1` (`eea12f40…`; [proposal](R6-QUALIFICATION-1-AUDIT-PROPOSAL.md), [build](R6-QUALIFICATION-1-AUDIT-BUILD.md)).
**`qualification-audit-v1`, its records and [addendum 1](R6-QUALIFICATION-1-ADDENDUM-1.md) are not changed.** The amended program
is a new revision under a new lock, `qualification-audit-v2`. Each new application is a separately locked record. It is proposed
alongside [R6-016](R6-016-PROPOSAL.md), whose control 8 would use it, and is reviewed on its own.

## Why

Two of the locked program's frozen rules withheld a classification for reasons that are not about the proofs.

1. **Binding, at l096 and l099 (16 of R6's 48 slots).**
   - **The rule.** Binding requires `hpos`'s printed type to equal the run's retained residual goal.
   - **Why it fails there.** R6-013's preparation renamed unsafe local names for the search context (`renameLocalsForSmt`): at l096
     and l099, `c'` became `c_`, `h1'` became `h1_`, and `h2'` became `h2_`. The pinned closer printed its residual in that renamed
     context, while the export keeps the original binder names.
   - **The effect.** Under exact equality the slots are unbound, and addendum 1 left them unclassified.
2. **Whole-target arity, at l175 (R6-015's 17 proofs there).**
   - **The rule.** The program counts the local theorem's parameters with `forallTelescope`, which stops at the first `let`, and
     requires the whole declaration's single reference to have exactly that many arguments.
   - **Why it fails there.** l175's closed local type contains a `have` partway through its telescope:
     `… → ∀ (hzh : ¬zhigh = 0), have hzh1 := ⋯; ↑Zmax ≤ ↑Zmax * zhigh → ↑Zmax ≤ v`. R6's capture helper keeps let-bound entries
     in the closed telescope and does not apply them (`capture/CaptureSite.lean`). So the whole declaration applies the local to
     its 14 non-let binders, while the program counts 13.
   - **A second defect.** The program's parameter list takes the first 13 context entries, so it can include the `let` itself and
     misalign the mapping.
   - **The effect.** The whole target is "not locatable", and control 8 failed.

**An erratum this draft also proposes.** [R6-015's record](R6-015.md) explains l175's failure as "its source applies the captured
result to one more argument". That is wrong. The cause is the `let` in the local's type, described above. A dated erratum line
should be appended to R6-015.md. Its result is unchanged.

## The amended rules

**A. Binding up to the run's recorded renaming.**
- **The input.** A run whose preparation recorded a search context (R6-013's `search_context` rows: index, original name, search
  name, in the run's sealed `stages/preparation/output/reification.json`) supplies its rename map, the rows whose names differ. The
  driver reads it from the sealed file, checked against the run's seal and `live-evaluation-v3`, and passes it to the program.
- **The printing.** The program prints `hpos`'s type twice: as it stands, and with each binder of the fold's context whose user
  name is a renamed original name displayed under its search name.
- **The conditions.** The renaming is applied only if the original name occurs exactly once among the fold context's binders, and
  the search name occurs in none of them, so nothing can be captured or confused.
- **The binding values:**
  - `matches_residual` if the unrenamed print equals the residual, as before;
  - otherwise `matches_residual_after_renaming` if the renamed print equals it;
  - `rename_ambiguous` if a condition fails;
  - `residual_mismatch` otherwise.
- **The classification.** Only the first two bind and allow a sufficiency classification. Both prints are recorded.

**B. Parameters counted through `let` binders.**
- **The count.** The local's parameters are its type's non-let binders, through every `let` in the telescope. Each `let` is
  introduced as a local definition and not counted, and the telescope continues into its body. This matches the capture helper's
  convention.
- **The parameter list.** It is the fold context's non-let, non-implementation-detail binders, in order. Mapping a reached
  hypothesis through the whole declaration's arguments uses that list.
- **Locatability.** The whole target is locatable only if the whole declaration refers to the local exactly once, with exactly that
  many arguments. Nothing else changes: no over-application is admitted, and no other arity.

Everything else is `qualification-audit-v1`'s, unchanged:
- the environment comparison;
- the kernel replay;
- Checks 1 and 2;
- the generalizations and their specializations;
- the classifications;
- the lock's freezing of selection, artifacts and digests.

## Controls

The amended program is first run on these synthetic controls. Their expectations are frozen here.

| control | expectation |
|---|---|
| C1–C9 | exactly `qualification-audit-v1`'s frozen results. A run without a rename map and without a `let` in the telescope behaves identically |
| R1, a renamed binder | C2's structure with its binder named `c'`, a residual printed with `c_`, and the map `c'` → `c_`: binds as `matches_residual_after_renaming` and classifies |
| R2, a wrong map | the same with the map `c'` → `d_`: `residual_mismatch`, both targets unbound |
| R3, ambiguity | two binders named `c'`: `rename_ambiguous`, unbound |
| R4, capture | the map's search name already names another binder: `rename_ambiguous`, unbound |
| R5, a `let` in the telescope | a synthetic local whose closed type has a `have` between its parameters, applied by its whole declaration at the full non-let arity: locatable, with each reached hypothesis mapped to the right parameter (one deliberately after the `let`) |
| R6, still an arity mismatch | the same whole declaration applying the local with one argument more than its non-let binders: not locatable |

## Applications, each a separately locked record

1. **Regression, R6's 32 classified slots.** The amended program must reproduce addendum 1's classifications exactly, at both
   targets. Any difference stops the amendment's applications.
2. **R6's 16 slots at l096 and l099,** with their recorded rename maps. The new classifications go in a new record, *R6 qualification
   1, addendum 2*. Addendum 1 stands.
3. **R6-015's 17 proofs at l175.** These are informational only: R6-015's result and its control 8 are unchanged. Their new whole-
   target results are recorded separately.
4. **R6-016's control 8.** This is the program R6-016 proposes to use (its section 5), if approved and locked first.

## Order

1. **Review this proposal.**
2. **Build** the program revision (`Audit.lean`, build revision 3) and the driver changes (the rename-map input and the new
   applications). Run the controls. Review.
3. **Lock** `qualification-audit-v2`: the program, the controls, the driver, the rename maps of the 16 slots, every consumed
   artifact's digest, and the toolchains.
4. **Run the controls under the lock, then the applications in the order above.** Record addendum 2, the l175 record and the
   R6-015 erratum.

No provider, credential or spending. R6's runs, R6-015's runs and all existing locks are only read.
