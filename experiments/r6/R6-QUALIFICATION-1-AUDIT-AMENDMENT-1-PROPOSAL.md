# R6 qualification 1 audit — amendment 1, proposal

Status: proposal, **revision 2**, 2026-10-02, against `main` at `3eb438a5`, for review. It responds to
[the review of revision 1](reviews/2026-10-02/R6-016-AND-AUDIT-AMENDMENT-1-REVIEW.md) (`ac5f7fec`), which found one P1 and one P2 here:
- Rule B guessed parameter identities from the fold context. It now establishes them;
- Rule A lacked a global injectivity check. It now has one. It amends the audit program locked as
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
   - **A second defect.** The program's parameter list takes the first 13 context entries. It can therefore include the `let`
     itself, or an internal binder the proof introduces (the review reproduced one, from an applied lambda), and misalign the
     mapping.
   - **The effect.** The whole target is "not locatable", and control 8 failed.

**An erratum this draft also proposes.** [R6-015's record](R6-015.md) explains l175's failure as "its source applies the captured
result to one more argument". That is wrong. The cause is the `let` in the local's type, described above. A dated erratum line
should be appended to R6-015.md. Its result is unchanged.

## The amended rules

**A. Binding up to the run's recorded renaming.**

**The input.** A run whose preparation recorded a search context supplies its rename rows. These are R6-013's `search_context`
rows (local index, original name, search name), from the run's sealed `stages/preparation/output/reification.json`, taking the
rows whose names differ. The driver reads them from the sealed file, checked against the run's seal and `live-evaluation-v3`.
Alongside them, the driver passes the site's frozen context (`context/local-context.json`), which lists each local declaration's
index, name and whether it is in the captured telescope.

**Every row must be verified** before any renaming is applied. Each condition is checked, and any failure gives
`rename_unverified`:
1. **Correspondence.** The row's index names an entry of the frozen context that is in the captured telescope, with the row's
   original name, and its `fvar_in_original` is true. That entry's position in the telescope identifies one declaration binder.
   Its binder in the export, established by rule B, must carry the same original name.
2. **Unique sources.** No two rows name the same index. No two rows' binders are the same declaration binder.
3. **Distinct destinations.** No two rows share a search name.
4. **Global injectivity.** After renaming, the names of all the fold context's binders that appear in `hpos`'s type are pairwise
   distinct. No search name equals the name of any other binder in the fold context. Nothing can be captured or confused.

**The renaming is applied by binder identity, never by name.** Only the verified declaration binders are displayed under their
search names, and every other binder keeps its own name.

**The binding values:**
- `matches_residual` if the unrenamed print equals the residual, as before;
- otherwise, with every row verified, `matches_residual_after_renaming` if the renamed print equals it;
- `rename_unverified` if a row fails verification;
- `residual_mismatch` otherwise.

Only the first two bind and allow a sufficiency classification. Both prints, and each row's verification, are recorded.

**B. Declaration parameters established, not guessed, and counted through `let` binders.**

**The local's type and value are walked in lockstep** from the outside in. Each step must match, or the walk fails:
- a `∀` binder of the type must meet a `λ` binder of the value whose binder type is definitionally equal to it (default
  transparency, checked in the walk's context). The value binder is introduced as a fresh variable and recorded as **parameter
  *i***, in order;
- a `let` of the type must meet a `let` of the value with a definitionally equal type and value. It is introduced as a local
  definition and not counted. This is the capture helper's convention: let-bound entries stay in the closed telescope and are not
  applied;
- the walk ends when the type has no further `∀` or `let`. The value's remaining body is then visited, in the context the walk
  built, to find the fold.

**The parameters are exactly the recorded variables,** identified by variable identity. A binder that the proof itself introduces
inside the body (an applied lambda, a `have`, a closer's `intro`) is never a parameter, wherever it falls in the fold context. Such
a binder is internal to the local proof, and is reported as internal if `hpos` reaches it.

**Mapping through the whole declaration.** A hypothesis `hpos` reaches is mapped to the whole declaration only if it is parameter
*i*, and then through argument *i* of the single reference.

**Locatability.** The whole target is locatable only if:
- the walk succeeded;
- the whole declaration refers to the local exactly once;
- that reference has exactly as many arguments as there are parameters.

**An unverified correspondence is refused, not guessed:** a failed walk gives `parameters_unverified`, and the whole target is not
locatable. No over-application is admitted, and no other arity.

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
| C1–C9 | `qualification-audit-v1`'s frozen classifications and mapped hypotheses. A run without rename rows and without a `let` in the telescope behaves identically |
| R1, a renamed binder | C2's structure with its binder named `c'`, a residual printed with `c_`, and a verified row `c'` → `c_` at the right index: binds as `matches_residual_after_renaming` and classifies |
| R2, a wrong destination | the same with the row `c'` → `d_`: verified, but `residual_mismatch`, both targets unbound |
| R3, a duplicate source | two rows naming the same index, or two binders named `c'` that the rows cannot tell apart: `rename_unverified` |
| R4, capture | the row's search name already names another binder of the fold context: `rename_unverified` |
| R5, duplicate destinations | two rows, `c'` → `c_` and `h1'` → `c_`: `rename_unverified` |
| R6, a wrong binder index | the row `c'` → `c_` at the index of a different binder: `rename_unverified` |
| R7, a `let` and an interleaved internal binder | a synthetic local with parameters `x`, `h`, `hn`, a `have` between them in its closed type, and a proof whose applied lambda puts an internal `_q` between `x` and `h` in the fold context (the review's case). Locatable; `h` maps to argument 1 and `hn` to argument 2, never through `_q`; if `hpos` reaches `_q`, it is reported internal |
| R8, still an arity mismatch | the same whole declaration applying the local with one argument more than its parameters: not locatable |
| R9, an unverified correspondence | a local whose value does not begin with the λ binders its type requires (an eta-reduced value): `parameters_unverified`, not locatable |

## Applications, each a separately locked record

1. **Regression, R6's 32 classified slots.** The amended program must reproduce addendum 1's classifications at both targets.
   Any difference stops the amendment's applications and is reported for review, whether in a classification or in a whole
   target's mapped hypotheses. A difference in the mapping would mean that `qualification-audit-v1`'s parameter guess was wrong at
   that slot. It would be recorded as that program's defect, not absorbed.
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
