# Proposal — auditing the final step of R6's 48 proofs

Status: proposal, 2026-09-30. It follows [R6 qualification 1](R6-QUALIFICATION-1.md). Nothing is frozen, and no tool is built.
- The audit is **offline**: no provider, credential, episode, bridge revision or spending.
- It **reads** R6's retained evidence and changes nothing: no run, record, lock or seal.
- It runs **before R6-015 is frozen**, so that R6-015 is designed with its answer in hand ([proposal](R6-015-PROPOSAL.md),
  revision 3).

## The question

For each of R6's 48 whole-validated proofs:
1. Does the final positivity step reference any of the goal's hypotheses?
2. Does the certificate's weighted sum suffice on its own?

Qualification 1 left both open. The receipts record the step (`residual_closer: omega`) but not what it depended on.

## Inputs, read-only

- **The 48 proof exports.** Each is `cohort-live-v9/<site>-draw<d>/solution.ndjson.gz`, in `lean4export` 3.1.0 format for Lean
  4.32.0, the header `validate/Replay.lean` pins. Each carries two targets with their full dependency closure:
  - the site's local theorem, `task.local` (for example `Bracket.lift_cell.r6_site_l069`);
  - the containing declaration, `task.whole` (for example `Bracket.lift_cell`), in which only this site was swapped to the broker.
- **For each slot:**
  - the run's seal, whose digests are checked before anything is read;
  - the consumption receipt;
  - the retained residual goal, from `residual_started`.
- **Units:** 48 slots; their coefficient maps, from the analysis input; 6 obligations.

## Locating the step

In each target's value, the broker's proof is the one application of `ProofBroker.TermMode.farkasContradictN s sumProof hpos`,
where `hpos : 0 < s` is what `omega` produced.
- The audit expects **exactly one** such application per target. Anything else is reported as *not locatable*, never guessed.
- `hpos`'s type, pretty-printed under fixed options, must match the run's retained residual goal. A mismatch is reported, which
  binds the audited term to the run.

## Check 1: dependency, which is syntactic

Open the binders on the path to `hpos` as local declarations, and collect `hpos`'s free variables. Classify each by whether its type
is a proposition (`Meta.isProp`, in the replayed environment).
- The **propositional** ones are hypotheses, and are reported by name.
- **Value** variables are expected and ignored: the variables `s` mentions, such as `x` in `x.val`, or `Zmax`.
- Binders that `omega` introduces *inside* `hpos` do not count.

## Check 2: sufficiency, which is semantic

Take `hpos`'s type, abstract its free value variables universally, admit **no** hypotheses, and attempt `omega`. Success means the
weighted sum is positive for all values: the certificate suffices by itself.

If `omega`'s support lemmas or an atom's definitions are not available in the replayed environment, first generalize each maximal
non-arithmetic subterm to a fresh variable of the same type. The arithmetic operators, numerals and ℕ→ℤ casts are kept. Control C3
validates that transformation.

## Controls

The controls are built with the fold compiled from the pinned source (`e627efe`), then frozen and run **before any of the 48**.

- **C1, the review's probe.** `h : x ≤ y ⊢ x ≤ y` with multipliers `h` 1 and `neg_goal` 2, closed by the pinned fold. Check 1 must
  report `h`, and Check 2 must fail.
- **C2, a valid combination in a rich context.** A combination that cancels, closed by the pinned fold, with extra unused
  arithmetic hypotheses in scope. Check 2 must pass. Check 1 reports whatever `omega`'s proof term references.

  **If Check 1 reports the unused hypotheses here,** then it cannot tell use from collection. It is dropped, and the record states
  dependency as *not determinable* and reports Check 2 alone. This is the main risk, because `omega` collects every hypothesis it
  understands before searching.
- **C3, casts and atoms.** A valid combination over ℕ→ℤ casts and an opaque product, the shapes R6's proofs contain. Check 2 must
  pass, including through the generalization step.
- **C4, local against whole.** For one synthetic declaration, the local and whole targets must give the same classification.

## Reading

| Check 1 (dependency) | Check 2 (sufficiency) | reading |
|---|---|---|
| no hypotheses | passes | the stronger claim holds for this proof: the certificate alone discharged the contradiction |
| hypotheses referenced | passes | the certificate suffices, but R6's proof drew on its context |
| any | fails | the Lean-level sum does not cancel although the checker verified the emitted rows. This is a mismatch between the rows and the Lean terms (casts, atoms), to be diagnosed, and a finding in itself |
| not determinable (C2 failed) | passes | the certificate suffices; how R6's proof was built stays open |
| not locatable | — | reported per target, with the reason |

## Reporting

- Results are reported per slot (48), per coefficient map and per obligation (6), for both targets.
- They are never pooled with R6-014's counts.
- The outcome is recorded as a dated addendum to qualification 1. It says either that the stronger reading holds for *k* of 48 (and
  which), or that dependency is not determinable while sufficiency holds for *k*.

## Freezing and order

1. **Review this proposal.**
2. **Build** the tool and the controls. The tool is in Lean on the pinned 4.32.0 toolchain, loading exports as `validate/Replay.lean`
   does (`Export.Parse`, `Lean.Replay`). Then review.
3. **Lock** the tool and the controls, and run the controls.
4. **Run** the audit on the 48, verifying R6's seals and locks before and after.
5. **Record** the result, with the addendum to qualification 1. Then freeze R6-015.

## Scope and cost

- The audit concerns R6's 48 proofs, and nothing more general.
- It costs CPU minutes once the tool exists. The build is roughly one focused session plus review.
- There is no spending, and R6's evidence is read, never rewritten.
