# Proposal — auditing the final step of R6's 48 proofs

Status: proposal, **revision 2**, 2026-09-30. It follows [R6 qualification 1](R6-QUALIFICATION-1.md), and responds to
[the review of revision 1](reviews/2026-09-30/R6-QUALIFICATION-1-AUDIT-PROPOSAL-REVIEW.md), which found two P1 and one P2 issue.
Nothing is frozen, and no tool is built.
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
  - the retained residual goal, from `residual_started`. All 48 runs retain exactly one.
- **Units:** 48 slots; their coefficient maps, from the analysis input; 6 obligations.

## Locating the step

**In the local target.** The broker's proof is the one application of `ProofBroker.TermMode.farkasContradictN s sumProof hpos` in the
local theorem's value, where `hpos : 0 < s` is what `omega` produced.
- The audit expects exactly one; anything else is reported as *not locatable*, never guessed.
- `hpos`'s type, pretty-printed under fixed options, must match the run's retained residual goal. A mismatch is reported.

**In the whole target, through the local theorem.** The whole declaration does not contain the fold. It refers to the local theorem
by name. In the l069 draw 1 export, `Bracket.lift_cell` applies `Bracket.lift_cell.r6_site_l069` and contains no
`farkasContradictN`. The audit therefore:
1. opens the whole declaration's binders down to the single reference to the local theorem. Zero or several references, or a
   partial application, are reported as *not locatable*;
2. takes the arguments at that reference, which are the whole context's terms for the local theorem's binders;
3. maps each local-theorem binder that Check 1 finds in `hpos` to its argument term, and analyses that term in the whole context,
   with let definitions resolved as in Check 1.

The whole-target result names hypotheses of the **whole** declaration. The mapping to the local theorem's binders is retained.

## Check 1: dependency, which is syntactic

1. Open the binders on the path to `hpos` as local declarations, including every enclosing `let`.
2. **Resolve local definitions first.** Every `let`-bound variable that `hpos` refers to, directly or through another definition, is
   expanded, or its definition's dependencies are traversed transitively.
   - A value variable whose definition refers to a hypothesis counts as a reference to that hypothesis, for example
     `v := Classical.choose h` refers to `h`.
   - The path back to the original hypothesis is reported.
3. Classify each remaining free variable by whether its type is a proposition (`Meta.isProp`, in the replayed environment).
   - The **propositional** ones are hypotheses, and are reported by name, each with the path by which it was reached.
   - **Value** variables whose definitions (if any) reach no hypothesis are expected and ignored: the variables `s` mentions.
   - Binders that `omega` introduces *inside* `hpos` do not count.

## Check 2: sufficiency, which is semantic

Take `hpos`'s type, abstract its free value variables universally (after resolving definitions as in Check 1), admit **no**
hypotheses, and attempt `omega`.

- **Success is kernel-checked.** The resulting proof must be checked by the kernel against the **original** quantified expression.
- **Abstraction.** If `omega`'s support lemmas or an atom's definitions are not available in the replayed environment, first generalize
  each maximal non-arithmetic subterm to a fresh variable of the same type. The arithmetic operators, numerals and ℕ→ℤ casts are
  kept. A success on the generalized statement counts only together with a **kernel-checked specialization back to the original**
  quantified expression.
- **Failure establishes only this: sufficiency not established; diagnosis required.** The causes include missing support,
  incomplete normalization, an abstraction that lost a relationship between atoms, and a tool defect. Even a counterexample to a
  generalized statement need not refute the original.
- **A mismatch between R6's emitted rows and the Lean expression** is reported only when it is demonstrated independently: the rows
  and the reconstructed Lean expression disagree at a concrete, checked assignment. It is never inferred from a failure of Check 2.

## Controls

The controls are built with the fold compiled from the pinned source (`e627efe`), then frozen and run **before any of the 48**.

- **C1, the review's probe.** `h : x ≤ y ⊢ x ≤ y` with multipliers `h` 1 and `neg_goal` 2, closed by the pinned fold. Check 1 must
  report `h`. Check 2 must report *not established*.
- **C2, a valid combination in a rich context.** A combination that cancels, closed by the pinned fold, with extra unused
  arithmetic hypotheses in scope. Check 2 must succeed, kernel-checked. Check 1 reports whatever `omega`'s proof term references.

  **If Check 1 reports the unused hypotheses here,** then it cannot tell use from collection. It is dropped, and the record states
  dependency as *not determinable* and reports Check 2 alone. This remains the main risk, because `omega` collects every hypothesis
  it understands before searching.
- **C3, casts and atoms.** A valid combination over ℕ→ℤ casts and an opaque product, the shapes R6's proofs contain. Check 2 must
  succeed, including through abstraction and its checked specialization.
- **C4, the exported structure.** A synthetic whole declaration that refers to a synthetic local theorem by name, as R6's exports
  do, passing a whole-context hypothesis as an argument. The local and whole results must agree, and the whole result must name the
  whole declaration's hypothesis through the argument mapping.
- **C5, a let-bound value.** `hpos` mentions a value `v := Classical.choose h`. Check 1 must report `h`, with the path through `v`.
- **C6, a lossy abstraction.** An expression that holds, but whose generalization separates two definitionally equal atoms (for
  example `x.val` and `(x + 0).val`), so that cancellation is lost. Check 2 must report *not established*, and must not report a
  mismatch.

## Reading

| Check 1 (dependency) | Check 2 (sufficiency) | reading |
|---|---|---|
| no hypotheses | succeeds, kernel-checked | the stronger claim holds for this proof: the certificate alone discharged the contradiction |
| hypotheses referenced | succeeds, kernel-checked | the certificate suffices, but R6's proof drew on its context |
| any | not established | sufficiency not established; diagnosis required |
| not determinable (C2 failed) | succeeds, kernel-checked | the certificate suffices; how R6's proof was built stays open |
| not locatable | — | reported per target, with the reason |

A row/term mismatch is a separate finding, reported only when independently demonstrated as described in Check 2.

## Reporting

- Results are reported per slot (48), per coefficient map and per obligation (6), for both targets.
- For the whole target, the argument mapping is reported.
- Results are never pooled with R6-014's counts.
- The outcome is recorded as a dated addendum to qualification 1. It says either that the stronger reading holds for *k* of 48 (and
  which), or that dependency is not determinable while sufficiency holds for *k*.

## Freezing and order

1. **Review this revision.**
2. **Build** the tool and the controls. The tool is in Lean on the pinned 4.32.0 toolchain, loading exports as `validate/Replay.lean`
   does (`Export.Parse`, `Lean.Replay`).
3. **Second review.** It checks the tool against this specification, and in particular that every Check 2 success is a kernel-checked
   proof of the original quantified expression, with checked specialization wherever abstraction was used.
4. **Lock** the tool and the controls, and run the controls.
5. **Run** the audit on the 48, verifying R6's seals and locks before and after.
6. **Record** the result, with the addendum to qualification 1. Then freeze R6-015.

## Scope and cost

- The audit concerns R6's 48 proofs, and nothing more general.
- It costs CPU minutes once the tool exists. The build is roughly one to two focused sessions plus two reviews.
- There is no spending, and R6's evidence is read, never rewritten.
