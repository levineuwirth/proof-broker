# R6 qualification 1 audit — build, for implementation review

Built 2026-09-30 to [the proposal, revision 2](R6-QUALIFICATION-1-AUDIT-PROPOSAL.md), after its approval ("I approve proceeding to
build the tool and controls. The implementation review remains required before locking and auditing the 48").

**Status:**
- The tool and the six controls are built, and the controls pass their frozen expectations
  ([pre-lock record](reviews/2026-09-30/R6-QUALIFICATION-1-AUDIT-CONTROLS-PRELOCK.json)).
- **Nothing is locked, and the 48 have not been audited.** The driver's `audit` refuses without a lock; this was checked.

## What was built

All of it is in [`qualification-audit/`](qualification-audit/):

| file | role |
|---|---|
| `Audit.lean` | the tool: environment, locating, Check 1, Check 2 |
| `make_controls.py` | generates `R6AuditControls.lean`: the pinned fold, copied byte for byte from `Tactic.lean` at `e627efe`, plus C1–C6 |
| `R6AuditControls.lean`, `.provenance.json` | the generated controls; the fold region's digest is `477c4ec7…`, and its thirteen declarations are asserted by name |
| `qualification_audit.py` | the driver: `build`, `controls`, `lock`, `audit` |

- **The build** is reproducible with `qualification_audit.py build` into `.cache/qualification-audit/` (gitignored).
  - Tool binary: `eb5859cf…`.
  - Controls: compiled against the lean-bridge's `ProofBroker.TermMode`, which is unchanged between `e627efe` and `r6`.
  - Control exports: made with R6's own pinned exporter (`.cache/exporter/…/lean4export`), one local-and-whole pair per control, the
    shape of R6's exports.

## The environment, and why it is 4.32.0

**The Lean build.** The exports' header names Lean 4.32.0 at git hash `8c9756b2…`, and the installed 4.32.0 toolchain has exactly that
hash. The tool is built with it and imports its `Init` with extensions loaded, which `omega` needs.

**The toolchain correction.** The proposal says "the pinned 4.32.0 toolchain, loading exports as `validate/Replay.lean` does".
`Replay.lean` actually builds on **4.32.2**. 4.32.2's `Init` differs from the export's in 218 shared constants, including `omega`'s own
lemmas, so an audit on 4.32.2 would reason about different constants. It was therefore built on 4.32.0.

**Equality with the export.** Every export constant that `Init` also has must equal it **up to what the kernel ignores**, or the audit
refuses. What the kernel ignores here is metadata, binder names and info, and the `let` `nonDep` hint, all of which the exporter
strips. Measured on the controls' exports, and on the one R6 export read during development (see the disclosure below):

| shared constants | identical | equal up to annotations | different |
|---|---|---|---|
| l069 draw 1 | 1,923 | 218 | 0 |
| the six control exports | 1,245–1,309 | 170–174 | 0 |

**Replay.** The export's other constants are replayed through `CoreM`'s `addDecl`, adapted from Lean's `Lean.Replay` (Apache-2.0,
attributed in the source). Each is therefore kernel-checked *and* visible to `MetaM`. A plain kernel replay leaves constants
invisible to `Environment.find?`.

**The kernel.** Check 2's theorems are checked by the 4.32.0 kernel. 4.32.2 fixes a soundness bug in checking *nested inductive
declarations*. Check 2 adds only theorems, and every replayed constant was already accepted by R6's 4.32.2 validation.

## Where the implementation departs from, or interprets, the proposal

1. **The toolchain:** 4.32.0, as above.
2. **Check 2 and local definitions.** The proposal says "abstract its free value variables universally (after resolving definitions
   as in Check 1)". The tool quantifies each `let`-bound value as a **plain variable**, with its definition dropped. That is a stronger
   statement.
   - Expanding the definition instead (zeta) can bring a hypothesis into the statement, as `v := Classical.choose h` does, and
     `intros` would then hand it to `omega`.
   - If a proof term remains in the statement, Check 2 reports *not attempted*.

   This interpretation should be confirmed.
3. **C6's mechanism.** The proposal's example was `x.val` against `(x + 0).val`. The built C6 uses `x % 2 < 2`. `omega` reads `%`, and
   the abstraction makes `x % 2` an atom, losing `x % 2 < 2`. It is the same property: a lossy abstraction that must read *not
   established* while the original succeeds.
4. **Internal hypotheses.** Propositional binders introduced inside the local proof are reported in both targets. For the whole
   target they are labelled "internal to the local proof". Examples are `neg_goal` and asserted cast facts.
5. **Check 2 for the whole target.** The whole target reaches the same `hpos` through its reference to the local theorem, so Check 2 is
   reported once per export and applies to both.
6. **An abstraction attempt after a failure.** When the direct attempt fails, the abstraction path is tried, as the proposal says. The
   controls force it for C3 and C6.

## Disclosure

**During development, before the controls existed, the prototype read one of the 48 exports, l069 draw 1.** It was used to establish
the export's structure and the environment. That exposed its Check 1 result early:
- `hpos` references **no hypotheses**, only value variables;
- its retained residual goal matched, character for character.

Its first Check 2 attempt was invalid: it ran inside the site's context, and the kernel rejected the leaked variables. That led to
the empty-context rule. No rule of the tool was tuned on the Check 1 result. No other R6 export has been read.

## The controls, pre-lock

| control | Check 1 | Check 2 | expectation |
|---|---|---|---|
| **C1**, the review's probe | `h` (and `neg_goal`) | direct and abstraction both fail: not established | met |
| **C2**, a valid combination with unused `hu1`–`hu3` in scope | `h`, `neg_goal`; **not** `hu1`–`hu3` | kernel-accepted | met; Check 1 **can** tell use from collection, and is kept |
| **C3**, casts and a product | `h`, `neg_goal` | direct accepted; the abstraction (atom `x * y`) and its specialization accepted | met |
| **C4**, the exported structure | local `h`; whole `hpq` through parameter 2, not `hextra` | not established, both targets | met |
| **C5**, a let-bound value | `h` through `v`; whole `h` through parameter 0 | accepted, over a plain `v` | met |
| **C6**, a lossy abstraction | `neg_goal` | direct accepted; the abstraction (atom `x % 2`) not established; counts as sufficient; no mismatch | met |

**An observation that bears on reading the 48.** In C2 the combination is valid, yet Check 1 reports `h` and `neg_goal`. Inside the
fold, a valid certificate's own hypotheses are jointly contradictory, so contextual `omega` can derive `0 < s` from them directly, and
here it did. Two things follow:
- The unrelated `hu` facts, including `hu3 : y ≤ z + 10`, which shares an atom, are not referenced. That is why Check 1 is kept.
- Reading R6's results: *hypotheses referenced* means the final step did not rest on the weighted sum alone, even when the certificate
  suffices. That is the table's "sufficient, but context referenced" row.

## For the implementation review

1. `Audit.lean` against proposal revision 2, in particular:
   - the whole-target traversal through the local theorem's reference;
   - the definition tracking for `let`s and applied lambdas;
   - **that every Check 2 success is a kernel-checked proof of the original quantified statement**, with checked specialization
     wherever abstraction was used.
2. The environment rule: the equality up to annotations, and the replay through `addDecl`.
3. The interpretation in item 2 of the departures (plain variables in place of definitions).
4. C6's changed mechanism.
5. The fold copy: `make_controls.py` and its digest, against `Tactic.lean` at `e627efe`.
6. The driver: the seal checks before any export is read, the `live-evaluation-v3` verification before and after, and the lock.

**After approval:** lock (`qualification_audit.py lock`), re-run the controls, run `audit` on the 48, and record the result and the
addendum to qualification 1. Then R6-015 is frozen.
