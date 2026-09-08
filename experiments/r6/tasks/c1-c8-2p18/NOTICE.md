# C1-derived exact-support recovery control

This is a synthetic control derived from the committed C1 `C8_coef_2p18` case.
It adds coverage of SDK certificate synthesis after bounded enumeration fails.
It does not add an independent downstream obligation or benchmark breadth.

[`source/C8.omega.lean`](source/C8.omega.lean) preserves the original generated
anonymous example from Proof Broker commit
`e627efe1ee69638678cc94e3f759d93abd69a160`, along with the original corpus,
independent arithmetic truth calculation, and saved final IR. The original
`RmsNorm.P` definition is retained as reference source from VerInf case-study
commit `573e1686323fe5fc1aa9a41c1d3c20b1175732cd`. See
[`source-provenance.json`](source-provenance.json) for exact paths and hashes.

[`Pristine.lean`](Pristine.lean) is the derived R6 control, not a verbatim copy of
that upstream example. [`derivation.patch`](derivation.patch) records all changes:
the repository imports become `Mathlib` plus the same numeral definition under
`R6.C8`; the theorem receives a name; a local `hlt` proof hole and an `exact hlt`
wrapper exposes both acceptance predicates; profiling/linter options are
omitted. The original mathematical binders and goal retain their source spelling.

The local proof closes over the wrapper's entire telescope, so both targets have
identical types. Containing replay adds only the `exact hlt` declaration
(1,470 → 1,471 checked declarations) and tests local-proof binding. It does not
test embedding an obligation in a larger downstream context as D1/70 does.
This qualification concerns replay coverage; the exact-support recovery branch
remains exercised.

The selected dependency lock is the same Mathlib/toolchain environment used by
D1/70. The original C1 `Model`, `ProofBroker`, and `ProofBrokerMathlib` imports are
reference material during freezing. The broker episode adds its separately
pinned and instrumented search modules. The original field's additional
instances and declarations are not silently claimed as part of this control.

[`permitted.patch`](permitted.patch) is the subsequent proof-hole instrumentation
against this derived pristine source. The capture helper differs from D1/70's
only in the task and saved declaration names. The two frozen targets are
`R6.C8.coefficient_bound.r6_c8` and `R6.C8.coefficient_bound`; the latter must
reference the former. Both human baseline footprints are `[Quot.sound, propext]`.
The allowed ceiling remains `[Classical.choice, Quot.sound, propext]`, with every
addition/removal reported.

In addition to the shared certificate and kernel checks, this control requires:

- bounded enumeration fails and exact-support recovery succeeds, in order;
- the synthesized witness is `262144·hhi + 1·neg_goal`;
- the reified goal and hypotheses match the saved C1 final IR exactly;
- the checked Farkas certificate is consumed and both declarations pass replay.

The IR comparison covers the goal and context. Qualified definition names and
library provenance intentionally differ after the recorded source derivation.
The control's `original_declaration` field names its derived pristine theorem;
the upstream C1 artifact is an anonymous `example`. The manifest states this
distinction explicitly.

Preparing these references in an unfrozen task requires a local VerInf checkout
containing commit `573e1686323fe5fc1aa9a41c1d3c20b1175732cd`, supplied to
`run.py freeze --task c1-c8-2p18 --verinf-repo PATH`. The script reads the pinned
Git object, not the checkout's current file. The published task is already
frozen and the command refuses to overwrite it. Ordinary runs and audits use
the retained reference bytes and do not need the original agent worktree.
