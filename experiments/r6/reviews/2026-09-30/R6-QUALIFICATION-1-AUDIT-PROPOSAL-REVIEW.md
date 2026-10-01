# R6 qualification 1 audit proposal review

Supplied by the reviewer in session on 2026-09-30, against revision 1 of `R6-QUALIFICATION-1-AUDIT-PROPOSAL.md`, which is committed
alongside this record as reviewed. It is recorded verbatim below.

---

The offline scope and review order are sound, but I would revise three points before building.

  1. [P1] Follow the local theorem reference when locating the whole-target step. At lines 31–33 (experiments/r6/R6-QUALIFICATION-1-AUDIT-PROPOSAL.md:31), the proposal searches each target’s value for exactly
     one application. In the retained l069/draw1 export, the local theorem contains farkasContradictN; Bracket.lift_cell contains no direct application and instead references Bracket.lift_cell.r6_site_l069. As
     written, the whole target would be “not locatable.” Specify traversal through that named reference, including argument substitution and binder handling. C4 should reproduce this exported structure.

  2. [P1] Check 2 failure does not establish a row/term mismatch. The interpretation at line 76 (experiments/r6/R6-QUALIFICATION-1-AUDIT-PROPOSAL.md:76) overclaims. Failure can result from missing support,
     incomplete normalization, the abstraction losing relationships between atoms, or a tool defect. Report “sufficiency not established; diagnosis required.” Reserve a mismatch finding for independently
     demonstrated disagreement between the emitted rows and reconstructed Lean expressions. Even a counterexample to the generalized expression need not refute the original expression.

  3. [P2] Resolve local definitions before ignoring value variables. The free-variable rule at lines 39–43 (experiments/r6/R6-QUALIFICATION-1-AUDIT-PROPOSAL.md:39) needs explicit handling of enclosing let
     bindings. A referenced value variable can have a definition containing a hypothesis—for example, a value obtained through Classical.choose h. Ignoring that variable would hide the reference. Expand local
     definitions or traverse their dependencies transitively, retaining the mapping back to original hypotheses. Add a synthetic control covering this case.

  For the second review, require Check 2’s successful proof to be kernel-checked against the original quantified expression; an abstraction-based success should include checked specialization back to it.

  I checked the replay adapter, pinned fold, instrumentation, and l069/draw1 export structure. The sampled run’s 298 retained-file digests and the live-evaluation lock’s 45 source digests match. I did not run
  the proposed audit or Lean controls, and changed no files.
