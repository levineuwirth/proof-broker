# R6 qualification 1 audit — build, for implementation review

**Build revision 2**, 2026-09-30. It responds to [the implementation review of revision 1](reviews/2026-09-30/R6-QUALIFICATION-1-AUDIT-BUILD-REVIEW.md),
which found two P1 defects and two P2 gaps. Revision 1 is `8a8bbeae`. The build follows [the proposal, revision 2](R6-QUALIFICATION-1-AUDIT-PROPOSAL.md).

**Status:**
- Controls C1–C9 pass their frozen expectations ([pre-lock record, revision 2](reviews/2026-09-30/R6-QUALIFICATION-1-AUDIT-CONTROLS-PRELOCK-2.json)).
- **Nothing is locked, and the 48 have not been audited.** `audit` refuses without a lock; this was checked again.
- The 48-slot selection was computed once as a dry run, to show that the lock step works: 48 slots, 6 target pairs, every consumed
  artifact matching its run's seal. That run hashed the exports but did not parse them.

## A retraction

**Revision 1 claimed that 4.32.2's `Init` differs from the export's in 218 shared constants, "including `omega`'s own lemmas", and
rejected 4.32.2 on that basis. The claim was wrong.** The 218 came from raw equality on 4.32.2, before I found that the differences
are annotations the exporter strips. The comparison was never repeated on 4.32.2 with annotations erased.

The review built the tool on 4.32.2 and found the same shared-constant counts as on 4.32.0; so does this build. Revision 2 is built
on **4.32.2**, the kernel of R6's final validation. The per-export equality check makes the choice immaterial for any export that
passes it; the review's caution stands that this does not establish compatibility for every R6 export in advance.

## What changed

1. **P1: the environment comparison covers the complete declaration.** Every expression in a `ConstantInfo` is erased of what the
   kernel ignores, recursor-rule right-hand sides included. Every other field is then compared by `==`: recursor rules and their
   `nfields`, constructor fields, inductive metadata, hints, safety, `all`, and so on. Generated constructors and recursors are
   compared the same way.
   - **C7** is the review's mutation: C2's export with `Nat.rec`'s first rule's `nfields` changed from 0 to 1. It is refused
     ("constants differ from Init beyond annotations: `Nat.rec`").
2. **P1: binding gates classification.**
   - **Real mode** requires the run's retained residual goal. If `hpos`'s pretty-printed type differs from it, both targets are
     classified `unbound_residual_mismatch`, and no sufficiency classification is made.
   - **Synthetic controls** run in an explicit `--synthetic` mode, with binding `not_applicable_synthetic`.
   - **C8** is C2 in real mode with a wrong residual; both targets are unbound.
   - **C9** is C2 with its exact residual (`0 < 1 * (x - y) + 1 * (y + 1 - x)`); it binds and classifies.
3. **P2: dropping definitions is a generalization.**
   - The **original** statement is `hpos`'s type closed over its free variables with local definitions **retained**. At C5 it is
     `∀ h, let v := Classical.choose h; 0 < …`.
   - `omega` is asked only for the *attempted* statement, with definitions dropped: `∀ v : Int, 0 < …`.
   - A kernel-checked specialization instantiates that theorem at the let-bound variable, against the original. No `omega` runs in
     the original context.
   - Check 2 is **established** only when a kernel-accepted theorem whose type is exactly the original exists. The atom abstraction
     composes the same way: atoms back to the attempted statement, then definitions back to the original.
4. **P2: the lock freezes every audit input.** The lock binds:
   - the analysis file that selects the 48, by path and digest;
   - the selection itself: for each slot, its run, its local and whole targets, and its retained residual goal;
   - the digests of each run's `seal.json`, `solution.ndjson.gz` and `events.ndjson`, each also checked against the seal;
   - the tool, the sources, the control exports, the exporter and the toolchains.

   `audit` recomputes all of it **before and after** (`verify_lock`), verifies `live-evaluation-v3` before and after, and checks
   each export's digest again as it reads it.

The review accepted C6's mechanism and the internal-hypothesis labels, and confirmed that the fold copy matches `e627efe` byte for
byte.

## The controls, pre-lock (revision 2, on 4.32.2)

| control | result | expectation |
|---|---|---|
| **C1**, the review's probe | `h` referenced; Check 2 not established | met |
| **C2**, valid, with unused `hu1`–`hu3` | `h`, `neg_goal`, not `hu1`–`hu3`; established | met; Check 1 kept |
| **C3**, casts and a product | established directly; the abstraction (`x * y`) and its specialization accepted | met |
| **C4**, the exported structure | local `h`; whole `hpq` through parameter 2, not `hextra`; the targets agree | met |
| **C5**, a let-bound value | `h` through `v`; `v`'s definition dropped and restored by a checked specialization; established against the original | met |
| **C6**, a lossy abstraction | established directly; the abstraction (`x % 2`) not established; counts as sufficient | met |
| **C7**, `Nat.rec` mutated | refused | met |
| **C8**, a wrong residual | `unbound_residual_mismatch`, both targets | met |
| **C9**, the exact residual | binds; classified | met |

The shared-constant counts on 4.32.2 are:
- C1–C4: 1,283 identical and 170 equal up to annotations;
- C5 and C6: 1,245 and 1,309 identical, and 170 and 174 up to annotations;
- 0 different in every case.

## Unchanged from revision 1

- The disclosure: one R6 export (l069 draw 1) was read while prototyping, and its Check 1 showed no hypotheses. No other has been
  read since.
- The observation that even a valid certificate can show "hypotheses referenced": a valid certificate's own hypotheses are jointly
  contradictory in the fold's context, and contextual `omega` can use them (C2).
- The files, in [`qualification-audit/`](qualification-audit/): `Audit.lean`, `make_controls.py`, the generated controls with their
  provenance, and `qualification_audit.py`.

## For the implementation review

1. The four repairs above, against the review's findings.
2. That **every established Check 2 is a kernel-checked theorem whose type is the original statement**, definitions retained,
   through every composition of generalizations.
3. The lock's contents, and the before-and-after verification in `audit`.

**After approval:** lock, re-run the controls, run `audit` on the 48, and record the result and the addendum to qualification 1.
Then R6-015 is frozen.
