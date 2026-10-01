# R6 bridge revision 2 and qualification audit amendment 1, build revision 3 — implementation review

Supplied by the reviewer in session on 2026-10-02, against bridge build revision 2 (`43abfa54`, bridge `64585867`) and the
amended audit's build revision 3 (`65e7c8bd`). It is recorded verbatim below.

---

 Bridge 64585867: approved. Audit amendment 65e7c8bd: changes required before locking.

  I reproduced the three bridge test suites and all eleven synthetic audit reports. The numeral budget and complete axiom inventory address the previous findings.

  The amended audit’s declared controls reproduce exactly, but additional synthetic probes exposed five issues:

  1. P1 — The walk can hide another fold. At experiments/r6/qualification-audit-v2/Audit.lean:438, a successful walk searches only w.body, omitting folds in definitions and applied-lambda arguments it peeled away. My exported example contains two     
     farkasContradictN applications: v1 refuses it as “2 fold applications”; v2 reports certificate_alone at both targets. Preserve the whole-value uniqueness check while using the walked context for parameter mapping.

  2. P2 — An applied lambda’s definition is unavailable to type comparison. experiments/r6/qualification-audit-v2/Audit.lean:358 introduces q as a plain variable, recording its value only in the dependency map. Consequently, (fun q => fun (h : 0 < q) 
     … => …) x incorrectly fails the comparison with the declaration’s h : 0 < x. Introduce an actual local definition, or resolve the recorded definition during comparison. Add a dependent-binder control.

  3. P2 — Renamed sources are exempted from the collision rule. The exception at experiments/r6/qualification-audit-v2/Audit.lean:416 permits destinations naming another binder when that binder is also renamed. Swapping x and c' binds successfully in 
     my probe. The frozen rule requires refusal whenever a destination names another binder. Remove that exemption and pin the swap case.

  4. P2 — A failed regression does not stop later applications. experiments/r6/qualification-audit-v2/qualification_audit_v2.py:267 requires no passing regression record. With stand-in evidence, regression returned failure and addendum 2 still wrote  
     its output. Require verified passing regression evidence under the current lock before subsequent applications.

  5. P2 — The lock does not bind the toolchains’ contents. experiments/r6/qualification-audit-v2/qualification_audit_v2.py:210 records literal version names without compiler or runtime digests. Changing both toolchain paths leaves the lock record     
     unchanged. Bind and recheck the toolchain artifacts actually used, including the imported environment.

  Your readings a, b and d are acceptable. Reading c’s scope is acceptable, subject to fixing the collision exception.

  The dry selection contains exactly 32 regression, 16 addendum-2 and 17 l175 slots. No retained export was audited, no lock was written, and the working tree remains clean.
