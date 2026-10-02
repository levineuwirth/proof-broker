# R6 qualification audit amendment 1, build revision 4 — implementation review

Supplied by the reviewer in session on 2026-10-02, against the amended audit's build revision 4 (`acc9432d`). It is recorded
verbatim below.

---

 The three Lean-side repairs pass re-review. Two P2 issues remain in the driver before lock approval.

  I reproduced all controls and twelve gate tests, including my original dependent-binder and two-fold probes. The recorded reports and digests match exactly.

  1. P2 — The regression gate checks classifications but ignores execution validity. At the regression check (experiments/r6/qualification-audit-v2/qualification_audit_v2.py:299), matching
     classifications and mappings pass even when a stored report has exit: 1, a boolean exit, a refused field, synthetic mode, or unbound/nonlocatable targets. I reproduced these acceptances with   
     synthetic records.

     Validate each report before comparing results: integer exit zero, no error/refusal, real mode on the frozen Lean version, successful residual binding, and both targets locatable. Use that same 
     validation when producing the regression verdict and when checking its record.

  2. P2 — Import binding uses the wrong search precedence. At the import resolver (experiments/r6/qualification-audit-v2/qualification_audit_v2.py:258), a module is skipped whenever it exists in the
     toolchain. Lean searches the supplied LEAN_PATH directories first. Adding or changing a bridge-side Init.olean leaves your binding unchanged, although Lean would select that file.

     Resolve imports using the compiler's actual search order, or refuse toolchain-module shadows in higher-priority directories. Include the controls directory in that check.

  For e, reading and recomputing the regression record is appropriate once its reports are validated; rerunning it inside the gate is unnecessary. The stated controls-first order remains required.  

  For f, binding only the imported closure is appropriate once resolution follows Lean's actual search path.

  The dry lock reproduces 32/16/17 slots, both 14,710-file toolchain inventories, and the current one-module bridge closure. No lock was written, no retained export was audited, and the working tree
  remains clean.
