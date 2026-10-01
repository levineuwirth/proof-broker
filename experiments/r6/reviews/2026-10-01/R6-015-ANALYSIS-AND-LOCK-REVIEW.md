# R6-015 analysis, control 3 and lock — review

Supplied by the reviewer in session on 2026-10-01, against `a335a054`. It is recorded verbatim below.

---

 Request changes before locking: two P1 findings and one P2.

  1. P1 — negative controls can pass on harness failures. experiments/r6/r6-015/analysis.py:179 accepts any non-proof after a recorded bypass. A synthetic scenario with all 24 invalid mutations and injected l170 ending in 
     harness_failure still returned complete_success.

     Require the constrained closer to reach the final step: “does not cancel” for control 1, and “not positive” for injected l170. Earlier refusals and harness failures require diagnosis and must fail these controls.     

  2. P1 — control records’ summary flags substitute for evidence. experiments/r6/r6-015/analysis.py:139 trusts unmet: []; controls 3 and 8 trust passed. Synthetic probes still returned complete_success with:
      • refused audit reports beneath unchanged summary flags;
      • contradictory control-3 results and nonempty unmet;
      • all 33 non-proof entries missing from control 8.

     Recompute the predicates from retained evidence. Bind control-8 results to the current runs’ seals and export/residual digests, require exact plan coverage, and verify control 3’s identity, provenance and results.    
     Reject dry-run or incomplete records. Recheck consumed analysis inputs afterwards.

  3. P2 — excluding control 5 changes the frozen outcome definition. Revision 5 (experiments/r6/R6-015-PROPOSAL.md:260) says complete success requires every control to behave as frozen. I recommend keeping the 36-         
     certificate measurement separate while requiring the 10 expected-pass regression entries for overall complete_success. The four entries without predictions remain diagnostic. Make that distinction explicit before     
     locking.

  On your other choices: axiom removals are acceptable; retain their deltas in the analysis. A bound harness failure means not consumed and requires diagnosis; it must not satisfy a negative control.

  The supplied tests pass. The lock inventory, all 108 source-artifact checks, and isolated mutation checks passed. No lock was written, no closer ran, nothing was replayed, and the working tree is unchanged.
