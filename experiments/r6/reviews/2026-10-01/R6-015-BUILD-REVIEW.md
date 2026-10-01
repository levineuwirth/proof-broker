# R6-015 build, revision 1 — implementation review

Supplied by the reviewer in session on 2026-10-01, against build revision 1 (`4bcf4a18`, bridge `aa32cf21`). It is recorded
verbatim below. The reviewer's reproducer was left at `/tmp/R6015Hint.lean`, with its audit report at
`/tmp/R6015Hint-production-report.json`; neither is retained here. The synthetic regression added in build revision 2 is
modelled on it.

---

Request changes: one P2 finding before step 2 approval.

  The hypothesis guard checks a different term from the one returned. In lean-bridge/ProofBroker/Tactic.lean:3388, it checks proof, then returns mkExpectedTypeHint proof  
  ty. That constructs @id ty proof, which can introduce hypothesis references through the original type.

  I reproduced this with a cast instance castViaHyp (_h : True) := instNatCastInt. The constrained closer succeeds, including through option-enabled proof_broker_term     
  [cvc4], but the exported positivity proof references tag : True. The locked audit reports tag in both targets, so control 8 fails. Kernel checking succeeds; the defect  
  concerns the frozen dependency predicate. See the reproducer (/tmp/R6015Hint.lean) and production audit report (/tmp/R6015Hint-production-report.json).

  Build the typed term before the dependency check, run both gates on that exact term, and return it unchanged. Add a synthetic regression for a hypothesis-dependent cast 
  instance.

  The five implementation choices are otherwise acceptable: the option, instance-transparency atom identity, term_mode_int reporting, Int facts in the constrained Nat/    
  False path, and the closer’s own kernel check. Document instance transparency precisely: it also unfolds reducible definitions. The harness must freeze the option       
  setting and explicitly name the constrained final step in receipts.

  Verification reproduced:

  • All nine supplied synthetic audit pairs behaved as recorded.

  • Test.TermModeConstrained, Test.Tactic, and Test.TacticStress passed.

  • Additional probes covered production routing, negative equation multipliers, cast powers, let-hidden dependencies, and kernel rejection of incorrect arithmetic        
    reflection.

  Mathlib and corpus suites remain untested. No retained certificate was read or replayed, and the working tree is unchanged.
