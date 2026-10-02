# R6-016 bridge build, revision 1 — implementation review

Supplied by the reviewer in session on 2026-10-02, against build revision 1 (`bdfc1c97`, bridge `84ea4634`). It is recorded
verbatim below.

---

 Request changes before bridge approval: two P2 findings.

  1. The exponent cap does not bound numeral evaluation. The evaluator (lean-bridge/ProofBroker/Tactic.lean:3258) accepts ((2 ^ 1024) ^ 1024) and computes a 1,048,577-bit numeral. Further nesting grows substantially while every exponent remains within
     the cap. Add a size budget checked before arithmetic evaluation, including nested powers, and pin its boundary behavior. Update the build record’s claim about preventing large powers.

  2. The promised axiom pins are incomplete. The tests (lean-bridge/Test/TermModeConstrained.lean:250) cover representative lemmas, while proposal section 2 promises the full route inventory and listed core helpers. Add guarded checks for that        
     inventory. I checked them independently: all currently satisfy the required axiom bound.

  Interpretations 1 and 3 are acceptable. Keep interpretation 3’s limitation explicit: ↑(a*b) * ↑a does not currently meet ↑(a*b*a) under this atom policy, although the expressions are arithmetically equal.

  Verification passed: the three reported test suites, all eleven synthetic audit reports reproduced exactly, production constrained routing, additional atom probes, and both overlays. The exact typed-term gates remain intact.

  The amended audit and its synthetic controls can continue. No retained R6 certificate was read or replayed; the working tree is unchanged.
