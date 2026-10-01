# R6 qualification 1, addendum 1 — the audit of the final step

Recorded 2026-10-01. This reports the audit that [R6 qualification 1](R6-QUALIFICATION-1.md) left open. It follows the
[proposal, revision 2](R6-QUALIFICATION-1-AUDIT-PROPOSAL.md) and the [build, revision 2](R6-QUALIFICATION-1-AUDIT-BUILD.md), in the
recorded order:
1. build revision 2 approved at `c116dbfd` ([approval](reviews/2026-10-01/R6-QUALIFICATION-1-AUDIT-BUILD-REVIEW-2.md));
2. locked as `qualification-audit-v1` (`eea12f40…`, commit `8bd84abf`);
3. controls C1–C9 re-run under the lock, all passing ([record](reviews/2026-10-01/R6-QUALIFICATION-1-AUDIT-CONTROLS.json));
4. the 48 audited ([record](reviews/2026-10-01/R6-QUALIFICATION-1-AUDIT.json)).

**The audit verified** the lock (the 48-slot selection and every consumed artifact) and `live-evaluation-v3` before and after, and
re-checked each export's digest as it read it. Nothing in R6's runs, records, locks, analysis, audit or counts changes.

## Result

| obligation | slots | classification |
|---|---|---|
| l069, l071, l078 | 24 | **certificate alone**: the final step refers to no hypothesis, and the certificate's weighted sum alone proves `0 < s`, hypothesis-free and kernel-checked |
| l070, draws 1–4 and 6–8 | 7 | **sufficient, but context referenced**: the weighted sum suffices (kernel-checked), but R6's proof of `0 < s` drew on `hZ`, `hZval` and `neg_goal` |
| l070, draw 5 | 1 | **sufficiency not established; diagnosis required** |
| l096, l099 | 16 | **unbound**: the residual binding failed, and no classification is made |

**By obligation:**
- three of the six proved obligations (l069, l071, l078) satisfy the stronger reading at all eight draws;
- l070 does not, at any draw;
- l096 and l099 are not determined by this audit.

**Consistency checks:**
- All 48 are locatable in both targets. Their local and whole classifications agree at every slot.
- Every export's shared constants matched `Init` up to annotations. The remaining declarations were kernel-checked through
  `addDecl` on 4.32.2. The counts vary by export and are retained in the audit record.
- Every established Check 2 was established **directly**: no atom generalization was needed, and no R6 slot had a definition to drop.

## What this means for qualification 1

- **For 24 of 48 slots (l069, l071, l078)** the stronger reading holds. The certificate's multipliers alone discharged the
  contradiction, and the final step used nothing else.
- **For l070 (8 slots)** R6's proofs drew on context at every draw. At seven, the certificate would have sufficed on its own. At
  draw 5, sufficiency is not established.
- **For l096 and l099 (16 slots)** the qualification's weaker meaning stands unchanged: the closer folded an independently verified
  certificate, and the kernel accepted the result.

R6-014's results are unchanged. "Consumed", in its strong sense, is now established for 24 of the 48 proofs, at three of the six
obligations.

## The 16 unbound slots: diagnosis, not results

**The cause is a naming artifact.** The retained residual goal names a variable `c_`, where the audited proof term has `c'`:
- l096 draw 1: retained `0 < 1 * (c + 1 - c_) + …`, audited `0 < 1 * (c + 1 - c') + …`.
- l099 is the same, with the roles reversed.

R6-013's preparation repair renamed unsafe local names at exactly these sites for the search context ("Renamed: the rows of l096,
l099 and l178"). The frozen checks kept the original names, so the site printed the renamed context, while the export carries the
original binder. Under the frozen rule, exact equality, these slots are unbound.

**Diagnostic values, which are not results.** The record also holds their Check 1 and Check 2 values: Check 2 established, with
`hlt` or `hgt` and `neg_goal` referenced. They are not claimed.

Classifying these slots needs a binding rule that accounts for the recorded renaming. R6-013 records the renamed context by local
index. That rule would be an amendment to the audit, proposed and reviewed separately. It is not applied here.

## l070 draw 5: sufficiency not established

- **The direct attempt fails.** `omega`'s counterexample treats two products that print identically, `↑Zmax * ↑zhigh.val`, as two
  distinct atoms.
- **The abstraction also fails,** with atoms `Zmax * 2 ^ 16`, `Zmax * zhigh.val` and `Zmax * zhigh.val`, the last appearing twice.

This points to incomplete normalization: distinct terms that print identically. That is one of the causes the proposal names. It
does **not** establish contextual dependence, or a mismatch between R6's rows and the Lean terms.

This draw's witness is the only l070 witness that uses product-atom facts (`hprod_le`, `_pb_nonneg_atom_4`). Comparing the two
subterms exactly is a separate diagnostic step, and has not been taken.

## An observation at l070

l070's eight draws carry four distinct witnesses, yet the hypotheses R6's final step referred to are the same at every draw: `hZ`,
`hZval` and `neg_goal`. Contextual `omega` derived `0 < s` from the same facts whichever certificate the closer folded. l070 is also
the site exposed before the census (the R6-000 control). No inference is drawn from that coincidence.

## Disclosure, and what follows

**Disclosure.** As disclosed in the build record, one of these exports (l069 draw 1) was read while the tool was prototyped. The
audited result for it, certificate alone, is the one the prototype showed.

**Proposed, not started:**
- a binding rule that accounts for the recorded renaming, as a reviewed amendment to the audit, so that l096 and l099 can be
  classified;
- a diagnosis of l070 draw 5's split atoms;
- a sharper version of the synthesis's dated qualification sentence, citing this addendum. That is the author's decision.

**For R6-015.** The constrained final step is expected to pass for l069, l071 and l078, whose sums suffice hypothesis-free. l070
draw 5 shows that the normalizer must identify cast and product atoms consistently.
