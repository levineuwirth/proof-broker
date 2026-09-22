# R6-011 review and contract decision at 27579e5

**Select C as an admission rule, preserving unique references. Do not freeze an eleven-site schedule from the current classification.** The arithmetic classification has one substantive error: l178 has a rational certificate over its distinct emitted rows, but those rows have ambiguous names. Ten sites are candidates under C with the current name-addressed boundary; l178 and the four SDK refusals remain in the fifteen-site primary population as unposable for the learned arm. Final eligibility still requires the new independent projection and executing gate.

## P1 — duplicate names invalidate the l178 nonexistence claim

`site_representability.py:45` builds `by_name` from the row list. Two different l178 rows are named `this`; the first is overwritten. The columns then refer twice to the second row. `check_certificate` repeats the same name-based lookup at line 89, so checking the solver against that checker does not protect against this error. The classifier also omits the unique-name admission check that `payload.validate_request` enforces.

The actual zero-based rows 7, 8 and 11, with coefficient 1 each, are:

| Index | Name | Left side, constrained ≤ 0 |
| --- | --- | --- |
| 7 | this | Zmax − v |
| 8 | this | v0 − Zmax |
| 11 | neg_goal | 1 + v − v0 |

Their sum is **1 ≤ 0**, with every variable cancelled. The frozen classifier returns `None`; changing only the analysis labels to unique row indices makes it find this certificate. This establishes arithmetic existence, not an admissible name-addressed SDK certificate or a reconstructed Lean proof. The missing `hzh` is not needed for this contradiction.

[Read-only reproduction](site_review_checks.py) and [results](R6-011-REVIEW-CHECKS.json) bind this calculation to the retained prepared bytes. Preserve the v1 classification as history and correct its interpretation in an addendum. In the next locked classifier, use row indices for mathematical feasibility and report name-addressability separately. An ambiguous input must fail admission explicitly. Add controls with distinct rows sharing a name, and require the name-addressed certificate checker to reject ambiguity instead of selecting either row silently.

For this cohort, keep l178 unposable under the existing name-addressed interface. A future identity repair must preserve the reference through IR, model proposal, SDK assembly/verification and the original Lean local context; renaming only the model payload is insufficient. Such a repair deserves its own native control before adding this site to an execution schedule.

## Arm-specific attribution correction

R6-011.md option B says l170 and l178 are interface failures “for both arms.” That does not follow. l178's arithmetic diagnosis is false; l170's diagnosis concerns the emitted row set. Independently, l170's rows admit the exact integer assignment `Zmax = 1`, all other emitted variables zero. The review record evaluates every row, including `neg_goal`, so this nonexistence result does not depend on the new simplex returning `None`.

A deterministic route using the same rows and certificate format has the same arithmetic limitation. A broker route using fuller IR, different theory handling, or another evidence path must be measured separately. Keep admission, mathematical feasibility, addressability, search outcome and reconstruction outcome separate per arm. Do not pre-fill the deterministic arm with a failure inferred from the learned interface.

## Contract decision and next implementation

- Keep all fifteen sites primary, the four family summaries, and the already recorded exposure and sensitivity strata. Do not select by certificate existence or either arm's success.
- Adopt C: accept independently checked arithmetic rows even when the source fragment is UF or hypotheses were omitted; extend the independent projection to negated comparisons. Preserve the original fragment and omissions in evaluator evidence. This does not claim complete representation of the original theory.
- Preserve all other admission checks: canonical integer rows, supported `le`/`eq` relations, unique references and exactly one correctly bound negated goal. Independently derive the included arithmetic subset and omissions; merely trusting the SDK omission list and skipping those names is insufficient. Include controls for omitted/replaced rows and the strictness and direction of negated comparisons.
- Candidate learned sites are 069, 070, 071, 078, 096, 099, 166, 170, 175 and 204. There are nine with arithmetic certificates and one, l170, with an independently demonstrated feasible row set. l178 is an identity limitation; 098, 101, 158 and 180 are SDK goal-form refusals. These are interface-based categories, not task removals. Confirm them through the new gate before freezing the schedule.
- l170 can be a predeclared negative control under the same request and budget rule. Report it separately from certificate-feasible proposal performance. Its invalid responses are not evidence of failure to discover an existing witness. Keep overall system coverage and success denominators at fifteen; label every conditional denominator.
- The full broker versus learned-row comparison measures systems with potentially different available information. Any claim about the marginal value of learned witness search needs a deterministic comparator on the same rows and evidence path. Keep the exact feasibility oracle and its witnesses evaluator-only.
- The in-process task registration and supervisor shim are acceptable adaptation boundaries. Freeze and retain their source identities in the new driver, verify before stages execute, preserve control tasks and conflicting-registration rejection, and keep the one-line stage-difference control. Bind the actual exposure-addendum bytes or re-derive them at admission; checking only its embedded census and decision digests does not authenticate its classifications.
- Continue with the new disabled contract/gate/driver revision and canned reconstruction/final-validation rehearsals. Exercise omitted-hypothesis/UF cases, l166's negation, the signed equality coefficient in l175, the negative control and ambiguous-reference refusal. Arithmetic certificate existence is not yet successful consumption or replay. This decision authorizes no signing, credential access or provider spending.

## Verification scope

R6-010's two follow-up gaps are closed: freshly ran the 157-case public census audit and all 24 controls, including the four review probes, at their intended boundaries. Freshly ran the 12 R6-011 controls; all passed, including retained seals/event chains and classification re-derivation. Those tests share the classifier's duplicate-name error, which is why independent row arithmetic matters.

Verified the current fixture v1, cohort v3, census v1 and site v1 source-lock entries against disk. The review calculations confirm only l178 has duplicate row names among the eleven prepared problems. No native preparation, Lean replay, model call or credential operation was rerun. Only new non-locked review files were written; implementation, frozen runs and locks remain untouched.
