# R6-013 outcome decision — 2026-09-23

Proceed with a versioned, observation-only instrumentation repair and **Option A**. Retain eleven posable sites, fifteen sites in the primary denominator, and the pinned tactic's existing behavior. No signing, live scheduling or spending is authorized by this decision.

## Consumption evidence

Add the missing successful-return receipt for the Int closer, and truthful closer-specific observations for any additional supported paths. Keep the original `instrument.py` and earlier fixture locks intact; derive a new overlay/version rather than editing a shared frozen file in place. Preserve the underlying closer dispatch, guards, certificate verification and proof construction. Record the actual closer, exact certificate binding and evidence path. Do not copy the Nat path's `residual_closer: omega` or other evidence fields onto extension paths without support from their implementation and observations.

The new receipt must follow successful consumption, not merely selection of a closer or certificate verification. Add controls for a removed or forged receipt, wrong closer/certificate, and closer failure without a success receipt. Exercise both Nat and Int successful paths natively. Unexercised extension instrumentation is not validated merely because those two paths pass.

For historical v5, retain l096/l099 as recorded kernel successes with missing explicit consumption receipts. The residual fold supports the code-path diagnosis; it does not retroactively supply the missing receipt. A bounded historical audit can accept that qualified record without treating it as a fully instrumented success. Never rewrite or synthesize a historical `reconstruction_finished` event.

## Reconstruction refusals and denominators

Keep l166, l175, l178 and l204 in the posable schedule. Their exact certificates are meaningful witness-generation targets even though this pinned reconstruction path rejects their goal shapes. The report should separate:

- request admission and arithmetic certificate feasibility;
- generated-witness verification;
- reconstruction attempted and selected closer;
- successful certificate consumption;
- local and containing-declaration validation.

For the observed failure path, use `reconstruction_refused` with a specific diagnosis such as `nat_closer_int_goal`, rather than an undifferentiated model failure. Derive it from a bound successful preparation/input check, accepted certificate, actual branch evidence and retained goal-shape failure/process record. A process crash, resource exhaustion, missing receipt or unrelated error must not qualify as this expected refusal.

The overall end-to-end denominator remains fifteen. Report the eleven posed sites, ten certificate-feasible sites, the negative control and the fixed closer-reachable stratum explicitly. A conditional six-positive-plus-negative-control view is useful as a predeclared diagnostic, not a replacement population. Assign limitations separately for each measured arm; another broker route may have a different reconstruction path.

The earlier requirement that every arithmetic-positive fixture finish both replays was a readiness target, not a scientific result to force. The checkpoint can now close with successful proofs **and correctly audited, explicitly classified failures**. The auditor accepting the integrity of a rejected episode does not make that episode a proof success. Do not change the tactic in this revision to improve these outcomes; any future closer repair is a separate method/version comparison.

## Auditor work

Extend the outcome kinds before producing controls. `cohort_v5_audit.py` currently hardcodes `term_mode_nat` for successful consumption and derives proof expectations directly from the classification's certificate-positive category. Both must distinguish arithmetic feasibility from actual closer outcomes.

Also split `history_v4:failures_repaired_in_v5`: it currently requires successful consumption for every repaired preparation mismatch. Establish preparation/reconstruction IR equality independently of downstream success. For l166/l175/l178/l204, record that execution reaches a later, different refusal. Preserve the full outcome sequence, receipt population and all ledger/accounting checks for failed reconstruction, including spent transmissions and absence of successful final validation. Missing final proof evidence is expected only on the appropriate failed path; fabricated completion must reject.

Keep all existing v4/v5 artifacts, record the new source lock and fresh run directories, and audit by revision. Re-run the native site rehearsals under the new instrumentation and then the exact-name-gated auditor controls. Previously passing proofs should remain accepted with unchanged axiom ceilings; any proof export change needs explanation rather than an automatic claim of observation-only equivalence.

## Review scope

This decision follows inspection of the pinned `e627efe` `runTermModeOnGoal` and `closeNatViaTermMode`, the frozen instrumentation, the v5 summaries/certificate-verdict records and all four retained closer error outputs. The missing Int receipt and Nat-dispatch/Int-target mismatch agree with the reported diagnosis. The draft auditor's receipt and history predicates were inspected directly. No full v5 audit, native rerun, live call or real-credential read was performed for this decision. This file is an implementation/research-design decision, not checkpoint approval.
