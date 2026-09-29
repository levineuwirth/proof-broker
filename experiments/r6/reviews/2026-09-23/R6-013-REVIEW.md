# R6-013 / cohort v6 review

Reviewed commit: `24332120` (harness `7a82fed3`, decision `9cbc2d83`).

The retained outcomes hold under recomputation, but four P2 audit gaps remain. Six independent, coherently resealed mutations pass the complete 628-case auditor. These are failures to reject contradictory evidence, not evidence that the original executions or Lean proofs are wrong. The repairs can be made in the non-locked auditor and its controls; these findings do not require a tactic change, new freeze, native rerun, or live authorization.

The reproductions are in [cohort_v6_review_probes.py](cohort_v6_review_probes.py) and [R6-013-REVIEW-PROBES.json](R6-013-REVIEW-PROBES.json). Each mutation uses a fresh copy, first requires the unmutated full audit to pass, changes one relationship, and uses the existing control helpers to regenerate the publication record, terminal commitment and seal (or the historical seal). All six mutated copies still return `accepted: true`, `case_count: 628`. They do not modify the retained original runs.

1. **P2 — Refused reconstruction skips certificate and dispatch bindings checked on successful reconstruction.**

   In [cohort_v6_audit.py](../2026-09-22/cohort_v6_audit.py), `reconstruction_common` (lines 1131–1157) checks the certificate in the selected-closer, reconstruction-start and verification-finished records. It does not check the `dispatch_received` certificate or final IR, or the verification-start certificate. Those comparisons are in `site_shared_checker` (lines 1089–1093), which refused runs never enter.

   Three separate mutations of `l204-draw1` replace, respectively, `dispatch_received.certificate`, `dispatch_received.final_ir`, and `certificate_verification_started.certificate` with `{"review_probe":"different_evidence"}`. Each still passes the full audit and qualifies as the diagnosed closer refusal.

   Move the shared reconstruction evidence checks before the success/refusal split: packet certificate, final IR and trace; every certificate-bearing observation; dispatch settings; and the child component/stage boundaries. Keep certificate validity, IR equality, branch selection, refusal diagnosis and completed consumption as separate predicates. Add one control per binding on the refused path. A valid final verifier receipt must not excuse contradictory earlier receipts.

2. **P2 — Consistently relabeling the successful Int closer as Nat is accepted.**

   `proof` (lines 1182–1187) and `site_shared_checker` (lines 1095–1097) compare closer labels to one another and require membership in `CONSUMING_CLOSERS`. Neither derives the branch from the bound input and pinned dispatch logic.

   On `l099-draw1`, changing the selected closer, finished closer and verdict closer from `term_mode_int` to `term_mode_nat`, then rebinding the verdict receipt and finalizing, passes all 628 cases. The Int comparison and the IR are unchanged. Thus the auditor accepts a false attribution even though one-field mutations correctly fail.

   Derive the selected branch from the pinned dispatch predicates, bound IR, goal carrier and applicable extension configuration, then compare the observations and verdict to it. Add a control with all closer mirrors changed together, leaving the underlying branch inputs unchanged. This concerns consistency with the recorded program and inputs, not inference attestation.

3. **P2 — The reconstruction command can name another site's evidence packet.**

   `command_reconstructed` (lines 700–734) reconstructs the HTTP sender command. `stage_outcomes` (lines 755–775) checks other stages' populations, outcomes and resource limits, but does not bind their argv inputs to the files whose contents the auditor checks.

   In `l204-draw1/stages/reconstruct/command.json`, changing only the source of the read-only `/evidence.json` mount from `l204-draw1/evidence.json` to `l070-draw1/evidence.json`, then finalizing, passes all 628 cases. The audit therefore accepts an invocation record that contradicts the claim that reconstruction used this run's packet.

   Reconstruct the reconstruction command against the recorded root and run layout, pinned executable/environment and exact task inputs. Check the analogous certificate-check, assembly, export and replay command bindings as part of the same review; their saved inputs and reports should be joined to their recorded invocations. A hash of an arbitrary command is not that binding. The demonstrated defect is in the reconstruction mount; no claim is made here that the original process used a different packet.

4. **P2 — Historical qualified kernel success is not bound to the replayed declaration.**

   `history_v5` (lines 1400–1411) calls the v5 l096/l099 outcomes qualified kernel successes based on the normalized verdict's acceptance flags, empty axiom-delta values, summary and receipt absence. It does not compare the target identity or normalized verdict to the retained raw replay reports.

   Changing `l096-draw1/verdict.json` in the v5 history so that `final_validation.local.targets[0].name` is `Unrelated.theorem`, rebinding its verdict receipt and historical seal, still passes the complete audit. The raw replay report and kernel receipt continue to name the real target. The auditor reports qualified kernel success despite this contradiction.

   Normalize the retained raw reports and check the expected site's target, type, axioms and receipt/verdict equality, while preserving the explicit missing-consumption-receipt qualification. Alternatively, a strictly preservation-only history check needs an independently pinned inventory and narrower wording. Resealing a self-consistent container does not establish its historical proof claim. No Lean rerun or retrospective consumption receipt is needed.

The independent recount in [R6-013-REVIEW-RECOUNT-REPRODUCIBLE.json](R6-013-REVIEW-RECOUNT-REPRODUCIBLE.json), reproducible with [cohort_v6_review_recount.py](cohort_v6_review_recount.py), found:

| Population | Runs | Event hashes | Retained seal entries | Recorded proof successes |
| --- | ---: | ---: | ---: | ---: |
| v4 | 13 | 447 | 3,449 | 4 |
| v5 | 16 | 547 | 4,158 | 6 |
| v6 | 16 | 559 | 4,178 | 6 |

All event chains and retained seal entries recomputed without a mismatch. The six v6 compressed proof exports are byte-identical to v5; the decompressed export digests also match, with the same empty axiom deltas. All fifteen sites' input IR, preparation reification and captured context are byte-identical between representability v3 and v4; all eleven available prepared records are too.

The fresh public audit accepts 628 exact-name-gated cases. It reconstructs the v6 ledger at eleven consumed transmissions, one release and no open reservation, and reports the separate 15/11/10/1/6/4 populations. A fresh site-control run passes all twenty cases, including the exact observation-only overlay reversal and unchanged preparation outputs. The full [audit-control rerun](R6-013-REVIEW-CONTROLS.json) passes its exact 77-case population: one accepted baseline and 76 mutations rejected at their expected cases. The six additional accepted mutations above are outside that existing population. [R6-013-REVIEW-EVIDENCE.json](R6-013-REVIEW-EVIDENCE.json) binds the review programs and JSON records by digest.

Three wording corrections:

- `R6-013.md:178`: 77 controls comprise one accepted baseline and 76 rejected mutations. The baseline was not rejected.
- The six sites now passing the IR comparison comprise five historical IR-guard failures plus l178's historical ambiguous-reference refusal. The machine-readable history distinguishes them; keep that distinction when describing the six-site comparison.
- `R6-013.md:65`: four previously posed requests change only their IR bindings. l096 and l099 also change `problem.rows[0].terms[1].variable` and `problem.rows[1].terms[1].variable`. The recount regenerates both request bodies and records the differing fields. Their mathematical meaning is preserved, but the row bytes also change.

Scope: source inspection, retained-artifact recomputation, existing non-native controls, and independent mutations on temporary copies. No overlay build, Lean replay, native episode, real-credential read, provider call, signing, commit or push was performed. Historical process and kernel reports remain recorded evidence; this review does not newly attest their execution.
