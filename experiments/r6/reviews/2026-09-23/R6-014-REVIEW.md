# R6-014 review at 9c5c1d54

Checkpoint not approved for signing. The recorded baselines reproduce, but the probes below expose seven gaps. Production remains disabled; there is no production checkpoint or live ledger. All signing tests used isolated temporary policies and synthetic authority. No real credential was read, no provider connection was made, and no frozen file or retained run was changed.

1. **P1 — Resuming signing can recreate an established live ledger and reset consumption.**

   Locations: `cohort_contract.py:379–418`, `cohort_ledger.py:216–237`.

   On an isolated policy frozen and signed through production functions, I reserved D1/1, committed its synthetic grant, and reconciled it as consumed. Reserving that slot again correctly failed with `cohort_slot_consumed`. I then moved the entire established live directory aside, preserving it, and repeated the identical `sign` call. It succeeded: consumption went from 1 to 0, and the same D1/1 slot could be reserved again.

   `signing_complete` treats unavailable established authority as incomplete signing; `ensure_activated` treats missing ledger and head as a first activation. Neither distinguishes loss of completed authority from interruption before activation. This contradicts the decision and §1's “never … resets consumption” claim.

   Recovery needs durable lifecycle evidence that distinguishes these states. Once activation has completed, losing its ledger must fail closed, including when its slot directory is lost with it. Retain a control that first demonstrates the spent-slot refusal, then removes established authority and requires re-signing to refuse; separately retain interrupted-first-activation positives. Do not repair this by silently starting a new campaign.

2. **P1 — The live auditor's accepted fixture is not the production signing state.**

   Locations: `cohort_v7_audit.py:187–200,349–385,396–425`.

   `eligibility` reads `ROOT/policies/farkas-cohort-v7.json` rather than the configured policy directory, and requires its execution schedule to be eight draws for every posable site. The fixture passes because the production file is still disabled with that schedule. Redirecting only that read to the fixture's genuinely signed draw-1 policy makes the otherwise accepted 549-case audit reject at `eligibility:recomputed_fifteen_sites`. That is what actual production signing will do to the file it reads.

   There is a second incompatibility with the required pricing refresh. Production `sign` accepts a different admissible capture and preserves the original disabled checkpoint. `signed_state_ok` requires all pricing fields and source paths to be identical to that checkpoint. An isolated production freeze/sign with a distinct admissible copy of the retained capture succeeds, but the auditor's signed-state predicate returns false. This probe uses identical source bytes; it makes no claim about a newly fetched price. `revision_bindings` also hardcodes capture 3 and its precise prose-difference record. The single-revision ledger predicate cannot accommodate the later authorization/pricing revisions described by the signing design.

   Read eligibility from the reviewed scientific population and planned schedule; validate execution scope separately against the configured signed authorization. Bind refreshed pricing and revision history using their retained records and admission rules. Before locking the live evaluator, demonstrate a production-layout draw-1 signature with a distinct admitted capture, and the intended later-revision path, on canned evidence.

3. **P1 — Contradictory per-file disclosure evidence is accepted as publication-clean.**

   Location: `cohort_v7_audit.py:1879–1915`.

   Three independent mutations of the scan entry for `runs/l069-draw1/accounting.json` each still pass all 549 live-audit cases: `scanned: false`; a non-null `error`; and a nonempty `findings` list. Each preserves the authentic file digest and leaves the report's top-level clean summary unchanged. They are separate probes, not a bundled mutation shadowed by its first rejection.

   The auditor checks the top-level conclusions, then reduces entries to a path→digest map. That proves byte coverage but discards whether those bytes were successfully scanned and whether a disclosure was recorded. Reconstruct cleanliness/completeness from the entry records, require the summary to agree, and reject duplicate or conflicting entries. This does not require the auditor to read the credential: it requires the operator receipt to be internally consistent.

4. **P2 — The deterministic arm lacks a sufficient independent artifact audit.**

   Locations: `test_site_broker.py:124–174`.

   The existing eight controls pass against the original records. They also pass with `deterministic.json.sites = []` and no run trees at all: the population assertion sits inside the loop whose population it is supposed to guard. A separate mutation keeps all thirty runs, changes l070's local target type digest to 64 zeroes, and coherently updates the verdict→outcome→summary/terminal→seal bindings. All eight controls still pass. `proofs_recomputed` checks the claimed acceptance, name and empty axiom delta but never compares the type against the frozen obligation or derives the verdict from the raw replay report; its loaded `expected` value is unused.

   Add a non-locked retained-artifact auditor with an independent exact 15×2 population, and carry over the applicable source, command, stage, certificate, export, raw replay/type/axiom, receipt and outcome bindings. Give this arm independent mutation controls rather than relying on its native execution and seals. The probes show missing validation, not that the original native results are false; a retained-evidence repair need not itself rerun those episodes.

5. **P2 — Unknown usage becomes zero, and the reported cost “ceiling” rounds down.**

   Location: `analysis_r6.py:167–171`.

   Eleven consumed slots with all usage fields `null` produce token totals 0/0/0 and `priced_ceiling_micro_usd: 0`. `usage_observed_slots: 0` exposes the missingness but does not make that numeric ceiling correct. Partial usage is also silently zero-filled or discarded according to whether input usage exists. A single reported cached input token costs 250 nano-USD at the frozen rates; integer floor division reports a zero-micro-USD ceiling.

   Preserve per-field unknowns. Distinguish known subtotals and coverage from a complete aggregate estimate; unknown total usage cannot establish a zero total cost. Keep exact nano-USD or round a micro-USD ceiling upward. Add all-unreported, partially reported and fractional-micro controls.

6. **P2 — The analysis accepts a changed denominator map.**

   Locations: `analysis_r6.py:71–80,104–121`.

   Removing l096 from `classes.posable_certificate` and coherently removing it from the supplied planned/authorized schedules is accepted. The analysis reports 15/10/9/1/5/4 instead of the frozen 15/11/10/1/6/4. It only fixes the primary count, the identity of l170, and containment of the four unreachable sites; the rest comes from the input under test. This contradicts the frozen specification's refusal of population/denominator inconsistencies.

   Bind exact unique populations and their partition to the reviewed classification, independently of the supplied schedules. Keep authorized subsets and partial collections legal without allowing them to redefine scientific membership.

7. **P2 — Ladder censoring can hide the negative control's integrity failure.**

   Locations: `analysis_r6.py:93–101,159–160`.

   Starting from the realistic complete canned input, change only l170's consumer observation to `true`, leaving verifier acceptance `false`. Analysis converts consumption to `null`, reports no false acceptance, sets `integrity_stop: false`, and permits continuation. Its definition says *any verifier or consumer acceptance* of the negative-control contradiction is an integrity stop; computing that predicate after censoring loses the anomalous observation.

   Reject contradictory stage observations, or derive integrity flags from raw observations before forming conditional stage tables. The current live auditor independently rejects such evidence: this is an analysis-layer defect, not a demonstrated bypass of the executing transport or existing audit gate.

Two reporting qualifications should accompany the repairs. `distinct_witnesses` currently counts invalid returned coefficient vectors too (including l170's correctly rejected proposal); distinguish proposal diversity from verified-witness diversity. Also, §4 calls all 24 live controls rejected, although one is the accepted baseline and only 23 are mutations, as the status paragraph correctly states.

Evidence and scope:

- Fresh public rehearsal audit: 665 accepted cases. Fresh copied live-fixture audit: 549 accepted cases before mutations. Both invoke cached builds, with no native episode or proof replay.
- Fresh deterministic controls: 8/8; fresh analysis controls: 12/12. The recorded cohort controls' 44-name set, analysis/deterministic sets, and recorded 101/24 auditor-control sets match their source declarations. The full 44-control cohort suite and full historical 101/24 mutation suite were not re-executed in this review.
- Current cohort, deterministic and analysis source locks all recompute. Across 16 cohort, 30 deterministic and 11 fixture episodes: 1,786 event hashes and 8,818 sealed entries recompute with no mismatches.
- These are artifact-consistency and adversarial-acceptance checks. They do not independently attest the historical native computations or provider behavior.

Reproduction (use fresh output paths):

```sh
python3 -B experiments/r6/reviews/2026-09-23/r6_014_review_probes.py quick --output /tmp/r6-014-review-quick-new.json
python3 -B experiments/r6/reviews/2026-09-23/r6_014_review_probes.py deterministic --output /tmp/r6-014-review-deterministic-new.json
python3 -B experiments/r6/reviews/2026-09-23/r6_014_review_probes.py live --output /tmp/r6-014-review-live-new.json
python3 -B experiments/r6/reviews/2026-09-23/r6_014_review_recount.py --output /tmp/r6-014-review-recount-new.json
```

The signing probes evaluate the historical capture at its admitted historical time, explicitly, as the canned controls do. They never activate production authority. Results are retained beside this review as `R6-014-REVIEW-PROBES-{QUICK,DETERMINISTIC,LIVE}.json`, `R6-014-REVIEW-RECOUNT.json`, `R6-014-REVIEW-BASELINE-AUDIT.json`, and `R6-014-REVIEW-ANALYSIS-CONTROLS.json`.

Signing/ledger and analysis repairs touch locked sources and therefore require new versions and appropriate canned verification. Auditor repairs should remain non-locked until review is complete. Preserve this checkpoint and its records; do not sign or freeze the live evaluator over the present gaps.
