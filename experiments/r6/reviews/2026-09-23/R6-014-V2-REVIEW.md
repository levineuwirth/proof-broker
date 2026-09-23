# R6-014 revision 2 review

Reviewed at e11e6251. Not approved for signing yet. The direct repairs are present and the reported baselines reproduce, but six remaining gaps are demonstrated below. These are isolated synthetic-authority tests and mutations of temporary artifact copies. No production policy, authority, locked source or retained run was edited; no real credential was read and no provider connection was made.

1. **P1 — The activation receipt pins identity, not consumption progress.**

   `cohort_ledger.py:224–240,301–319`; `cohort_contract.py:227–231`.

   The original missing-directory test now correctly rejects at `cohort_activation_authority_lost`. The adjacent rollback case still resets consumption:

   - Freeze and sign a temporary policy with the production functions; save the live directory immediately after activation.
   - Reserve D1/1, commit a synthetic grant and reconcile it as consumed. A second reservation correctly refuses `cohort_slot_consumed`.
   - Preserve the spent directory elsewhere and restore the activation-only snapshot to its path. Leave the activation receipt beside the policy byte-for-byte unchanged.
   - `live_permitted` accepts; it reports zero consumed transmissions; D1/1 reserves again.

   This does not remove both records, forge a hash chain, or create a new activation identity. The receipt survives and authenticates the same old first row, while all consumption progress has rolled back. It is a storage-restoration case, not a demonstrated model or hostile-host exploit.

   To meet the stated no-reset/rollback requirement, authority outside the replaceable ledger directory must bind a durable progress floor, with conservative recovery when the two records disagree. Add this same-activation snapshot control alongside the now-passing missing-directory control. The report's stated limitation (both receipt and ledger lost) is presently too narrow.

2. **P1 — Gzip scan coverage is inferred from the filename rather than the bytes.**

   `cohort_v8_audit.py:1972–1984`; compare `publication.py:124–137`.

   The three original entry mutations now reject at `operator_scan:report_bound`, as intended. The frozen scanner recognizes gzip by its `1f 8b` magic; the new auditor requires a gzip stream only for paths ending in `.gz`.

   In a temporary fixture root I added `compressed-disclosure.bin`, containing a gzip-compressed header for that fixture's synthetic operator credential. The production scanner found **two gzip-stream disclosures and zero raw-stream disclosures**. I then retained its authentic path, size and digest in the operator inventory but reported only a clean raw stream, updating the file count. All **550 live-audit cases passed**. The file is inside the declared publication root, outside the episode directories; no episode or receipt was changed.

   Derive required stream coverage from the bytes the inventory identifies, using the frozen scanner's rule, and reconcile the aggregate stream counts as well. No real credential is required for this check. Keep a `.bin` compressed control whose positive precondition demonstrates the actual scanner's gzip findings; a `.gz`-only control cannot establish this property.

3. **P2 — Deterministic certificate evidence is still incompletely bound, particularly on refused paths.**

   `deterministic_audit.py:217–242`.

   Three independent coherently re-chained/re-sealed mutations pass all **478 cases**:

   - On refused l166, replace every top-level certificate-bearing child observation's coefficients with `0·neg_goal`. The independent checker, run separately on the reconstructed packet, rejects it as `farkas_not_contradictory` (weighted sum zero); the auditor still accepts it as reconstruction-refused after verification.
   - On the same refused site, change the selected closer to `term_mode_int` and carry that label into the outcome/summary. The auditor accepts it despite the pinned dispatch selecting the Nat path.
   - On successful l070, change only the certificate in `certificate_verification_finished` to the zero witness. The independently checked packet and other receipts remain authentic, but the inconsistent verification observation is ignored.

   Rebuild and check the packet wherever certificate verification is claimed, including refused runs, and bind every certificate-bearing observation to it with the expected stage/component/order. Derive closer selection from the pinned dispatch rules. Successful consumption receipts and refused-run evidence need the same cross-record bindings; accepting failure integrity must not implicitly trust the claimed intermediate successes.

4. **P2 — The retained solution is not joined to the export used by the replays.**

   `deterministic_audit.py:243–247`.

   `sha(decompressed solution) == verdict.solution_sha256` verifies two mutually editable fields. I substituted l069's proof export for l070's `solution.ndjson.gz`, changed that digest, and coherently rebound outcome, summary, terminal and seal. All **478 cases passed** while the export stdout record and raw kernel reports still described the original l070 replay input. A smaller added-newline control also passed.

   Join the retained decompressed solution to the export stdout digest already recorded in the seal (and its bytes when present), alongside the existing command/path and replay-report bindings. Do not infer a historical replay of replacement bytes merely from agreement with a replacement verdict digest. Where only an ephemeral digest survives, retain that qualification explicitly.

5. **P2 — Search-stage workload cleanup is exempted from the deterministic audit.**

   `deterministic_audit.py:208–217`.

   Changing l070's search process record to `workload_empty_after_cleanup: false`, updating its supervisor receipt and resealing still passes all **478 cases**. The auditor computes `clean` including workload emptiness, exempts `search` from that predicate, then computes `failed` without the workload field. The positive proof classification therefore survives an explicitly nonempty workload.

   Separate expected nonzero exits on mathematical refusal from mandatory termination/monitor/resource observations. Require workload cleanup on successful search and derive any failure classification conservatively. The companion exit-code-7 mutation correctly rejects at `search:outcome_recomputed`; it does not test the omitted cleanup field.

6. **P2 — Frozen family and exposure strata can still be redefined by the analysis input.**

   `analysis_r6.py:99–104` and the family/sensitivity table construction.

   Exact primary/posed membership is now enforced. But changing only l069's supplied family from `Bracket.lift_cell` to `Review.synthetic_family` is accepted: the analysis gains a fifth family, and the first block's `excluding_lift_cell` table grows from **7 to 8 collected slots**, with `continue_permitted: true`. The headline 15/11/10/1/6/4 map remains unchanged.

   The declaration is the independence unit, and this family determines a predeclared exposure sensitivity. Bind the site→declaration map to the reviewed census/classification independently of the caller's record, just as the site memberships are now bound. This is an analysis input-validation gap; it does not establish that the live auditor would accept a forged classification artifact.

The original fixes that were directly re-exercised include missing-ledger refusal, all three contradictory operator-entry refusals, and the 18 analysis controls (unknown/partial usage, rounding, membership drift, raw integrity observations and diversity separation). The live fixture's distinct-capture/later-authorization/pricing-revision baseline now passes 550 cases. The new deterministic population and raw replay/type checks are present; the remaining issues above concern their surrounding evidence joins.

Verification and scope:

- Fresh public audits: **665 rehearsal cases**, **550 live-fixture cases**, **478 deterministic cases**. Fresh analysis controls: **18/18**.
- Source locks recompute: cohort v8 `73ebe32f…`, deterministic `a080efa7…`, analysis v2 `ee28047e…`.
- Recorded suites match their source-declared populations: 46 cohort controls, 18 analysis controls, 26 deterministic-audit controls, 101 rehearsal-audit controls, and 42 live records (baseline + 39 rejected mutations + 2 acceptance probes). I checked these recorded populations and statuses; I did not rerun those entire control suites other than analysis.
- All 57 episode trees were rehashed: 16 cohort runs (559 events / 4,178 sealed entries), 30 deterministic runs (717 / 1,455), and 11 live fixtures (510 / 3,185). Total **1,786 event hashes and 8,818 sealed entries**, zero mismatches.
- The deterministic auditor invokes cached builds, dependency inspection and independent certificate checks; it does not rerun Lean proof episodes or kernel replays. Its first sandboxed attempt was blocked by `ldd` on CVC4; the same audit and targeted probes then ran with approved escalation.
- Production remains disabled with no checkpoint, activation receipt or live ledger. New files are review evidence only and are uncommitted.

One non-blocking audit-contract improvement: `deterministic_audit.Audit` rejects duplicate case names but does not assert a frozen complete expected-name set before returning success. The controls gate their own names; the auditor should also expose and gate its full per-outcome case population before the live-evaluation lock.

Reproduce with fresh output paths:

```sh
python3 -B experiments/r6/reviews/2026-09-23/r6_014_v2_review_probes.py authority --output /tmp/r6-014-v2-authority-new.json
python3 -B experiments/r6/reviews/2026-09-23/r6_014_v2_review_probes.py deterministic --output /tmp/r6-014-v2-det-new.json
python3 -B experiments/r6/reviews/2026-09-23/r6_014_v2_review_probes.py deterministic_extra --output /tmp/r6-014-v2-det-extra-new.json
python3 -B experiments/r6/reviews/2026-09-23/r6_014_v2_review_probes.py live --output /tmp/r6-014-v2-live-new.json
python3 -B experiments/r6/reviews/2026-09-23/r6_014_v2_review_probes.py analysis --output /tmp/r6-014-v2-analysis-new.json
python3 -B experiments/r6/reviews/2026-09-23/r6_014_v2_review_recount.py --output /tmp/r6-014-v2-recount-new.json
```

The authority test uses the retained pricing capture at an explicitly supplied historical admissible time, as the canned signing controls do. Results are in the adjacent `R6-014-V2-REVIEW-*.json` files. Keep the existing checkpoints intact; signing-state and analysis fixes need new locked versions, while the auditor repairs can stay in non-locked review paths.
