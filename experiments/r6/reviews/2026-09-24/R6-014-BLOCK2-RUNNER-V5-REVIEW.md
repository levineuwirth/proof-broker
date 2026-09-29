# Block 2 runner revision 5 — review

Reviewed `994bf8bc` on 2026-09-25. **Approved for the reviewed operator-runner scope. No findings.** This review does not activate the authorization or permit additional scope beyond the separately recorded operator approval.

The revision 4 stage-population finding is closed. `receipts_agree` now checks the union of process-record stages and stage-finish receipts. The later comparison against the frozen sequence requires exactly the corresponding stage directories and process records. Missing files cannot remove their own comparison, unmatched receipts cannot escape it, and duplicate process records are detected by the full population comparison.

The ordered `(source, stage, event)` sequence comes from the auditor bound by `live-evaluation-v2`, in live mode. The runner checks that auditor's digest before importing its sequence definitions. This reuses the frozen outcome grammar rather than creating a second definition. The complete sequence comparison also checks missing, extra, duplicated and reordered observations beyond the individually compared records. Receipt contents remain governed by the gate's record comparisons; the frozen final auditor remains the acceptance gate for the collected evidence.

Independent verification:

- Fresh supplied suite: 50 cases × fresh/restart = **100 passing records**, with the exact recorded name set, decisions, outcomes and launch counts. Runner and control-program digests match.
- All **eleven block 1 baselines** continue with no reasons.
- All three previous reviewer-probe wrappers rerun: **14 revision-2, four revision-3 and four revision-4 probe outcomes** stop or pause. The eleven genuine-ledger baselines continue.
- Additional probe: a second process record in the export stage pauses before the next launch, both fresh and on restart. This exercises the duplicate that the per-stage dictionary alone would collapse.
- Additional import control: a mismatched auditor digest is refused before its sequence definitions are loaded.
- `live-evaluation-v2` still verifies **69 files** at `96ce9f6d…`. Production remains revision 1 with eleven authorized slots.

Evidence is retained as `R6-014-BLOCK2-RUNNER-V5-REVIEW-{CHECKS,CONTROLS,V2-PROBES,V3-PROBES,V4-PROBES,EXTRA}.json`. All mutation runs use synthetic copies and mocked sender/ledger boundaries; no actual sender subprocess, real credential read or provider call occurred. No authorization was created. The frozen collection, analysis and evaluation sources were not edited.

Proceed with the fresh admitted pricing capture and the addendum naming it, then the separate authorization step using the previously approved scope. Preserve the eleven consumed draw-1 slots. Collection should use this reviewed runner unchanged, followed by the operator scan and frozen audit/analysis as planned; any pause or integrity stop still requires review.
