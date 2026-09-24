# R6-014 amendment 1 — the policy-directory check, amended after collection

Status: prepared for review, 2026-09-24. This is a **post-collection amendment** to one layout check. It is not an unchanged
preregistered evaluation. Its decision is [R6-014-AMENDMENT-1-DECISION.md](reviews/2026-09-24/R6-014-AMENDMENT-1-DECISION.md).

Analysis stays deferred. No further transmission or spending is authorized. The eleven consumed slots stay consumed whatever the audit
eventually concludes.

## When and why

| time (+0200) | commit | event |
|---|---|---|
| 2026-09-24 10:34 | `ffab7cf4` | live-evaluation-v1 lock over the approved auditors (`996ada00…`) |
| 10:56 | `c00247ed` | cohort v9 block 1 signed into the shared production `policies/` |
| — | `6a361a3e` | block 1 collected: 11 returned sends; operator scan clean, all 11 runs bound |
| 11:12 | `6a361a3e` | frozen live audit **rejected** at `revision:history_bound` |

The frozen check required the policy directory to hold *only* the campaign's files. Every reviewed fixture had a directory to itself.
Production signs into the shared `policies/`, beside every earlier policy and lock. No review or control exercised a shared directory.

The rejection was on layout, before any per-run case, and no analysis input was emitted.

Retained byte-for-byte:
- the lock (`policies/live-evaluation-v1.sha256.json`);
- the frozen auditor (`reviews/2026-09-23/cohort_v9_audit.py`);
- the collection (`cohort-live-v9/`, the live ledger, floor and slots);
- both operator scan reports;
- the rejection ([R6-014-BLOCK1-LIVE-AUDIT-REJECTED.json](reviews/2026-09-24/R6-014-BLOCK1-LIVE-AUDIT-REJECTED.json)).

## The amendment

The amended auditor is [`cohort_v9_audit_amended.py`](reviews/2026-09-24/cohort_v9_audit_amended.py). It is the frozen auditor with one
predicate changed, and its docstring states when and why. The diff is that predicate and its helper, `campaign_files`:

- **Expected, campaign-owned files.** They are derived explicitly:
  - the policy;
  - its checkpoint, activation receipt and progress floor;
  - its retained revisions `<stem>.r<k>.json`, for k < n;
  - the source lock `cohort-harness-v9.sha256.json`, whose name does not share the policy's prefix.
- **Campaign-specific names present.** These are:
  - the policy's own name, or any name beginning with its stem and a dot;
  - the lock's own name, or any name beginning with its stem and a dot.
- **The rule.** The campaign-specific names present must equal the expected set exactly: all present, nothing unexpected. Unrelated
  policies are ignored.

Every other predicate is the frozen auditor's, unchanged: content, revision chain, authorization, pricing, ledger and evidence.

## Controls (synthetic evidence only)

The record is [R6-014-AMENDMENT-1-CONTROLS.json](reviews/2026-09-24/R6-014-AMENDMENT-1-CONTROLS.json). The collected block 1 is not read.

- **Production directory layout.** A shared directory holds every unrelated file of the production `policies/` (never the production
  campaign's own files) beside the synthetic fixture campaign's files:
  - it is **accepted**, with the same 550 cases;
  - an unrelated look-alike name (`<stem>0.json`) is **accepted**;
  - each of these is **rejected** at `revision:history_bound`: a missing floor, a missing checkpoint, an unexpected campaign revision,
    an unexpected policy-prefixed file, an unexpected lock-prefixed file, and an altered retained revision;
  - an altered activation receipt is rejected at `ledger:continuous_across_revisions`.
- **Isolated fixture.** Its case population is unchanged: the amended auditor evaluates exactly the 550 cases, all true, of the frozen
  record `R6-014-V4-LIVE-FIXTURE-AUDIT.json`.
- **Frozen live controls.** All 51 records (baseline, 48 mutations, 2 acceptance probes) have the same outcomes, including zero sentinel
  reads for the escapes.

**Not re-executed:** the rehearsal-mode audit and its 101 controls. They presuppose the pre-signing production tree: a disabled policy,
a rehearsal-only ledger directory and a single-revision rehearsal ledger. Signing changed all three by design, and this is true of the
frozen auditor too. The amended predicate is reached only in live mode, since `revision_history` returns before it in rehearsal mode.
The rehearsal path is therefore byte-identical to the frozen, recorded one.

## After review

1. Freeze **live-evaluation-v2** over the amended auditor and its controls. v1 is retained.
2. `verify` it.
3. Audit the unchanged collection with the amended auditor.
4. If another production-only mismatch appears, retain that rejection and review it separately. Exceptions are not accumulated until the
   collection passes.
5. Only after an accepted audit, run the frozen analysis.
