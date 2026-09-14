# R6-009 independent review — 34eae76

The recorded demonstration holds, but the checkpoint needs repairs before closeout. The main regression is that the new campaign auditor establishes substantially less than the R6-008 auditor it replaces. There are also gaps in admission and in the durability of the new slot hierarchy. All observations below concern the committed implementation; original sources, policies, episodes and campaign ledgers were preserved.

The supplied focused suite passed afresh at **23 cases**, including its nested 17-fault sweep. The public auditor accepted at **53 cases**, and its supplied controls completed at **9 entries**. These results do not discharge the additional probes below.

## What rederives from the original bytes

The [review recount](R6-009-REVIEW-RECOUNT.json) checks actual body files, not just reconstructed arguments:

- Four serialized bodies have digest `e684c1167a4eb9eed768114fcb242d71bf3996c3521cf8216090d961670ba8a5`. Three outbound bodies and three receiver captures have that same digest. The credential-format failure serialized a body but transmitted none; the consumed-slot refusal had no actor stage.
- All **187 event hashes and 1,302 sealed entries** recompute across the five episodes. Four reservation ids, three grant ids and four nonces are distinct.
- The ledger contains **10 rows**, three consumed slots and **307,200 µUSD committed**, with no open reservation. The three retained proof results have empty axiom deltas and the reported 3,702/3,721 declaration counts.
- The frozen source checks pass. The policy remains disabled, with no live ledger. All **39,444 files in the review-start inventory** remain byte-identical; that inventory excludes `.cache` and `__pycache__` and is distinct from the Git-selected population.

These are retained-evidence checks. I did not rerun native Lean episodes, kernel replay, a provider request or a real-credential scan. The new actor probes use a plain subprocess and the local TLS fixture, as the focused suite does; they do not claim a new bubblewrap/native episode.

## Findings

### 1. P1 — a D1 request can consume a C8 slot

At [cohort_budget.py:45](../../cohort_budget.py), reservation receives `task_id` separately from the request. Admission validates the envelope but never compares `request.binding.task_id` with that funded task. At [cohort_https.py:157](../../cohort_https.py), the actor binds the permit to its CLI task/draw and binds the request digest to the permit, without joining those two relationships.

The production host reservation function accepted an authentic D1 request while reserving C8/1 in a temporary rehearsal ledger. The production actor then admitted it, sent that exact D1 body to the local receiver, received HTTP 200, and reconciled to `send_grant` for **C8/1**. An unaltered D1/D1 control also sent successfully. This uses the existing rehearsal authorization, which schedules both tasks; no authorization, price, request hash or ledger chain was forged.

Evidence: `d1_request_funded_as_c8` in [actor probes](R6-009-REVIEW-ACTOR-PROBES.json), implemented by [cohort_review_probes.py](cohort_review_probes.py).

Repair: before reservation, derive the request's task and compare it with the scheduled task; repeat the binding inside the actor before reading the credential. Keep manifest/challenge/IR identity tied to the admitted task, rather than treating a matching request digest as a substitute. Add both directions of the D1/C8 crossing and independent host/actor controls. The recorded five D1 episodes are correctly bound; this finding concerns what the executing boundary will admit.

### 2. P1 — the new auditor loses established episode checks

[cohort_audit.py:89](cohort_audit.py) computes `bodies` from regenerated arguments. It never compares those bodies with `serialized-body.json`, `outbound-body.json` or `received-body.json`. Therefore its headline identical-input check proves equality of reconstructed envelopes, even when the captured transmission bytes disagree.

The problem extends beyond that one comparison. All **14 corrupted artifact copies** in [audit probes](R6-009-REVIEW-AUDIT-PROBES.json) are accepted at 53 cases:

| Relationship perturbed | Separate probes accepted |
| --- | --- |
| Actual transport | Altered serialized body; altered outbound body; altered received body; raw provider response changed to `status: failed` |
| Reconstruction identity | Captured target changed to `False`, with its context receipt updated |
| Results and cost attribution | Summary task changed to C8; summary's nested allowance changed to zero; accounting allowance changed to zero; recovery proposer changed to `live_model_response` |
| Credential evidence | `exact_receipt` changed to false |
| Authority and imported provenance | Recorded authoritative-ledger mount redirected; retained imported `campaign_ledger.py` bytes changed |
| Publication | A new file added after sealing; a scan report marked rejected while terminal acceptance remains true |

Each copy passed the unmutated audit first. Twelve mutations use the production finalizer to rebuild the scan, terminal event and seal. The publication-result mutation updates the terminal's report digest and reseals; the unlisted-file mutation deliberately tests completeness after sealing. These are independent perturbations, not a bundle whose first rejection hides later checks. The remaining, fifteenth probe concerns case-population gating below.

The shared proof checker is still useful, but it is not the complete episode auditor. In particular, it binds the two context hashes to their respective files without comparing the captured context with the frozen context; R6-008 added that equality outside the shared checker. The new auditor has dropped that addition. The same pattern affects summary/accounting, authority mounts, imported-module binding, publication recomputation, process receipts and trace attribution.

Repair: inventory and carry forward the applicable cases and mutations from [campaign_audit.py](../2026-09-13/campaign_audit.py), with explicit adaptations for the contract and campaign revisions. Add the cross-revision checks on top. Do not repair only the fourteen demonstrated holes: use the previous audit's case population as the migration checklist, including disposition derived from supervisor/grant evidence, expected event order, command/resource receipts, and complete finalization. This repair can remain under non-locked review paths.

### 3. P2 — the request schema is pinned but not enforced at admission

[pricing_gate_v3.py:61](../../pricing_gate_v3.py) checks the version, contract digest, canonical encoding and row relations. It does not enforce the frozen request schema's required fields or `additionalProperties: false`. The builder validates that schema, but neither the later host reservation boundary nor the actor independently does so.

Two separate production host/actor probes each sent successfully and consumed a slot:

- Add the current `policy_sha256` to an otherwise authentic request, then render that request consistently. This reintroduces authorization metadata into model-visible bytes.
- Delete `binding.task_id`, keeping the rest of the body and envelope consistent.

Both are forbidden by [cohort-request.schema.json](../../schema/cohort-request.schema.json). Evidence: `request_policy_digest_injected` and `request_task_binding_deleted` in [actor probes](R6-009-REVIEW-ACTOR-PROBES.json).

Repair: enforce the complete, hash-bound request grammar in both executing admissions, including required bindings, allowed keys, row shape, integer-string grammar and nonempty populations. A shared standard-library validator is reasonable if the sandbox intentionally omits `jsonschema`; it needs parity controls against the frozen schema. Keep this separate from finding 1: two valid requests can still be crossed even when both satisfy the schema.

### 4. P2 — Python equality admits different generation-option bytes

The option comparisons in [pricing_gate_v3.py:57](../../pricing_gate_v3.py) and policy comparisons use Python value equality. That accepts JSON values of different types. At production admission, changing `max_output_tokens: 4096` to `4096.0`, or `store: false` to `0`, yields `accepted: true` with entity bytes different from the frozen rendering.

Evidence: [admission type probes](R6-009-REVIEW-ADMISSION-TYPES.json), including the unmodified control. These are shared-admission predicate probes, not additional actor transmissions.

Repair: require exact JSON types and compare the canonical serialized arguments with the canonical contract rendering. Apply the same rule to policy generation settings. Test integer/float and boolean/integer substitutions separately. Equality of Python dictionaries is weaker than the byte/type identity this contract promises.

### 5. P2 — the auditor can succeed with a missing named case

`run_cases()` at [cohort_audit.py:46](cohort_audit.py) is unused. The terminal result is `accepted=all(a.cases.values())` without an exact expected-name assertion. Suppressing one named case produces **accepted: true, case_count: 52**. This probe establishes missing-case acceptance; it does not claim the underlying proof checker was skipped, since the probe suppresses the named `require` call.

The audit-control runner likewise reports a result count without asserting its expected name set. Its grant-ordering control repeats an inequality rather than driving the production auditor through a coherently rebound bad HTTP record.

Evidence: `audit_case_removed` in [audit probes](R6-009-REVIEW-AUDIT-PROBES.json); terminal population logic in [cohort_audit_controls.py](cohort_audit_controls.py).

Repair: derive the full expected set from the frozen episode population and declared outcomes, require exact membership and uniqueness, and fail incomplete output. Add a missing-case control to the public gate. Exercise the real grant-ordering check rather than a copied predicate.

### 6. P2 — new task/draw parent directories are not made durable

[cohort_ledger.py:234](../../cohort_ledger.py) now creates `slots/<task>/<draw>/<reservation>/`. It fsyncs `<draw>` after creating the reservation directory, and grant commitment fsyncs the reservation directory. It does not fsync `slots` after creating `<task>`, or `<task>` after creating `<draw>`.

The [durability probe](R6-009-REVIEW-DURABILITY.json) observes actual `os.fsync` calls through production reserve and grant, forwarding every call to the real implementation. It first proves that the task and draw directories are new. Both parent-directory syncs are absent. The prior flat layout explicitly fsynced `slots`; carrying forward the lifecycle fault sweep does not test this new hierarchy.

Repair: make every newly created path component durable before the reservation can authorize a sender, including correct parent-directory ordering. Add a control for a first task/first draw and for a new draw under an existing task. This is a demonstrated omission in the durability protocol, not a reproduced power-loss event or a claim that these retained grants were lost.

## Reporting correction

The ledger sequence in R6-009.md omits the first `send_grant`. The actual sequence is:

`activation → reservation → send_grant → reservation → release → authorization_revision → reservation → send_grant → reservation → send_grant`.

The three consumed slots and 307,200 µUSD total are correct. Also preserve the serialized/sent distinction: four serializations, three sends, with the same body digest where each exists.

## Recommended checkpoint repair

Repair admission and directory durability in a new locked revision. Restore the full prior episode audit with explicit contract/campaign adaptations under non-locked paths. Run each new negative against its own accepted control, then rerun the native revision demonstration under the new lock, including a real second-task control. Preserve this revision as the reviewed record. The extended-anchor work remains a separate checkpoint; these defects should not become its baseline or be deferred until authorization.

Review-only evidence:

- [Fresh focused suite](R6-009-REVIEW-FOCUSED.json), [fresh public audit](R6-009-REVIEW-BASE-AUDIT.json), [fresh supplied audit controls](R6-009-REVIEW-BASE-CONTROLS.json).
- [Actor and copied-artifact probe source](cohort_review_probes.py), [type probe source](cohort_admission_review.py), [durability probe source](cohort_durability_review.py), [recount source](cohort_review_recount.py).

The first focused invocation was blocked by sandbox socket restrictions and was rerun with local-loopback permission. Two review-helper construction errors were corrected before the completed records were produced: unpacking the ledger's tuple return and supplying a required synthetic request binding for the grant probe. Incomplete scratch outputs were not substituted for completed records. No experiment source, policy, original episode or ledger was changed, and nothing was committed or pushed.
