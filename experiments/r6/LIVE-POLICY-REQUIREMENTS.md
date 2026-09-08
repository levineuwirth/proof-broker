# Requirements for the first live Farkas proposer

Status: requirements recorded following approval of R6-001 on 2026-09-08.
These are acceptance requirements for a new policy, not features already
implemented in `fixture_farkas_v1`. No provider or model is selected here.

The approved [fixture checkpoint](R6-001.md) establishes the request/response,
certificate, consumption and replay boundaries. The first live policy should
keep the strict arithmetic-row interface and the downstream Farkas acceptance
conditions. It needs its own source lock and policy version. Preserve the
approved fixture sources, schemas, admission record and receipts.

## Model-visible semantics and exact prompt binding

A policy hash is an identity check, not instructions a model can read. The
frozen prompt must explain the arithmetic in words:

- Each row denotes `constant + Σ coefficient × variable ≤ 0`, `< 0`, or `= 0`,
  according to `relation`. Variables are the emitted arithmetic symbols.
- The integer compiler has already tightened strict bounds by adding one where
  appropriate. The model must use the emitted rows, without tightening again.
- `neg_goal` is the negated target, included among the inputs to contradict.
- Witness entries reference row names. Explain the coefficient grammar and
  sign restrictions, support limits, and the exact contradiction condition of
  the pinned verifier. State the required JSON response shape and prohibit
  extra proof text. Any prompt example must be checked against that verifier.

Freeze the exact UTF-8 instruction bytes, including whitespace and newlines,
as an artifact such as `prompt.txt`. Add its SHA-256 to the new request's
binding alongside the policy identity. Construct the canonical task request
and hash its exact bytes. Send the actual prompt text and request to the model;
give the model the resulting request digest explicitly to echo in its response.
A hash alone never substitutes for the text. Compute the request digest before
placing it in the outer transport envelope, avoiding a self-referential hash.

The echoed digest establishes response/request binding only. The harness
recomputes the expected digest from the retained request bytes and compares it
with the response field. Equality does not establish that the proposer read,
parsed, understood or used those bytes, nor that a remote model received or
executed the claimed input. Hash computation belongs to the harness; the model
is asked to echo an explicitly supplied identifier.

This is already the meaning of the R6-001 fixture check:
[`RequestSession.invoke`](proposal_episode.py) computes the digest and passes
it as an argument. [`fixture_responder.c`](validate/fixture_responder.c) opens
`/request.json`, counts bytes, and returns 4 if the count is zero. That guard
checks only that the file opens and yields at least one byte. It never parses
the request JSON or uses the arithmetic rows. It echoes `argv[2]` without
hashing the file, so a correct echo is compatible with the rows being entirely
ignored. These are properties of the inspected fixture program under the
recorded execution assumptions, not facts proved by the echo. The
`wrong_binding` case injects `'0'*64` from the harness; it does not perturb a
digest computed by the fixture.

Use `transport_binding_failure` for an echo mismatch in the new policy, with
an error such as "Response request digest does not match the recorded request
bytes." Report the checked association, never `model_input_verified`,
`request_consumed`, or an inference-attestation claim derived from this field.
This category names the failed boundary; it does not assign the cause to the
provider, model or harness. Keep the historical fixture's `proposal_binding`
label and sealed records unchanged.

Retain the complete model-visible messages and the actual serialized provider
request envelope, with hashes. Bind request-start and response receipts to
these bytes. If a client library transforms the envelope, capture what is sent
at that boundary rather than recording only its input arguments. Keep credential
headers outside the model-visible artifact; no credentials belong in the log.

Checking the captured outbound envelope is a separate obligation from checking
the echo. A correct echoed digest can coexist with an altered or omitted
request body. The envelope audit must catch that discrepancy independently.
Even a faithful local transport record does not attest what the remote model
received, attended to or computed.

Required controls before a live call:

1. A canned responder passes through the exact live-policy prompt/envelope path
   and produces a verified, consumed witness for each existing control.
2. Altering instruction bytes, omitting the semantic instructions, or pairing a
   correct prompt hash with different emitted messages fails binding/audit.
3. The model-visible envelope contains the actual semantic instructions and
   request digest; the arithmetic row identity is preserved byte-for-byte.
4. Malformed, wrongly bound, and well-formed invalid witnesses retain their
   distinct rejection boundaries. Request exhaustion and transport failure
   cannot be counted as a negative arithmetic-verification result.
5. An echo-only canned responder that ignores the arithmetic body can pass the
   digest comparison. Give it a well-formed invalid witness and require failure
   at certificate verification, demonstrating that binding establishes neither
   request use nor mathematical correctness. Its digest comparison must produce
   no input-consumption or inference-verification claim.
6. Mutate the outbound body while preserving a correct echoed request digest:
   the echo comparison alone passes, but the independent envelope audit rejects
   the mismatch. An incorrect echo with an otherwise valid witness instead
   fails at transport binding, before certificate acceptance.

## Admission review versus payload-integrity failure

Fixture v1's `_proof_` filter remains conservative and frozen. A legitimate
original type may mention an auxiliary such as `Foo._proof_1`; do not call that
observation a demonstrated sanitizer leak.

Before adding tasks, the new policy must distinguish:

| Condition | Required interpretation |
|---|---|
| An unchanged original target or retained hypothesis type contains an auxiliary constant barred by the context policy | Task/context admission requires review; record the source field and hash |
| Emitted fields contain a proof body, declaration placeholder, unexpected field, or content differing from the permitted source projection | Payload-integrity failure |

Both fail closed before a request. Do not remove a hypothesis, erase a constant
from its type, or broaden the allowlist to suppress the failure. The first
control must contain an auxiliary in an otherwise legitimate original type;
the second must contain an actual injected body or placeholder. Verify distinct
error categories and zero requests in both cases. The sanitized Lean projection
remains evaluator-only unless a separately named information policy admits it.

Keep P6's frozen diagnostic rule: recorded dropped proposition, independently
established original truth, and a checked satisfying assignment for the weakened
IR with negated goal. Unknown evidence remains unresolved. Admission must not
depend on whether the deterministic solver or live proposer succeeds.

## Failure attribution and resource accounting

Preserve the detector's `failure_stage` and add a separate logical
`failure_phase` in the new policy's schema. For example, `proposal-1` timeout and
`proposal` decoding/binding/budget failures share phase `proposal`; an invalid
witness belongs to phase `certificate_verification` and stage
`certificate-check`. Never infer phase by trimming strings from arbitrary stage
names; use the policy's explicit stage-to-phase mapping.

Freeze one request, no fallback, and explicit wall/CPU/memory/output,
token and monetary limits for the first live policy. Record provider/model
revision, sampling settings, actual usage, latency, cost and request count.
Disable hidden client retries or count every transmitted attempt against the
frozen budget. Separate provider/transport failure from candidate invalidity.
An unavailable usage field is unknown, not zero.

The fixture's network-isolated process is not a ready-made provider transport.
Use an explicit transport boundary that receives only the admitted request and
prompt, with the credentials and network access it needs. Give it no repository,
human-proof or sanitized-context access. Audit the actual outbound payload and
all retry behavior. Retain the independent certificate verifier and final replay
as separate stages with their existing narrow inputs.

## Next checkpoint

Complete the prompt, envelope binding, admission-error distinction and transport
accounting with canned responses first. Then freeze the concrete live policy,
model/provider revision and spending limits before making the first request.
R6-001's approval establishes fixture interface readiness; it supplies no model
capability result. The model/provider and live-run budgets remain unspecified.

## R6-002 implementation checkpoint — 2026-09-08

[R6-002](R6-002.md) implements the prompt, byte binding, admission-error
distinction and accounting controls using an isolated **local canned receiver**.
Its checkpoint passes 84 checks, including fresh certificate consumption and
independent proof replay on D1 and C8. The received serialized envelope,
response/request association and mathematical witness are checked separately.
The receiver deliberately ignores the arithmetic, so a passing echo is explicitly
compatible with an ignored or altered body.

This discharges the local canned-interface checkpoint above. It does not
discharge provider integration: a selected SDK/HTTP adapter must retain its
actual outbound bytes and pass canned controls at that boundary, including
retry/usage handling, before live requests. Model revision, sampling, token
and monetary limits still require a separately frozen live policy. The old
fixture's sources, schemas, policy and evidence are unchanged.

## R6-002 review decisions for R6-003 — 2026-09-08

The author approved the local checkpoint. These requirements refine the next
implementation; they do not modify the frozen `canned_envelope_v1` policy,
prompt, diagnostics or artifacts. See the
[approval and reporting closeout](reviews/2026-09-08/R6-002-REVIEW.md).

### Scope the next prompt to reachable relations

The review found zero `lt` rows across the 13 request instances (193 `le`,
24 `eq`, with task repetition). This is structural for the present admitted
pipeline, not just an unrepresentative sample:
[`Farkas.compile_hypothesis`](../../sdk/lib/farkas.ml) emits `Lt(a-b)` in LRA
but `Le(a-b+1)` in LIA, and
[`payload.arithmetic_rows`](payload.py) independently tightens the integer
forms. `payload.request` requires LIA and agreement with that projection.
Relabeling a saved row, lying about the fragment, or applying the integer `+1`
step to Real inputs would test a changed problem rather than this pipeline.

For the first provider policy, retain the two frozen controls and **explicitly
admit only emitted `le` and `eq` relations**. Freeze a new prompt and request
schema around that scope; omit instructions for unreachable `lt` rows. This
supersedes the earlier general `lt` prompt requirement for that first policy
only. Preserve the R6-002 prompt bytes. Require controls demonstrating that:

- A strict integer source bound produces the expected `+1` and `le` row exactly
  once; its certificate is consumed and its original target independently replayed.
- An injected `lt` row and an unsupported/effectively non-LIA problem fail
  admission before a request, even if a metadata label claims LIA.
- Request, prompt and actual outbound messages agree on the relation scope;
  the live model is not given semantics for rows it cannot be asked to use.

Before task expansion, explicitly review the admitted fragment/relation set.
Before admitting any genuine `lt` row **or restoring `lt` instructions in a live
prompt**, require an end-to-end control whose effective fragment actually
compiles a strict row. Retain the ordinary request/envelope, independent
certificate verification, certificate-consuming proof and isolated replay
checks under a separately frozen compatible policy. SDK verification alone
does not establish compatibility with the existing `term_mode_nat` consumer.

For that strict-row extension, the minimum mathematical contrast is a weighted
sum with all variables canceled and constant zero: accepted when a strict row
has a positive multiplier, rejected when no strict row has positive weight.
Also cover a negative multiplier on a strict row and a Real counterexample
that an erroneous integer `+1` transformation would make contradictory. Assert
at least one actual `lt` row before counting the strict control; do not let
the test pass on an already-tightened `le` surrogate. The criterion is constant
`>= 0` with positive strict weight, and `> 0` otherwise.

Existing SDK tests provide starting points:
[`test_farkas.ml`](../../sdk/test/test_farkas.ml) contains
`test_compile_lt_lra`, `test_verify_lra_strict_residual_zero`,
`test_verify_lra_strict_loose_mix`,
`test_verify_real_typed_ir_mislabeled_lia_rejects_plus_one_trick`, and
`test_verify_lra_strict_negative_coef_rejected`;
[`test_farkas_search.ml`](../../sdk/test/test_farkas_search.ml) contains
`test_exact_lra_strict_zero_residual`. Their source was inspected during
closeout, not rerun. They exercise SDK behavior, not the R6 prompt/envelope/
consumption/replay chain, and do not discharge the new admission gate.

### Diagnose the diverging envelope component

Retain category `outbound_envelope_binding` and phase `proposal`. The new policy
must include a machine-readable mismatch list and a specific human explanation
for the failing component: envelope decode/shape, message layout/role,
system-message content, user prefix (including digest/header/separator), or
exact request suffix. Record presence, expected/observed byte length and digest
where applicable; use null for a missing component, not a fabricated empty
string. These identify an observed discrepancy, not its causal author.

Define deterministic handling of multiple discrepancies and unparseable or
oversized envelopes. Do not discard component evidence when wrapping an
exception or writing `transport-validation.json` and `failure.json`.
Independently reconstruct each diagnostic in the artifact auditor from the
retained captured bytes and frozen expected messages. A reported component
label is evidence to check, not authority for the diagnosis.

Controls must separately alter/remove the system message, alter the user prefix,
and alter only the request suffix while keeping a correct response echo. Add a
resealed mutation that falsely labels one component failure as another. Each
must preserve the common category and identify the actual differing component;
the valid standard/alternate serialization controls must remain accepted.
The approved v1 generic error strings remain unchanged.

### Reuse the already extracted proof-check module

Decision: the next compatible policy calls
[`envelope_proof_audit.audit`](envelope_proof_audit.py) as the shared frozen
Nat/Farkas proof-path checker. Its approved SHA-256 is
`ccd9b82881167affc17a6104c713c574207e1181d2093bb46d2c73600eeb3644`.
It is already extracted and accepts task, packet, verdict, observations and
artifact/receipt readers. A third copy or a rename-copy adds no useful boundary.

Pin the module and its transitive implementation/protocol dependencies in the
new policy's source/provenance contract; retain those bytes in its artifact.
Verify before launch and during retained-artifact audit. Keep provider-specific
receipt order, transport, accounting and attribution in the calling auditor.
Do not rewrite R6-001's inline checks or redirect either historical auditor.
Its equality regression with the R6-001 block remains a historical guard.

The next checkpoint must demonstrate that production audit actually calls this
module, accepts the existing positive proof paths, and rejects substituted
certificate/proof/type/axiom evidence through it. A new theory, certificate
consumer or replay predicate needs a new version with its own conformance
controls; do not relax the Nat checker to make new inputs fit.

Finally, keep `response_validated` separate from certificate acceptance in
reports. The former checks decoding, shape, support, coefficient grammar and
binding. Mathematical validity is in `certificate-verdict.json`. When a prior
stage rejects, later verification is not reached, not a failed mathematical
test. R6-002's controls separate these predicates; they are not all combinations
of three Boolean outcomes.
