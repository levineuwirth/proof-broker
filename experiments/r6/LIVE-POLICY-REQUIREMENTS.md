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
