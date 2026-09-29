# R6-002 checkpoint approval and closeout

The author approved R6-002 after independent artifact recomputation on
2026-09-08. The approved object is
[`envelope-checkpoint-v1`](../../runs/envelope-checkpoint-v1/checkpoint.json),
using `canned_envelope_v1`. It establishes the local canned interface; there
is no provider SDK, live model or inference-attestation claim.

The review confirmed 84 checks (36 / 13 / 35), exact case sets and hashes,
5,698 preserved files pinned to `79a4a07`, six historical audits, the three
positive episodes' 47 events and 157 sealed files each, empty axiom deltas,
and the reported prompt, request and proof hashes. The alternate serialization
changes wire bytes while preserving D1's decoded messages, request and proof.
The 1,484-file retention population excludes `final-checks.json`, as reported.
These statements summarize the author's recomputation, not another native run.

## Three predicates, with distinct recorded evidence

`transport-validation.json` records response/request association, outbound
message consistency, and `response_validated`. The last field means successful
decoding, schema/size checks, known unique support, coefficient grammar and
binding; **it does not establish mathematical witness validity**. That result
lives in `certificate-verdict.json` and, for accepted episodes, in the final
verdict's `certificate_validation`. It is produced by a separate process.

The controls separate the predicates; they do not cover their full Cartesian
product. Certificate verification is not reached when transport validation
fails, so its result is unobserved in those cases, not false:

| Control | Association | Message consistency | Independent certificate verification |
| --- | --- | --- | --- |
| Three positive episodes | Pass | Pass | Pass |
| Altered/omitted prompt or altered body | Pass | Fail | Not reached |
| Wrong echoed digest | Fail | Pass | Not reached |
| Two well-formed wrong witnesses | Pass | Pass | Fail |

Both wrong witnesses receive `farkas_not_contradictory`, with different residuals:
D1 retains `-5*Zmax + 55340232208193355782`; C8 retains
`-786431*_pb_atom_0 + 55340227810197241860`. Neither failure can be inferred
from the response's grammar or correct echoed digest alone.

## Accepted follow-ups and scope decisions

1. **Relations before expansion.** The 13 recorded request instances contain
   193 `le`, 24 `eq` and zero `lt` rows. These totals include repeated tasks.
   More strongly, the pinned LIA compiler tightens strict integer bounds into
   `Le`; the independent arithmetic projection does the same. A genuine `Lt`
   control cannot be created by changing a row label in the present policy.
   The next live policy will explicitly admit only emitted `le`/`eq` relations
   and use a newly frozen prompt restricted to those relations. Genuine `lt`
   instructions or inputs require a separately admitted fragment, real compiled
   strict-row controls, and a certificate-consumption/replay path first.
2. **Component diagnostics.** Keep `outbound_envelope_binding` as the category,
   but require the new policy to distinguish message layout, system message,
   user prefix and exact request suffix in structured evidence and error text.
   Preserve the approved generic v1 error strings. The next auditor must
   reconstruct the diagnostics from the retained bytes, including missing
   components, rather than trust a reported component name.
3. **One shared frozen proof checker for future compatible policies.** Reuse
   [`envelope_proof_audit.audit`](../../envelope_proof_audit.py), already extracted
   from the frozen R6-001 block. Pin it and its dependencies in the next policy;
   do not introduce a third copy or redirect historical auditors. Its contract
   is the existing Nat/Farkas consumption path, not arbitrary new theories.

Concrete acceptance controls and the limits of existing SDK strict-row tests
are recorded in [LIVE-POLICY-REQUIREMENTS](../../LIVE-POLICY-REQUIREMENTS.md).
These are next-policy requirements, not changes claimed in the approved code.

## Closeout scope

Approval closeout changes documentation and records a local checkpoint commit.
It leaves all ten new locked sources/schema/prompt files, both new policy/lock
files, the R6-001 dependencies, frozen tasks and all recorded episodes unchanged.
The implementation and evidence reviewed above remain one checkpoint. No push,
provider selection, live budget or native re-execution is part of closeout.

The [commit preflight](R6-002-COMMIT-PREFLIGHT.json) records fresh read-only
artifact audits, preservation/source-lock checks, stage-to-index comparisons
for all 471 sealed files across the three positives, retention, and the staged
whitespace diagnostics. The 61 expected diagnostics are single ASCII spaces
on retained unified-diff context lines; those evidence bytes are preserved.
