# R6-003 checkpoint approval and closeout

The author approved R6-003 after independent artifact recomputation on
2026-09-09. The approved object is
[`provider-checkpoint-v1`](../../runs/provider-checkpoint-v1/checkpoint.json),
using `openai_responses_http_fixture_v1`. Its scope is local serialization,
HTTP transmission and response handling, followed by certificate consumption
and independent proof validation. Remote receipt, TLS, credential handling
and inference attestation remain outside that claim.

The review confirmed all 108 checks (47 / 23 / 38), suite hashes and exact case
sets, 7,195 preserved files pinned to `13baa73`, 450 event hashes and 2,757
sealed entries across 23 episodes. Each positive has 45 events and 172 sealed
files, empty axiom deltas, and the reported request/proof hashes. D1 checks
3702/3721 declarations; C8 checks 1470/1471 with its previously qualified
statement-identical wrapper scope. Nine historical audits pass. Retention
excluding `final-checks.json` is 2,808 files, 25,163,529 apparent bytes, 673
distinct contents and 6,468,592 unique-content bytes. Repeated requests contain
363 `le`, 44 `eq` and zero `lt` rows. All episodes reserve one attempt;
22 record one body send and capture, while the failed connection records zero.
This paragraph records the author's recomputation, not another native run.

## Tightening: decisive for this witness, not a model diagnostic

D1 uses weights 8, 4 and 4 on `hZ`, `neg_goal` and `hnum`. Its variable
coefficient is `8 - 8 = 0`. The constant is exactly `4`; removing the one
integer-tightening increment from `neg_goal` subtracts its weight, giving `0`.
A zero constant is not a contradiction under this admitted `le`/`eq` rule.
The `hx` row has weight zero and remains a separate projection check.

One review inference needs narrowing: this does not establish that a model
which internally tightens again must fail. With the same weights, an extra
increment would give an internally computed constant of `8`; the returned
weights still verify against the authentic rows with constant `4`. Altering
the emitted rows would instead confront the independent projection/envelope
checks. Those checks concern observable problem bytes, not a model's private
calculation. No model ran here. The closeout records the `0 / 4 / 8` arithmetic
as a derived explanation, not a new native control or capability result.

## Credential finding: accepted as a required pre-live control

The report's Authorization-omission statement is a description of the
implementation and inspected records, not a tested invariant. The native
server records header presence, never its value. The fixed fixture marker
occurs in retained actor source. `no_external_endpoint` checks the CLI/config
surface; it supplies no credential-disclosure control over logs or retained
artifacts. The approved 108 checks must not be described as providing one.

The next canned checkpoint must inject a distinctive synthetic Authorization
value through the intended credential input path, demonstrate at the receiving
endpoint that the exact value arrived, and enforce its absence from publishable
records. This must precede the live policy and any real credential input. The
[requirements](../../LIVE-POLICY-REQUIREMENTS.md#r6-003-approved-pre-live-credential-control--2026-09-09)
now specify reproducible canary construction, exact-receipt preconditions,
complete publication-file inventory, compressed-artifact inspection, successful
and failed request paths, and deliberate leak mutations that the scanner must
reject. Source exceptions must be exact and justified; a dynamically derived
canary can normally avoid them altogether.

This is a required future control, not a patch to the frozen HTTP actor or a
claim that the test was executed during closeout. The existing prompt, request,
certificate and independent declaration requirements remain the acceptance
boundary for the next compatible adapter version.

## Closeout scope

Approval closeout updates documentation and records the approved implementation
and evidence in a local checkpoint commit. The nine locked R6-003 source/schema/
prompt files, three policy/source/runtime lock files, earlier dependencies,
frozen tasks and every recorded episode remain unchanged. No native episode,
TLS session, live call or credential experiment is part of this closeout.

The [commit preflight](R6-003-COMMIT-PREFLIGHT.json) checks source locks,
preservation, suite hashes/counts, retained-only audits, staged bytes and
publication selection. The staged whitespace diagnostics include the retained
single-space unified-diff context lines and the deliberately oversized all-space
provider body. These bytes remain evidence; they are catalogued rather than
silently changed or suppressed.
