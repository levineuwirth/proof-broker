# R6-001 checkpoint approval and reporting closeout

The author approved R6-001 after independent artifact recomputation on
2026-09-08. The approved object is
[`proposal-checkpoint-v2`](../../runs/proposal-checkpoint-v2/checkpoint.json),
using policy `fixture_farkas_v1`. The claim is interface readiness with no live
model calls, not model capability or additional benchmark breadth.

The review confirmed all three exact-name suites (32 / 8 / 24), their hashes,
both consumed and independently replayed fixture proofs, empty axiom deltas,
four historical golden audits, and all 4,905 prior committed artifacts. The
preservation population consists of 2,871 C1 and 2,034 R6 files. The reported
retention counts and P6's upper-bound/counterexample arithmetic also matched the
reviewer's recomputation. These statements summarize the author's review;
they do not claim another execution of the native episodes.

## Reporting qualifications

There are six native negative cases across **five** failure categories. The two
invalid-witness cases intentionally exercise the same mathematical boundary:

| Case | Logical phase for comparison | Recorded `failure_stage` | Recorded `failure_category` |
|---|---|---|---|
| `d1_malformed` | proposal | `proposal` | `proposal_decode` |
| `d1_wrong_binding` | proposal | `proposal` | `proposal_binding` |
| `d1_timeout` | proposal | `proposal-1` | `resource_exhaustion` |
| `d1_exhausted_budget` | proposal | `proposal` | `request_budget_exhaustion` |
| `d1_invalid_witness` | certificate verification | `certificate-check` | `certificate_verification` |
| `c8_invalid_witness` | certificate verification | `certificate-check` | `certificate_verification` |

The logical-phase column is an interpretation of the recorded detectors, not a
new field retroactively inserted into the episode artifacts. Timeout retains
the native stage name. A later schema should record both phase and detector.

The fixture command has **five** read-only mounts: libc, its loader, the
arithmetic request, the selected witness, and the fixture executable. Counting
only four omits the executable mount. The command clears the inherited
environment and sets two explicit variables. `/out` is the sole host-backed
writable output directory; temporary, process and device mounts also exist.
The source/context files are absent from this sandbox's inputs. This is
enforced process isolation under the trusted OS/harness boundary, not a
computation attestation or a proof that a future networked provider transport
has the same access restrictions.

## Accepted follow-ups

1. Before task expansion, distinguish a legitimate original type containing a
   barred auxiliary constant from an actual payload-integrity violation. Both
   must stop before a request; neither should silently remove a fact. The
   conservative v1 filter and its historical evidence remain frozen.
2. Preserve raw detector-stage labels; use an explicit logical phase for
   cross-case summaries and add that field to the next policy's schema.
3. Include the row semantics in the actual model-visible prompt. Freeze its
   exact bytes, hash them into the request binding, and retain the complete
   outbound envelope. A policy hash cannot teach the model those semantics.

These are concrete requirements in
[LIVE-POLICY-REQUIREMENTS.md](../../LIVE-POLICY-REQUIREMENTS.md). They are not
reported as already implemented in the approved fixture policy.

This closeout changes documentation only after approval; it does not change
the 21 locked harness sources, policy/schema bytes, frozen tasks, or retained
episodes. The R6-001 implementation and evidence form one local checkpoint
commit, following the separate C1 amendment and R6-000 commits. No push or live
request is part of this closeout.

[Commit preflight](R6-001-COMMIT-PREFLIGHT.json) rechecked the two fixture audits,
four historical audits, the source lock and the exact recorded final-check
result without rewriting artifacts or rerunning native stages. All 270 sealed
episode files match their staged bytes. The staged whitespace check reports 40
empty context lines in retained unified patches; each is exactly one ASCII
space required by the patch format. All non-patch files pass. Those hashed
patch bytes are preserved, and no ignored development run or compilation product
is staged.
