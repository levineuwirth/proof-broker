# Second golden control: C1 exact-support recovery

Amended September 8 to distinguish C8's statement-identical wrapper from D1's
embedding in a larger downstream declaration. Recorded episodes are unchanged.

The second deterministic control is complete. C8 now supplies an R6 episode
that exercises the recovery branch introduced by C1, while D1/70 continues to
exercise bounded enumeration. Both pass the same certificate, task-identity,
proof-reference, axiom and kernel checks. No learned policy was connected.

| Observation | D1/70, `golden-broker-v3` | C8, `golden-c8-v1` |
|---|---|---|
| Task class | Original VerInf local obligation | Synthetic control derived from committed C1 C8 |
| Bounded enumeration | Succeeds | Fails: `search_exhausted` |
| Exact-support recovery | Not entered | Succeeds |
| Synthesized witness | `2·hZ + 1·neg_goal` | `262144·hhi + 1·neg_goal` |
| Evidence | Tier-1 Farkas, consumed | Tier-1 Farkas, consumed |
| External derivation replay | No | No |
| Residual closer | `omega` | `omega` |
| Local and containing proof replay | Both pass, Lean 4.32.2 | Both pass, Lean 4.32.2 |
| Containing-replay scope | Distinct local/whole types in the original VerInf declaration | Statement-identical `exact hlt` wrapper; checks local-proof binding |
| Checked declarations, local → containing | 3,702 → 3,721 (+19) | 1,470 → 1,471 (+1) |
| Axiom footprints, both declarations | `Classical.choice`, `Quot.sound`, `propext` | `Quot.sound`, `propext` |
| Axiom delta | Empty | Empty |
| Receipt events / retained files | 36 / 74 | 38 / 74 |

Sources: [D1 verdict](../../runs/golden-broker-v3/verdict.json),
[C8 verdict](../../runs/golden-c8-v1/verdict.json),
[C8 receipt log](../../runs/golden-c8-v1/events.ndjson).

C8's residual positivity goal is
`0 < 262144·(v + 1 − 2^42) + (P − 2^18·v)` over integers, with
`v = g_hi.val`. The variable terms cancel; `omega` still discharges that
reconstruction subgoal. This demonstrates SDK synthesis followed by Lean
reconstruction, not improved extraction of a solver proof or replacement of
the residual closer.

## Task derivation and admission

The upstream C1 artifact is an anonymous `example` with imports from the prior
case study. It was not silently relabelled as an unmodified VerInf theorem.
The [task notice](../../tasks/c1-c8-2p18/NOTICE.md),
[source provenance](../../tasks/c1-c8-2p18/source-provenance.json), and
[derivation patch](../../tasks/c1-c8-2p18/derivation.patch) record the self-contained
control, its named wrapper and every import/source change. Original source,
the field definition, corpus, arithmetic truth calculation and saved C1 IR
remain reference artifacts. This control adds branch coverage, not benchmark
breadth or a held-out capability result.

C8's local obligation closes over the wrapper's entire telescope. Its local and
containing targets therefore have the same type fingerprint,
`178f93e731a1a2e54be349d1dd27986f61e203c858350652f1f012f5c70127b2`
([expected declarations](../../tasks/c1-c8-2p18/expected.json)). Containing replay
adds just the `exact hlt` wrapper: it exercises the requirement that the wrapper
reference the saved local proof, not an obligation embedded in a larger real
context. D1's local and whole types differ, and its containing replay adds 19
declarations. The common acceptance predicates do not imply equal coverage of
embedding; C8's recovery-branch claim is unaffected.

The [frozen manifest](../../tasks/c1-c8-2p18/manifest.json) has SHA-256
`b517153f5b2dd878ba724ecc172d38deceb5475f58a0b871daebdcee29852e97`.
Freezing independently checked the human baseline, the instrumented containing
statement against that baseline, and the local/containing proof binding.
The original [freeze records](../../runs/c8-freeze-v1/) and
[overwrite-guard check](c8-freeze-guard.json) are retained.

The C8 admission/episode policy requires the exact recovery branch and witness.
It also compares the resulting IR goal and context with the saved C1 final IR;
both match exactly. Definition/library provenance retains the intentionally
different qualified names. The broker's final C8 solution SHA-256 is
`799feec12af62e5a3dccee0f2890739c48159dac1269087b09a49a9a4d0298b0`.
Independent replay checks 1,470/1,471 declarations for those statement-identical
targets, with the binding-only scope described above.

## Shared harness changes and checks

[`task_spec.py`](../../task_spec.py) registers explicit task identities, source
anchors, declaration pairs and recovery requirements. The compiler, extractor,
broker driver and auditor receive a task explicitly. The CLI accepts registered
IDs; it does not accept arbitrary candidate-selected paths or theorem names.
The original D1 task and capture helper remain unchanged. Receipt logs inherit
their initial task identity and reject a mid-log change.
The [September 8 follow-up](../2026-09-08/REVIEW.md) requires an explicit
registered identity on the first receipt, removes internal D1 task defaults,
and parameterizes the local checkout used only when preparing C8's references.

Conformance version 4 adds four named cases: a proof from the other task, an
explicit conflicting task selection, a changed task ID inside a rehashed log,
and a coherently resealed wrong recovery branch. The latter retains a valid
proof and certificate but must fail the required-branch check. This separates
proof correctness from the claim that a particular search path was exercised.
The registered branch/witness requirements apply to the `cvc4_term_mode_v1`
golden controls. Native, learned and hybrid evaluation policies will need their
own evidence requirements, as specified in the protocol.

- [C8 conformance](../../runs/c8-conformance-v1/tests.json): all 41 checks pass.
- [D1 conformance](../../runs/broker-conformance-v4/tests.json): the same 41 checks pass.
- [C8 completion](../../runs/c8-completion-v1/tests.json) and
  [D1 completion](../../runs/conformance-completion-v4/tests.json): each rejects
  all 45 incomplete/altered suite mutations before publishing success.
- [Review regressions](../../runs/further-review-v2/tests.json): all 26 checks
  pass, including a C8 audit using only retained publication files. The native
  resource observations are reused from the prior review; controlled injections
  and audits are reexecuted.
- [Standalone C8 validation](../../runs/c8-standalone-v1/verdict.json): both
  declarations pass using the saved proof export without broker/solver inputs.

D1's new episode reproduces the earlier uncompressed solution hash
`f4c179f39dc8b5f2116348361bc457ede86e12591d4cd354f0d058bc86e589ca`,
recovery route and axiom deltas. The preservation check covers all 2,336 files
in the pre-C8 task/run snapshot, including the earlier reviewed artifacts.
[Final artifact checks](c8-final-checks.json) record the hash and packaging audit.

These are controlled harness checks. They do not measure model capability,
independent benchmark breadth, general reliability across theories, or verified
computation provenance. Source/binary hashes retain the existing trusted-host
and trusted-build assumptions. The next step is to freeze the model-context
policy and the treatment of P6 before any live learned-search episode.
