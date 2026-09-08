# September 8: C8 replay scope and explicit task initialization

C8's containing replay establishes local-proof binding through a
statement-identical `exact hlt` wrapper. D1/70 additionally exercises reinsertion
into a larger real VerInf declaration. The [C8 report](../2026-09-07/C8-CONTROL.md),
[task notice](../../tasks/c1-c8-2p18/NOTICE.md), and
[protocol](../../PROTOCOL.md) now distinguish these scopes explicitly. C8 still
covers exact-support recovery after bounded enumeration fails.

[Fresh retained-artifact audits](retained-audits.json) reproduce the two identical
C8 type fingerprints and the 1,470 → 1,471 declaration counts. D1's local/whole
fingerprints differ, with 3,702 → 3,721 declarations. These are checks of saved
reports and their evidence chain, not new kernel executions. The earlier report
and source versions are retained under [`before/`](before/).

## Task and preparation changes

- [`run.py`](../../run.py) enriches C8 positively and rejects an unsupported
  freeze task before toolchain work or writes. A third control needs its own
  explicit freeze implementation.
- [`events.py`](../../events.py) requires a registered task ID on the first
  append. Later receipts inherit it; empty/unknown IDs or conflicting explicit
  IDs fail before writing. [`episode.stage`](../../episode.py) rejects an absent,
  empty, unregistered, or closed receipt log before preparing a native stage.
- Internal task-dependent APIs now require an explicit task argument. CLI
  defaults remain documented; saved episode audits infer a registered identity
  and validate it against the frozen task. The D1-specific legacy validator
  tests and review probes now supply their identity explicitly.
- [`c8_control.py`](../../c8_control.py) accepts the VerInf reference checkout
  through `prepare(model_repo=...)`; the freeze CLI exposes `--verinf-repo`.
  It reads the pinned Git object and retains the existing frozen-task guard.
  Ordinary episodes need the retained bytes, not the original agent worktree.

No broker SDK, reifier, certificate reconstruction, Lean capture source, frozen
manifest, expected declaration, or saved episode was changed.

## Checks executed

| Check layer | Result | Scope |
|---|---|---|
| [Task initialization suite](../../runs/task-initialization-v1/tests.json) | 20/20, exact expected case set | Missing/invalid identity, inheritance/conflict, stage preflight, required API arguments, explicit freeze dispatch, portable preparation, CLI guards, two native positive stages |
| [Existing review regressions](../../runs/further-review-v3/tests.json) | 26/26 | Retained-file audits and fresh controlled injections; earlier native exhaustion observations are rechecked, not rerun |
| [Retained golden audits](retained-audits.json) | Four accepted | D1 v1/v2/v3 and C8 v1; hashes, receipts, policies and saved verdict relationships |
| [Model reference read](model-reference-check.json) | Exact byte match | Actual parameterized `git show` from a local VerInf checkout at the pinned revision |
| [Final checks](final-checks.json) | See machine-readable results | Preservation, test/source hashes, packaging and Python call-site validation |

The initialization suite demonstrates the old silent D1 default using the
preserved writer. Its negative controls require the expected exception before
any receipt or stage directory is written. Both identities also pass fresh
normal-completion stages through systemd, Bubblewrap and the resource monitor,
with no exhaustion, monitor error or remaining workload. These stages use the
existing C resource fixture; they do not invoke Lean or proof search.

Temporary freeze tests use recorded environments and a stubbed inventory, and
the configurable-checkout preparation test mocks only the VerInf Git-object
read. They test dispatch and reference plumbing, not a newly established frozen
challenge. The separate actual Git read above checks the pinned reference bytes.
The suite requires every expected case exactly once before publishing success;
its interim report remains `passed: false`.

No golden episode, kernel replay, full certificate/proof conformance suite, or
completion-mutation suite was rerun in this follow-up. The earlier 41-case and
45-mutation results remain historical evidence from their recorded source
versions. The 20 and 26 checks above are different layers and should not be
combined into a headline count of corrupted proofs. Source and binary hashes
continue to assume the recorded host/build process; there is no compilation or
inference attestation.

## Preservation and retention

[`pre-review-files.sha256.json`](pre-review-files.sha256.json) freezes the bytes
of 3,243 pre-existing task/run files, including ignored development files. Task
notices and `__pycache__` entries were filtered from that original snapshot;
the latter are regenerable bytecode. It includes 491 Git-ignored development
files but is not an exhaustive filesystem inventory.

The final review narrows the notice exclusion to the amended C8 notice through
[`preservation-supplement.sha256.json`](preservation-supplement.sha256.json).
The supplement adds D1's unchanged notice using its hash from the earlier
[pre-C8 snapshot](../2026-09-07/pre-c8-files.sha256.json), without rewriting the
reviewed 3,243-entry snapshot. The combined guard covers 3,244 files and retains
every non-bytecode entry from the earlier snapshot. Its one `.pyc` entry remains
filtered as regenerable data; it was never part of the episode seal.
Sealed runs and frozen task artifacts remain unchanged. The final check rejects
any discrepancy against the combined guard. No old run is replaced or pruned.

Retaining repeated evidence across the selected runs is deliberate. Every
conformance directory keeps its own inputs and provenance; identical content
shares a Git blob. The final check records selected paths, apparent bytes and
unique content bytes. Unique content is **not** a measurement of compressed
pack size, filesystem usage, or push size. New code snapshots and small review
outputs account for this follow-up's growth.

The [staged whitespace check](commit-preflight.json) reports 30 blank context
lines inside retained unified patches. Each is exactly one ASCII space, required
by the patch format. All other staged files pass the check. These warnings are
recorded without normalizing or changing the hashed patch artifacts.

The commit split is:

1. C1 reporting amendment: `experiments/c1-cert-recovery/README.md` and
   `experiments/c1-cert-recovery/reports/checkpoint-2.md`.
2. R6 harness, controls and retained review evidence: `experiments/r6/` plus the
   root `README.md` link to R6. That README hunk contains no C1 correction.

The initial follow-up left these changes uncommitted. The final review closes
with separate local commits in the order above, without pushing. Commit reporting
attributes the two fresh native controls to the 20-case initialization suite;
the 26-case review suite rechecks earlier native observations. The next research
decision remains source context versus IR-only context, with P6's
dropped-hypothesis confound handled explicitly before connecting a learned policy.
