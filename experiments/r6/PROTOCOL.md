# R6-000: the deterministic golden evaluation episode

VerInf D1/70 passes from its frozen downstream context through deterministic
Proof Broker search, Farkas certificate checking and consumption, then isolated
validation of both the saved local proof and its containing declaration. This
is a harness check on an already-understood obligation, not a capability or
reliability result. No LLM calls occur.

Step 1 (September 6) froze the original human `omega` proof and validation
challenge. Step 2 adds the broker episode, an append-only receipt log, external
process-tree budgets, and corruption tests. The original task manifest,
challenge, capture helper, human episode, and validator tests remain unchanged.
The search policy is a separately versioned extension of that task.

The retained [`golden-broker-v1` verdict](runs/golden-broker-v1/verdict.json)
accepts both declarations with no axiom changes. Its 36 receipt events record
the bounded-enumeration witness `2·hZ + 1·neg_goal`, tier-1 certificate
consumption, residual `omega`, and fresh proof replay. All
[34 conformance checks](runs/broker-conformance-v1/tests.json) pass. These include
positive controls and cleanup checks, not 34 distinct corrupted proofs.

The September 7 review follow-up retains those artifacts unchanged. The revised
[conformance suite](runs/broker-conformance-v2/tests.json) passes 35 explicitly
named cases, including normal completion under the resource monitor. Its
terminal writer requires every expected name exactly once. Separate
[completion tests](runs/conformance-completion-v2/tests.json) reject 39 mutations
of the recorded results before a passing verdict or completion event is written.
This follow-up reruns conformance against the saved proof; it does not rerun the
golden search episode.

A further [September 7 review](reviews/2026-09-07/REVIEW.md) found and fixed four
additional harness issues: incomplete evidence cross-checks, swallowed stage
failures in conformance tests, CPU overruns missed at process exit, and child
observations that could close the supervisor's log. The fresh
[`golden-broker-v2`](runs/golden-broker-v2/verdict.json) passes the strengthened
audit and both kernel validations. The revised
[conformance suite](runs/broker-conformance-v3/tests.json) passes 37 named checks;
[completion tests](runs/conformance-completion-v3/tests.json) reject 41 mutations;
and [review regressions](runs/further-review-v1/tests.json) pass 25 checks covering
retained-file audits, injected stage failures, controlled monitor transitions,
and separately executed native resource probes. These counts describe distinct
test layers, not a total of corrupted proofs. Earlier runs remain unchanged.

The subsequent [C8 recovery control](tasks/c1-c8-2p18/NOTICE.md) now covers the
other synthesis branch. [`golden-c8-v1`](runs/golden-c8-v1/verdict.json) records
bounded enumeration failing with `search_exhausted`, followed by exact-support
recovery of `262144·hhi + 1·neg_goal`, certificate consumption, and successful
local/containing replay with no axiom changes. Its 38 events distinguish both
recovery attempts. C8's containing declaration is a statement-identical
`exact hlt` wrapper: its replay tests local-proof binding, not embedding in a
larger real context. D1/70 supplies the latter coverage.
A fresh [`D1/70 episode`](runs/golden-broker-v3/verdict.json)
under the shared task support produces the same proof hash as the earlier runs.
The [second-control report](reviews/2026-09-07/C8-CONTROL.md) records the derivation,
checks and limits: both controls pass 41 conformance checks and 45 completion
mutations each; 26 further-review checks and standalone C8 replay also pass.

The [September 8 follow-up](reviews/2026-09-08/REVIEW.md) qualifies that replay
scope explicitly and tightens task initialization and preparation. Its targeted
checks are separate from the recorded kernel and conformance runs above.

## Reproduce

From the Proof Broker repository root, with Python 3.11+, `jsonschema`, Linux
Bubblewrap, a user systemd manager with cgroup-v2 delegation, and the installed
Lean 4.32.0 and 4.32.2 toolchains:

```bash
python3 experiments/r6/episode.py golden --run-dir experiments/r6/runs/my-golden
python3 experiments/r6/episode.py audit --episode experiments/r6/runs/my-golden
python3 experiments/r6/episode.py self-test --episode experiments/r6/runs/my-golden
```

`golden` defaults to `verinf-d1-70`. Use `--task c1-c8-2p18` for the second
control. `audit` and `self-test` infer the registered task from a saved episode;
an explicit conflicting `--task` is rejected. Selection chooses a registered
manifest, source transform and declaration pair, not candidate-supplied names
or paths. The first receipt must specify a registered task ID; subsequent
receipts inherit it and reject any change. Internal task-dependent APIs require
a task argument. Only the documented CLI entry points default to D1/70; saved
episode audits infer a registered identity and check it against the frozen task.
Stages reject an absent, empty, unregistered, or closed receipt log before
launching a child process.

```bash
python3 experiments/r6/episode.py golden --task c1-c8-2p18 --run-dir experiments/r6/runs/my-c8
python3 experiments/r6/episode.py audit --episode experiments/r6/runs/my-c8
python3 experiments/r6/episode.py self-test --episode experiments/r6/runs/my-c8 --run-dir experiments/r6/runs/my-c8-tests
python3 experiments/r6/test_suite_completion.py --suite experiments/r6/runs/my-c8-tests
```

The C8 task is already frozen. `run.py freeze --task c1-c8-2p18` refuses to
overwrite it; its original freeze and human validations are retained in
`runs/c8-freeze-v1/`. Preparing an unfrozen C8 task additionally requires
`--verinf-repo PATH`, a local checkout containing the pinned Model commit listed
in its notice. Normal frozen runs and audits need no such checkout. A new task
ID needs an explicit freeze implementation; it cannot fall through to C8's
provenance enrichment. Standalone `run.py validate` requires `--task c1-c8-2p18`
when checking a C8 export. The human/standalone path defaults to D1/70 and does
not infer task identity from submitted proof data.

The golden run also needs CVC4 1.8 on the host PATH, the SDK's OCaml/Dune
dependencies, the existing bridge C glue library, and a C compiler for the
resource tests. It builds an instrumented overlay under `.cache/instrumented/`
from broker commit `e627efe1ee69638678cc94e3f759d93abd69a160`. It does not rebuild
the original SDK or rerun the C1 campaign. Source hashes, the instrumentation
diff, actual CVC4 version output, build-package versions, and executable hashes
are retained. The prebuilt C glue's bytes are hashed; its compilation is not
attested. Inspect `provenance/build-environment.json` for the recorded machine.

Both human and broker runs need the Mathlib/dependency checkouts and compiled
cache matching `tasks/verinf-d1-70/upstream-lake-manifest.json`. By default it
uses `lean-bridge/.lake/packages`; `--packages-dir` selects another matching
cache. The runner verifies dependency commits, tracked-source cleanliness,
and the frozen cache inventory. It does not install or update dependencies.
Build the bridge's pinned Mathlib environment using the repository's existing
setup before running this command.

Each generating invocation creates a new directory in `runs/`; an existing
directory is never reused. `--run-dir PATH` chooses its name. The retained runs
are `golden-human-v1/`, `validator-tests-v2/`, `golden-broker-v1/`, and
`broker-conformance-v1/`, with the review follow-up in `broker-conformance-v2/`
and `conformance-completion-v2/`. The further review adds `golden-broker-v2/`,
`broker-conformance-v3/`, `conformance-completion-v3/`, `further-review-v1/`,
and the before/after resource probes. Raw stage streams, source inputs, evidence, commands,
resource outcomes, and verdicts are retained. Large proof/type data use gzip
with deterministic headers. Generated `.olean` files, redundant uncompressed
exports, and development runs are ignored by Git.

The second-control follow-up adds `c8-freeze-v1/`, `golden-c8-v1/`,
`c8-conformance-v1/`, `c8-completion-v1/`, `golden-broker-v3/`,
`broker-conformance-v4/`, `conformance-completion-v4/`, and `further-review-v2/`.
The independent saved-export replay is retained in `c8-standalone-v1/`.

Retaining repeated inputs across review/conformance runs is deliberate: each
run preserves its own evidence and provenance. Git deduplicates identical blob
content; apparent filesystem size is not the repository's packed size. The
September 8 review records the selected file count and unique content size.
Review amendments and new checks do not replace earlier sealed artifacts.

`audit` checks the retained files against `seal.json`, the event hash chain,
cross-stage evidence consistency, and the terminal verdict. It binds the frozen
source/context and policy to their receipts, checks the recovery sequence,
compares the saved verifier/kernel reports with the verdict, hashes the
uncompressed proof, recomputes axiom deltas, and checks final resource counters
against the recorded budgets. Contradictory records fail even if their producer
recomputed the seal. It does **not** rerun a kernel or authenticate the producer's
computation. `self-test` reruns fresh certificate and proof verifiers against
saved evidence and disposable corruptions. The following command independently
replays saved proof data without Mathlib, broker, or solver inputs:

```bash
gzip -dc experiments/r6/runs/golden-broker-v1/solution.ndjson.gz > /tmp/r6-solution.ndjson
python3 experiments/r6/run.py validate --solution /tmp/r6-solution.ndjson
```

`validate` accepts serialized proof data, not Lean source. Its trusted checker
is built from the pinned vendored sources. A nonzero exit or absent/negative
trusted verdict is rejection. The actual checking process has an empty
filesystem populated only with its executable, required runtime libraries,
the protected challenge and policy, the submitted export, and scratch output.

## Task identity

This section describes the original VerInf task. The second control's distinct
provenance, source derivation, targets and axiom baselines are documented in
[`tasks/c1-c8-2p18/NOTICE.md`](tasks/c1-c8-2p18/NOTICE.md) and its manifest. It is a
C1-derived synthetic control, not a second unmodified downstream theorem.

The upstream source is
[`Bracket.lean` at `c07e03c94884e9084ffaf7a7294fc0907672f6c2`](https://github.com/JamesPetrie/VerInf/blob/c07e03c94884e9084ffaf7a7294fc0907672f6c2/lean/BracketSpike/BracketSpike/Bracket.lean#L70).
The task unit is the local `hle` obligation at line 70, inside
`Bracket.lift_cell`:

```lean
have hle : (2:ℕ)^24 + 2 * Zmax ≤ P := by omega
```

`Pristine.lean` is the entire original file, byte-for-byte. Its SHA-256 is
`03b4d5ca39f435b0eed7d79fe70e9cc33c401fc7ec240a4120a194b54de722a2`.
The upstream toolchain and Lake configuration are retained alongside it.
This historical source also matches the downstream demo's
`reference/Bracket.original.lean`.

`permitted.patch` adds the trusted `Capture` import and replaces only this
proof's `omega` with `r6_capture_human`. The helper executes the same human
`omega`, saves its closed proof as `Bracket.lift_cell.r6_d1_70`, and fills the
original hole by applying that named proof. All other original bytes, including
the surrounding human proofs, remain in the compilation input. The runner
constructs this file itself; no free-form source submission is accepted.

The context is captured at the original hole, before normalization or broker
reification. It preserves all genuine local binders, including unused ones,
and the values of preceding `have` declarations. Lean represents these as
nondependent lets whose values are hidden by the default `LocalDecl.value?`
API. The helper explicitly preserves them rather than turning them into fresh
assumptions. The serialized closed theorem type is authoritative;
`context/local-context.json` is its readable companion and may abbreviate proof
terms in pretty-printing.

Lean also exposes an auxiliary placeholder for `lift_cell` while elaborating
its body. The context record includes this placeholder with
`included_in_telescope: false`. It is not an admissible hypothesis. An extracted
proof or type that still mentions it fails the closed-expression check.
This exclusion is distinct from selecting useful mathematical hypotheses.

The complete pristine file and human proof are evaluator reference material.
They are **not a selected model payload**. Source-context versus IR-only model
context remains a subsequent decision; no prompt or model context is frozen
by this artifact.

## Two acceptance predicates

These predicates apply to both controls, but their coverage depends on the task.
D1's distinct local and containing statements test reinsertion into its real
VerInf context. C8's statement-identical `exact hlt` wrapper tests the required
reference to the saved local proof; it adds no larger-context embedding check.

`local_obligation_closed` means the saved local theorem exists, has the frozen
elaborated type and corresponding definition meanings, respects the transitive
axiom policy, and its proof dependency closure passes kernel replay.

`whole_declaration_validated` means `Bracket.lift_cell` separately meets those
checks and its saved proof references the named local theorem from the same
export. Both must be true for the episode to be accepted. The shared export
binds the local proof checked in isolation to the local constant consumed by
the containing proof. A reference proves inclusion in the artifact; it does
not establish that every local `have` is mathematically indispensable.

The trusted challenge is itself produced from the original human proof.
Freezing first validates the pristine containing theorem, then compares the
instrumented containing theorem against that pristine export, including all
definitions reachable from its statement. Thus the extraction cannot choose
a new containing target. It then validates the local and containing proofs
and their binding. No `sorry` or challenge axiom is needed.

The allowed transitive axioms are exactly the ceiling
`Classical.choice`, `Quot.sound`, and `propext`. The local and containing human
proofs' exact baseline footprints are recorded separately in `expected.json`.
A footprint includes dependencies in the type, including the preserved local
let values; it is not an assertion that a bare LIA proof needs all three axioms.
A result may use fewer allowed axioms; every added and removed axiom is
reported. Any other axiom, including `sorryAx` or a computation-specific native
evaluation axiom, is forbidden. An allowlist is used rather than a blacklist
of historically known escape names.

## Validation boundary and version accounting

Elaboration and export use the upstream Lean **4.32.0** environment. Final
replay uses Lean **4.32.2**, which fixes the nested-inductive kernel soundness
bug in 4.32.0. This is intentional, not a silent toolchain substitution:
the original environment is exported as proof data and checked by the patched
kernel. See the [4.32.2 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.32.2/).

The exporter and validated NDJSON parser come from
[`lean4export`](https://github.com/leanprover/lean4export/tree/4e7915201d3f9f04470d9eae002fa695f7cdc589).
Statement/dependency comparison and transitive axiom checking use the unchanged
libraries of [`comparator`](https://github.com/leanprover/comparator/tree/2312244ac716564a61cc0bf4e107d9abf1757a61).
`vendor/sources.lock.json` pins revisions and every vendored file's hash.
The 4.32.2 exporter tag changes only `lean-toolchain` relative to the pinned
4.32.0 source, so its parser is identical.

`validate/Replay.lean` is a project adapter, not the upstream Comparator CLI.
It follows Comparator's primitive-constant comparison, axiom policy, kernel
replay, and quotient post-check. It uses the 4.32.2 replay API, selects each
requested theorem's dependency closure, explicitly checks expected declarations
in the replayed kernel environment, and emits machine-readable verdicts.
It additionally validates the export header and full JSON lines (the upstream
parser skips metadata), and checks its read-only input/mount contract before
parsing. Matching a metadata header is a format check, not independent evidence
of which executable produced it. It imports no candidate `.olean` and runs no
tactic. The parser, comparison
library, dependency selection, adapter, runner, frozen challenge construction,
Lean kernel, trusted compiler/cache used to establish the challenge, operating
system, Bubblewrap, and hardware are part of the trust account.

Bubblewrap replaces the filesystem root, clears inherited environment variables,
and creates user, PID, network, IPC and other namespaces. The final replay has
no Lean/Mathlib module cache, source tree, SDK, solver executable, shell, or
provider credentials mounted. It cannot rebuild the proof or call search.
The build/export phases have their own read-only source and library mounts;
the export process cannot overwrite build outputs. Each stage receives only
its own writable output directory. These guarantees assume the supervisor and
host are trustworthy and the OS isolation works; they do not defend against a
malicious concurrent process with the supervisor's host privileges.

The original `run.py` human/standalone-replay path retains its step-1 limits:
150-second wall, 120-second per-process CPU, 32-GiB address space, and 256-MiB
per-file output. The new `episode.py` stages additionally enforce aggregate
process-tree CPU, cgroup memory, and combined stdout/stderr limits, described
below. Neither path's guardrails are a frozen fair-search budget for a paper.

This implementation uses a fresh, patched Lean kernel, not a separately
implemented kernel. Nanoda or another independent implementation is an
additional assurance check, not something this artifact claims to have run.
The [Lean proof-validation guidance](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
motivates this boundary; neither process success alone nor a candidate's own
`#print axioms` output is an acceptance condition.

## Freeze and change control

`manifest.json` binds the pristine source, exact context, expected declarations,
baseline/challenge exports, import pins, permitted patch, capture helper, and
compiled-environment inventory by hash. `expected.json` contains declaration
type fingerprints, baseline axioms, and the trusted comparison policy. Exact
expression comparison, not the fingerprint alone, enforces type identity.

`freeze` is an authoring command used once for this task. It refuses to overwrite
an existing `expected.json`. Changing the target, context policy, source patch,
or allowed environment requires a reviewed task revision; normal runs must never
regenerate expected results from the candidate. The manifest and evaluator code
are controlled by the supervisor, outside the search process's writable area.

`runs/validator-tests-v2/tests.json` retains the validation checks, including
replay of the pristine baseline and the original-to-extracted source binding.
Those original rejection tests exercise malformed exports, wrong/missing targets,
changed definitions, forbidden axioms, invalid proof terms, and a missing local
proof reference. They also check that a valid local proof remains independently
accepted when the containing declaration is changed. These are validator checks,
not measurements of prover capability. The broker conformance suite extends
them with saved certificate, evidence-path, and resource-boundary tests.

## Search policy and observed evidence

`cvc4_term_mode_v1` substitutes the trusted `BrokerCapture` import and
`r6_capture_broker` call for the step-1 capture helper. The original source is
still assembled by the supervisor, and the permitted changes remain one import
and the selected proof-hole replacement. This extends the manifest's original
human-proof policy explicitly; it does not pretend those extra imports were
already authorized by that manifest. Each episode retains the parent manifest
hash, exact source patch, capture source, and `search-policy.json` before search.
The resulting local-context JSON must equal the frozen human context. Final
replay compares the full elaborated types and statement dependencies.

The helper calls `proof_broker_term [cvc4]` once. There is one manifest and one
solver invocation. CVC4 receives the captured SMT-LIB script with its existing
`--tlimit-per 5000` argument. After its `unsat` response, the SDK synthesizes a
Farkas witness. This is not improved extraction of a CVC4 proof trace. D1/70 uses
the existing bounded coefficient enumeration; the overlay also records the
exact-support fallback if reached.

The instrumented path records these actual calls and returns:

```text
local context → reification (including omissions) → dispatch input
→ CVC4 command / input / response → SDK witness synthesis
→ certificate template → dispatcher manifest-hash binding → selection / return
→ certificate verifier → Nat/Int reconstruction → residual omega
→ saved local proof → rebuilt containing declaration → fresh saved-certificate verifier
→ proof export → isolated local and containing kernel checks
```

The fresh certificate check is tied to the saved proof by the certificate observed at creation,
binding, selection, verification, and reconstruction. The checker independently
rechecks the witness, final IR, rewrite trace, and trace's initial-IR binding.
The raw adapter certificate has a zero config-hash placeholder. The dispatcher
fills it with the manifest hash. The log records both versions and rejects any
other change. It must not report them as byte-identical certificates.

Numeric tiers remain unchanged. The verdict records the following independently:

| Field | Meaning on this route |
|---|---|
| `search_succeeded` | The single backend attempt returned the required evidence |
| `certificate_type`, `trust_tier` | `farkas`, existing tier 1 |
| `certificate_producer`, `recovery_route` | SDK synthesis and the observed synthesis branch |
| `certificate_verified` | In-process and fresh saved-evidence checks accepted |
| `certificate_consumed` | The instrumented term-mode closer used this witness and returned successfully |
| `derivation_replayed` | False: there is no external derivation trace on this route |
| `residual_closer` | `omega`, on the reconstructed sum's strict-positivity subgoal |
| `proof_replayed` | The exported proof passed the patched Lean kernel |
| `local_obligation_closed` | Frozen local target, dependencies, axioms, and proof validated |
| `whole_declaration_validated` | Frozen containing target validated and bound to that saved local proof |
| `axiom_delta` | Added/removed transitive axioms relative to each frozen human baseline |

The local final-validation policy additionally requires an occurrence of
`ProofBroker.TermMode.farkasContradictN` in the saved local proof. The unchanged
checker reports this generic dependency check as `local_proof_binding`; for the
containing theorem it checks `Bracket.lift_cell.r6_d1_70` instead. An ordinary
human proof that meets the original task is rejected by the additional broker
path policy. A helper occurrence is a structural check, not a proof that its
coefficients were uniquely necessary or an attestation of how the computation
ran. The consumption claim still depends on the recorded trusted instrumentation.

The reifier drops data locals outside its fragment and `hrec`, a proposition at
`ZMod P`. Their names and reasons remain in the trace. The full original context
remains in the frozen local type. Neither a successful local proof nor this
episode establishes general adequacy of the reifier; C1's P6 dropped-hypothesis
failure remains a separate known issue.

## Receipt log, resources, and artifact integrity

`schema/event.schema.json` fixes the event envelope; `schema/episode.schema.json`
fixes this route's verdict. They complement the frozen task and validation
schemas. Event payloads retain exact IRs, certificates, rewrite traces, solver
interactions, verifier responses, residual goal, and boundary verdicts. The
schemas are deliberately for this deterministic episode, not a complete model
interaction format.

Only the host supervisor appends to `events.ndjson`. Each fsynced row records a
sequence number, predecessor hash, event hash, run/task identity, monotonic
receipt time, UTC receipt time, stage, source, and payload. SDK and Lean
observations share a flushed stderr transport. These are receipt times, not
precise in-process spans: serialization, buffering, scheduling, and observer
work affect them. The pinned dispatcher joins its worker threads before return;
selection and return have separate events. This single-backend run makes no
claim about which concurrent backend is faster.

Observation parsing is explicitly enabled for the instrumented search stage.
Other stages preserve raw output without interpreting it as broker events.
Malformed, unterminated, or reserved terminal observations fail with
`observation_protocol_failure`; a child report cannot end the supervisor's log.

Each stage runs in its own delegated systemd scope. Its trusted monitor is in a
sibling cgroup outside the workload's resource limit and outside Bubblewrap.
The workload cgroup charges the namespace's entire descendant tree, including
children that create new process groups. Default limits are 150 seconds of wall
time, 120 aggregate CPU seconds, 8 GiB of cgroup-accounted memory with no swap,
and 256 MiB of combined stdout/stderr. Cgroup memory includes charged file/cache
memory; it is not summed process RSS. The monitor polls CPU/wall/output limits
at 20-ms intervals; those limits can overshoot by scheduling and read granularity.
Final accounting also checks completed workloads before accepting them. A normal
exit with a measured overrun is resource exhaustion, even if no poll caught it.
The resource-limit receipt distinguishes `poll` from `final_accounting` detection.
Memory uses the kernel's hard cgroup limit. The per-process address-space and
per-file limits also remain in force.

On a limit or failure, the monitor kills the workload cgroup, waits for its
direct child, and verifies that the descendant cgroup is empty. An independent
scope lifetime limit and outer watchdog cover a failed monitor. An OOM can kill
all workload processes while leaving the monitor alive to save the verdict.
`process.json` records exit status, resource exhaustion, wall time, aggregate
CPU, peak cgroup memory, memory events, output bytes, monitor/observation errors,
all final resource violations, and cleanup status. CPU and peak memory exclude
the monitor. `execution_wall_seconds` includes launch and observation and is
used for the wall-budget verdict; `wall_seconds` also includes cleanup. Older
retained stages only have the latter. These overheads are not model search costs.

The `search` stage includes Lean module loading, the broker call, and rebuilding
the containing declaration with its other existing proofs. It must not be
reported as solver-only latency. Preparation/building and cache admission occur
outside the metered stages. Export, certificate verification, and each final
kernel validation have separate resource records. Tokens, model calls, and model
spend are explicitly zero; that is not a claim that compute is free.

After a successful episode, `seal.json` records all retained file hashes, the
terminal event count/hash, and hashes of omitted native/intermediate products.
The gzip proof and raw validation reports preserve the original serialized bytes.
A rerun creates new observations; it does not recover omitted historical bytes.
An existing run cannot be overwritten and a terminal log cannot be appended to
through this API. These rules protect against the sandboxed search and ordinary
artifact damage. The seal is not externally authenticated until anchored in
trusted version history or an equivalent record. A host operator could rewrite
both data and hashes. No event, hash chain, or binary hash proves that a claimed
model computation occurred.

## Corruption tests and failure attribution

The conformance runner operates on copies and checks both the result and the
expected rejection stage. Its retained `tests.json` identifies the source
episode/seal, test sources, individual outcomes, and supporting artifact hashes.
Since version `r6-conformance-2`, it records the independent expected-case registry.
Finalization rejects missing, unexpected, duplicate, or nonpassing entries
before writing `passed: true` or `tests_finished`. Interim verdicts remain
`passed: false`.

Version `r6-conformance-3` requires the exact expected stage-failure category.
A saved native verdict cannot override a supervisor failure, resource failure,
or nonzero exit in a positive control. Native negative tests must reject at
their intended boundary with a healthy monitor and completed cleanup.

Version `r6-conformance-4` runs the same 41 named checks for either task. It adds
foreign-task proof rejection, explicit wrong-task selection, a task-identity
change inside a rehashed log, and a coherently resealed wrong recovery branch.
The last mutation preserves the proof and certificate: it verifies that a valid
proof cannot stand in for exercising the control's required search branch.

The completion tests call that actual terminal writer after deleting each
recorded case in turn, replacing one case with a duplicate while preserving the
count, adding a duplicate or unexpected case, or marking a case failed. They
require rejection at the completeness guard, preservation of the failure
marker, and absence of a completion event. These tests have their own expected
mutation-name gate. Reproduce them after a successful conformance run:

```bash
python3 experiments/r6/test_suite_completion.py --suite experiments/r6/runs/broker-conformance-v4
```

| Deliberate change | Expected boundary |
|---|---|
| Malformed certificate | Certificate decoding |
| Zero witness or valid certificate for a different goal | Certificate verification |
| Changed dispatch input without its trace | Input/trace binding |
| Wrong target, changed containing statement, missing declaration | Challenge comparison |
| New axiom, `sorryAx`, fresh native-escape axiom name | Transitive axiom allowlist |
| Invalid proof term | Kernel replay |
| Human proof without Farkas construction, or inlined local proof | Required proof reference |
| Changed original target/source | Task construction/integrity |
| Dropped, duplicated, reordered events; substituted consumed certificate; truncated episode | Chain, evidence consistency, or seal audit |
| CPU, wall, memory, or output exhaustion with forked descendants | Resource monitor and empty-workload check |
| Finite CPU overrun, including one first visible at EOF | Resource exhaustion despite native exit zero |
| Child report claiming a supervisor terminal event | Observation protocol, before log insertion |

Positive controls include the real local/containing broker proofs, the actual
certificate, a positively rescaled witness, and a valid certificate for a
different weaker goal. The cross-goal negative test therefore cannot pass merely
because it was given an intrinsically invalid certificate. A fresh synthetic
native axiom tests the allowlist; it does not execute every historical native
escape or reproduce the old `apply?` frontend bug.

A dedicated resource control starts four child processes in new process groups,
allocates and touches bounded memory, waits for all four successful exits, and
emits a completion marker. It must finish with exit zero, no exhaustion flag,
no resource-limit event, no monitor error, and an empty workload cgroup.

The further-review runner also exercises the real monitor control flow with
simulated cgroup counters and a successful child exit. Below-budget and
exact-budget EOF cases pass; a last-poll-to-EOF CPU overrun fails through final
accounting. The archived monitor accepts that same overrun. This is a controlled
regression test, separate from the native cgroup probes; native finite workloads
can hit either detection path depending on scheduling. The report distinguishes
rerun audits/injections from replayed native resource observations:

```bash
python3 experiments/r6/test_review.py --resource-run experiments/r6/runs/resource-review-after-v1
```

An incomplete episode writes `failure.json` and retains the available stage
streams/events. `failure_stage`, `failure_category`, resource details, and the
native checker's narrower stage locate the observed failure. Causal attribution
is explicitly unassigned: a stage rejection alone does not distinguish a bad
benchmark, unsupported theory, reifier defect, or invalid candidate. Missing
monitor output is `supervisor_failure`, never a negative model-capability result.
These controls exercise this route and the independent validators; they are not
a complete conformance suite for every broker tier, backend, or future agent.

## Next decision

Select and freeze source context versus IR-only context before the first live
model call. Then add one learned search policy behind the same task identity and
final acceptance boundary, extending the event schema with request/response,
revision, sampling, retries, and model cost. Native Lean, deterministic broker,
learned, and hybrid policies need explicit policy-specific evidence requirements;
a direct valid proof should not inherit the Farkas-helper requirement of this
golden route. Benchmark expansion and capability comparisons follow that policy
work, not from this one successful episode.

D1/70's coefficient 2 lies inside the existing enumeration bound of 3. It does
not exercise `try_close_exact` and is not a regression anchor for C1's new
recovery branch. The second control implements the previously recommended
coverage addition from C1's `C8_coef_2p18` shape: its witness needs a multiplier of 262144
([checkpoint 2, diagnostic table](../c1-cert-recovery/reports/checkpoint-2.md)).
It requires observations of bounded enumeration failing and exact-support
recovery succeeding, followed by certificate consumption and final proof
validation. Its new R6 episode supplies those observations independently of the
earlier C1 logs. This covers another branch; it does not add independent benchmark
breadth. Both deterministic controls now precede the model-context decision.

Freeze P6's treatment alongside the context policy. The original
`P6_hyp_le` obligation is true, but its truncated-Nat-subtraction range hypothesis
is dropped and the resulting IR admits a counterexample
([checkpoint 1, limitation 6](../c1-cert-recovery/reports/checkpoint-1.md)).
An IR-only policy cannot recover that missing information from its payload;
`sat` concerns the weakened IR, not the original obligation. Recorded omissions
alone do not decide whether a particular dropped hypothesis is needed.

Recommendation for the first learned policy: retain P6 and other known cases of
inadequate IR in a named diagnostic stratum, outside the primary model-capability
denominator. Freeze that membership and its audit rationale before live calls;
report the exclusions and keep those tasks in end-to-end failure accounting.
Admission should not require deterministic automation to solve a task. A source
policy may recover information unavailable to an IR-only policy, so any paired
comparison on this diagnostic stratum measures context/translation repair as
well as search. Report original-task truth, IR status, context supplied, and the
failure boundary separately. This is a proposed scope rule; no learned-policy
selection or exclusion has yet been implemented.

## R6-001 checkpoint amendment — 2026-09-08

The preceding next-decision section records the R6-000 checkpoint. The
[R6-001 implementation](R6-001.md) now adds a one-request, no-fallback fixture
policy for Farkas witness proposals. Its implemented default is strict compiled
arithmetic IR. A field-level sanitized Lean context is retained and tested
separately as evaluator reference data; it is not part of that request.

The [policy](policies/fixture-farkas-v1.json) binds the
[pre-search admission rule and control membership](policies/admission-v1.json),
including an independently checked counterexample to P6's weakened IR. The new
policy separates witness proposer from certificate assembler and preserves the
existing Farkas-consumption and independent declaration-validation requirements.
Historical deterministic policies, artifacts and branch requirements remain
the reference for R6-000. This checkpoint contains no live learned search; the
next decision is the final context choice and a separately frozen live policy.

The author approved R6-001 after independent recomputation on 2026-09-08. The
[review closeout](reviews/2026-09-08/R6-001-REVIEW.md) qualifies the six negative
cases as five failure categories and distinguishes detector stage from logical
phase. The [next policy's requirements](LIVE-POLICY-REQUIREMENTS.md) now require
model-visible row semantics with exact prompt-byte binding, distinct admission
review versus payload-integrity errors, and explicit provider transport/retry
accounting. The approved fixture policy and evidence remain frozen.

## R6-002 checkpoint amendment — 2026-09-08

The [R6-002 checkpoint](R6-002.md) now implements a frozen arithmetic prompt,
request/prompt binding, and capture of the actual serialized bytes read by a
local canned receiver. The new `canned_envelope_v1` policy preserves the
R6-001 request information boundary and Farkas consumption/replay requirements.
The approved historical sources, policies, tasks and episodes remain unchanged.

The response's echoed digest checks association only. The canned receiver
deliberately ignores the arithmetic body. Altered-message controls retain a
passing echo but fail independent envelope validation; well-formed wrong
witnesses pass both transport checks and fail certificate verification.
Admission-review versus injected-payload errors now differ, and new failures
record logical phase separately from detector stage. Unavailable simulated
usage is null; actual live-model calls and spending are zero.

The checkpoint passed 36 focused prompt/transport/admission checks, 13 native
episodes (three positive runs on two tasks, ten deliberate failures), and 35
artifact/audit regressions. All 5,698 preserved files pinned to `79a4a07` match.
The three positive episodes have empty axiom deltas. C8 retains its previously
qualified, statement-identical wrapper scope. This is readiness of the local
interface, not a model-capability experiment or provider-transport validation.

Next comes review of this artifact, followed by selection and freezing of the
provider adapter, exact outbound capture, model revision, sampling settings and
budget. Canned responses must exercise that adapter boundary before live calls.

The author approved R6-002 after independent recomputation on 2026-09-08.
The [review closeout](reviews/2026-09-08/R6-002-REVIEW.md) records three
next-policy requirements: relation coverage before expansion, structured
envelope-component diagnostics, and reuse of the existing frozen proof-check
module. Current LIA compilation emits `le`/`eq`; a genuine `lt` path requires
separate admission and end-to-end evidence. The approved broad prompt and
its artifacts remain unchanged. Response decoding/support/binding acceptance
is distinguished from the separate certificate's mathematical verdict.
