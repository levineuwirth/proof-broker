# R6-000 further review — September 7, 2026

Four additional harness issues were reproduced and fixed. No kernel, target-type,
or axiom-policy bypass was found in this review. The original golden episode
remains valid under the stronger audit; a fresh deterministic episode also
passes. This review does not authorize or implement learned search.

## Findings and changes

### 1. A valid seal did not imply consistent evidence claims

The old auditor accepted eight independently modified copies of `golden-broker-v1`
after recomputing their file hashes, event chains, and seals: a wrong recovery
branch; a negative nested certificate verdict; absent kernel targets; a wrong
uncompressed proof hash; an injected resource-monitor error; a missing fresh
certificate-check receipt; a changed source goal; and a missing recovery-start
observation. The unmodified artifact contained none of these defects.

This was an admission/consistency gap. It did not bypass an externally anchored
seal: these probes deliberately supplied new seals. Nor did it make the kernel
accept an invalid proof. It showed that a producer could publish contradictory
records that the auditor failed to cross-check.

[`audit_episode.py`](../../audit_episode.py) now checks the frozen source/context,
policy and receipt bindings, saved certificate and kernel reports, target type
fingerprints, uncompressed proof hash, axiom deltas, resource measurements and
budgets, and required ordered supervisor receipts. `episode.evidence` additionally
requires complete, correctly ordered recovery start/finish observations. Every
file used by the new consistency checker must occur in the retained seal.

All eight mutations now fail at their expected consistency checks. The regression
runner checks the diagnostic reason as well as rejection, and has positive audits
of both golden versions using copies containing only sealed publication files.
Evidence: [before](audit-before.json), [after](audit-after.json),
[probe](audit_probe.py).

### 2. Conformance tests could swallow an unrelated stage failure

The nested certificate/proof test functions caught `RuntimeError` broadly and
then evaluated a native report that might already have been written. Four
controlled injections were counted as passing tests: a positive certificate
followed by supervisor failure; a positive local proof followed by native exit 7;
that proof followed by supervisor failure; and a negative certificate accompanied
by CPU exhaustion rather than its intended native rejection.

These injections execute the actual nested case-function bodies extracted from
the current source, with archived native reports and an injected post-verdict
`StageFailure`. They simulate the failure timing; they are not new native proof
executions. Separate conformance runs provide the native positive controls.

[`checked_stage`](../../test_episode.py) now permits only the explicitly expected
failure category, requires a healthy monitor and completed cleanup, and prevents
resource exhaustion from satisfying a native-negative case. Positive controls
cannot continue after a stage failure. All four injections now propagate the
failure instead of recording success. Evidence: [before](stage-before.json),
[after](stage-after.json), [probe](stage_probe.py).

### 3. Finite CPU overruns could escape the polling verdict

Six real finite workloads exited zero and were accepted with measured CPU usage
of 11,219–17,864 microseconds against budgets of 4,000 or 8,000 microseconds.
The old monitor checked CPU, wall time and output limits in its polling loop;
only OOM received a final check. A workload finishing between the last poll and
EOF could therefore exceed its CPU budget without a rejection.

[`supervise.py`](../../supervise.py) now adjudicates final CPU, execution wall
time, output and OOM measurements before accepting a completed workload. It
records all final violations and whether exhaustion was detected by polling or
final accounting. Cleanup time is recorded separately from the wall interval
used for that verdict. Physical overshoot remains possible; a measured overrun
cannot count as successful completion.

All six repeated native probes are rejected as CPU exhaustion with healthy
monitors and empty workload cgroups. They exited zero; this time all six were
detected by polling. The finite-workload case in conformance-v3 also hit polling,
so those observations alone do not demonstrate execution of the final-accounting
branch.

A controlled regression therefore runs the actual monitor with real EOF pipes,
simulated cgroup counters, and a simulated successful child exit. Below-budget
and exactly-at-budget cases pass. A CPU overrun first visible after the last poll
is rejected with `detection: final_accounting`; the archived monitor accepts that
same controlled overrun. This isolates the race from host scheduling. It is not
a measurement of real cgroup accuracy. Evidence: [native before](resource-before.json),
[native after](resource-after.json), [controlled transition](monitor-after.json),
[native probe](resource_probe.py), [controlled probe](monitor_probe.py).

### 4. A child could insert a supervisor terminal event

A real child emitted an `R6_EVENT` observation named `episode_finished`. The old
monitor appended it, then could not append `stage_finished` because the log
appeared closed. The outer runner classified the result as `stage_rejected`,
although the native child exited zero and the saved process stats reported a
healthy monitor. This did not fabricate a successful sealed episode; it damaged
the receipt chain and mislocated the failure.

Only supervisor terminal rows now close the log. Reserved child terminal events
are rejected before insertion. Observation parsing is opt-in for the instrumented
search stage; raw diagnostics from certificate/kernel checkers are not interpreted
as SDK observations. Malformed, unterminated or reserved observations produce
`observation_protocol_failure`, with the error and cleanup outcome retained.

Both native versions of this negative control now reject at that boundary with
no forged terminal row. The fresh golden search provides a positive control for
the legitimate event transport. Evidence: the `terminal_event` entries in the
[before](resource-before.json) and [after](resource-after.json) probes, and
`reserved_child_event` in [conformance-v3](../../runs/broker-conformance-v3/tests.json).

## Validation actually performed

| Layer | Retained result | Scope |
|---|---|---|
| Fresh deterministic episode | [golden-broker-v2](../../runs/golden-broker-v2/verdict.json) | Real broker search, fresh certificate verification, export, isolated local and containing kernel replay |
| Native conformance and artifact corruptions | [37 named checks](../../runs/broker-conformance-v3/tests.json) | Fresh native validators, resource controls and receipt/source integrity checks |
| Suite completion | [41 rejected mutations](../../runs/conformance-completion-v3/tests.json) | Actual terminal writer; missing, duplicate, unexpected or nonpassing cases cannot publish success |
| Further review | [25 named checks](../../runs/further-review-v1/tests.json) | Two retained-file audits; eight resealed mutations; four stage injections; four controlled monitor cases; seven checked native probe records |
| Provenance consistency | [53 source records and 13 binaries](provenance-check.json) | Base hashes against `e627efe`, overlay hashes against disk, recorded binaries against disk |
| Preservation | [747 file hashes](preserved-files.sha256.json) | Frozen task and earlier retained runs unchanged |

The fresh episode has 36 events and 72 retained files, all hash-checked. Its
uncompressed solution hash is identical to v1:
`f4c179f39dc8b5f2116348361bc457ede86e12591d4cd354f0d058bc86e589ca`.
Both declarations replay on Lean 4.32.2, with 3,702/3,721 declarations checked,
the same three allowed axioms, and empty axiom deltas. The observed path remains
bounded enumeration, witness `2·hZ + 1·neg_goal`, Farkas consumption and residual
`omega`. These are conformance observations on one known obligation.

The source-subtree inventory found only the expected added `episode_trace.ml`
beyond the 53 pinned files. This supports source/binary consistency under a
trusted build and cache. It is **not proof that those sources compiled into those
binaries**. The native glue remains prebuilt and hashed. No new compilation
attestation or verified inference claim follows from this check.

The test counts above are separate units; summing them would misrepresent the
number of corrupt proof objects or independently tested obligations. The review
runner reexecutes audits and controlled injections, but checks the saved native
resource observations. It does not itself rerun those native probes or a kernel.
Its exact expected-case gate prevents omitted or duplicate cases from publishing
success. Before-results and earlier sealed runs were preserved, not repaired in
place.

## Reproduction

Run from the repository root using fresh output directory names. Native commands
require the toolchains, dependencies, Bubblewrap and delegated user-systemd
environment described in [PROTOCOL.md](../../PROTOCOL.md).

```bash
python3 experiments/r6/episode.py golden --run-dir experiments/r6/runs/my-reviewed-golden
python3 experiments/r6/episode.py self-test --episode experiments/r6/runs/my-reviewed-golden --run-dir experiments/r6/runs/my-reviewed-conformance
python3 experiments/r6/test_suite_completion.py --suite experiments/r6/runs/my-reviewed-conformance
python3 experiments/r6/reviews/2026-09-07/resource_probe.py --run-dir experiments/r6/runs/my-resource-probes
python3 experiments/r6/test_review.py --resource-run experiments/r6/runs/my-resource-probes
```

The review probes intentionally keep v1 as their historical mutation baseline;
the stage injections use conformance-v2's saved native reports. The controlled
monitor probe loads the archived v1 monitor to demonstrate the regression.
The original one-off native probe used the same retained C source from `/tmp`;
the reusable runner now resolves that source relative to itself and explicitly
enables observation parsing. The before-implementation hashes are in
[sources-before.json](sources-before.json); the matching old source bodies remain
in the earlier runs' provenance directories. New test runs retain their sources
and supporting artifact hashes.

## Remaining limits before the next step

The Lean replay adapter, capture helper and Comparator code paths were reviewed;
the existing challenge/type/axiom/kernel corruption cases were rerun. No new
bypass was found. That is a bounded review, not a proof of the harness or its
OS/toolchain dependencies. An audit checks saved evidence consistency; fresh
kernel replay checks the proof. Neither authenticates an entire search
computation against a malicious host capable of rewriting data and seals.

D1/70 still does not exercise C1's exact-support recovery. The separate frozen
large-coefficient control remains the next coverage addition. Source versus
IR-only context and the P6 diagnostic-stratum policy remain decisions to freeze
before live calls. No context policy, benchmark breadth, model capability result,
or LLM integration was added during this review. C1's search implementation and
its known G1/G2/P6 limitations remain unchanged.
