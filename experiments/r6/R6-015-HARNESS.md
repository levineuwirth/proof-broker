# R6-015 — replay harness, for review

**Harness revision 3**, 2026-10-01. It responds to [the review of revision 2](reviews/2026-10-01/R6-015-HARNESS-REVIEW-2.md), which
found one remaining P2: control 8's binding ignored the run's provenance and its terminal event. Revision 2 (`f26ff76b`, code
`1425f84b`) responded to [the review of revision 1](reviews/2026-10-01/R6-015-HARNESS-REVIEW.md), which found three P1 defects and
one P2 gap, and approved two pinned-route rehearsals after the repairs, as a limited pre-lock exception. Revision 1 is
`ef995231`. The harness builds on step 2's bridge,
[approved](reviews/2026-10-01/R6-015-BUILD-REVIEW-2.md) at `476fab31`. It implements the replay of
[the proposal, revision 5](R6-015-PROPOSAL.md) (step 5) and control 8, with the three recorded harness requirements.

**Status:**
- **Nothing is locked, and nothing of R6-015's has been replayed.** Without the lock, every planned episode is refused at its
  boundary.
- **Both approved pinned rehearsals ran and reproduced R6-014** ([record](reviews/2026-10-01/R6-015-HARNESS-REHEARSAL-PINNED.json)).
  The runs are sealed under `r6-015-rehearsal-runs/` and excluded from R6-015's results. The synthetic rehearsal of revision 1
  stands ([record](reviews/2026-10-01/R6-015-HARNESS-REHEARSAL-SYNTHETIC.json)).
- **What was read:** the two rehearsals' sources (l069 draw 1's `evidence.json`, l069's deterministic events), by the harness, as
  approved; and, for revision 1, the field names of l069's and l170's deterministic events. No other certificate was read.
- R6's harness locks still verify. No R6 file was edited.

## What changed in revision 3

**P2: control 8 binds provenance and termination, before the outcome is used** (`replay_campaign.bound`, now given the verified
lock and its digest). Besides revision 2's checks:
- **The start record** must name the verified lock's digest, its bridge revision, the replay schema and the locked harness
  digests.
- **The run's provenance** must match the lock: its copies of the harness, and its instrumented `Tactic.lean`.
- **Exactly one `episode_finished`**, the last event and from the supervisor, must name the verdict's outcome and digest.
- **The seal's acceptance flag** must agree with the outcome (accepted exactly for a proof).

`r6-015/test_binding.py` writes sealed synthetic runs with R6's own event chain and seal, shaped as `execute` writes them. The
lock, the plan, the packet source and the audit report are stand-ins. Results:
- **Refused before the outcome is used:** every probe, including the review's three:
  - a start record naming another lock;
  - another bridge;
  - another harness;
  - another schema;
  - a rehearsal start;
  - a verdict resealed to disagree with the terminal event;
  - a sealed run with no terminal event, as a proof and otherwise;
  - a disagreeing acceptance flag;
  - a changed harness copy;
  - a changed instrumented `Tactic.lean`;
  - an unsealed file.
- **Bind:** well-formed runs.
- **Control 8 itself** now fails on the unfinished proof that passed in the review's probe, and passes the well-formed one.

**Real episode output** was also checked. Both sealed rehearsal runs meet the new terminal, seal and provenance checks. Their start
records name `admission: rehearsal`, so control 8 would refuse them as planned episodes, as it should.

## What changed in revision 2

1. **P1: admission at the episode boundary** (`replay_lock.admit`). Admission runs before anything else is run or written,
   through `execute` and through the command line, which admits before it creates the run directory.
   - **A planned episode** must be exactly its entry in the locked plan, and the lock must verify.
   - **A pinned episode** must be exactly one of the two approved rehearsals (`REHEARSALS`: bridge `476fab31`, the option unset,
     injection disabled). Its records are marked `admission: rehearsal` and `excluded_from_results: true`.
   - **Nothing else is admitted.** A probe with a constrained spec and no lock was refused, with nothing written.
   - **The expected events now come from the spec.** `certificate_gate_bypassed` is required under injection and forbidden
     otherwise, and must name this packet's certificate. The pinned route's own events (`residual_started`, `residual_finished`)
     are required on that route only.
2. **P1: the lock binds the complete source closure** (`replay_lock.lock_record`).
   - **Python:** every module the episode, campaign and supervisor processes import from `experiments/r6`, found by importing
     them. That is 31 files, `site_network.py` among them.
   - **Data:** the capture helper, the event and site schemas, the checker and assembler sources, the vendor lock, and R6's
     harness locks: census, site, fixture and qualification audit.
   - **Binaries:** the compiler, the exporter, the kernel checker, the glue library and the audit program.
   - **Bridge and plan:** the bridge revision and the instrumented `Tactic.lean`; the plan; every planned episode's source seal
     and consumed artifact.
   - **The census and site locks** are also verified directly.
   - **Nothing is loaded lazily outside this closure.** The rehearsal compared the modules it loaded with the closure computed in
     a fresh process, and none was outside it.
3. **P1: control 8 binds every run to the locked plan before it branches on the outcome** (extended in revision 3, above). For
   every planned episode, proof or not:
   - **the seal:** every file present is sealed, every retained file matches, and the event chain matches the seal;
   - **the spec, the start record and the verdict's identity fields** (id, site, source, route, coefficients, injection,
     admission) equal the plan's entry;
   - **the packet** equals the one rebuilt from the locked source and the spec's coefficients;
   - **for a proof, the receipt** is the one the spec requires.

   A run that fails these is recorded as unbound, and control 8 fails. Afterwards every audited artifact is rechecked against its
   seal, and the lock is verified again.
4. **P2: complete command records.** The residual's audit command and control 8's audit commands are recorded in full: the
   argument list with temporary paths normalized, the environment, each input's origin and digest, the exit code and the tool's
   digest.

## The pinned rehearsals

| rehearsal | outcome | closer, final step | kernel replays, axioms | residual from the export | export |
|---|---|---|---|---|---|
| l069 draw 1, learned | proved | `term_mode_nat`, `omega` | local and whole accepted; no axiom delta | binds (`matches_residual`); `certificate_alone` at both targets; control 8's predicate met | **byte-identical** to R6's retained `solution.ndjson.gz` |
| l069, deterministic | proved | `term_mode_nat`, `omega` | the same | the same | **byte-identical** to R6's |

Each reproduces its R6-014 result. The site path is now exercised end to end on the new revision:
- setup with the new modules;
- retained-packet loading, from a learned run's evidence and from a deterministic run's events;
- the independent check, capture and reconstruction under the site stage;
- the pinned receipt, export and kernel replays;
- the residual from the export, and the seal.

The `certificate_alone` classifications agree with the qualification audit's for l069. They test control 8's path only and are
not results.

## The three requirements

1. **The option setting is frozen.** The reconstruction helper is R6's, with one call changed: `set_option
   proofBroker.term.constrained true in proof_broker_term [r6_fixture_witness]`. The lock binds it by digest. Every run records
   the value the closers saw (`term_route`), and its receipt check requires that value to match the route.
2. **The receipt names the constrained final step.** On the constrained route, `reconstruction_finished` carries the
   certificate, the closer, `final_step: constrained`, `residual_closer: constrained_normalization` and
   `constrained_option: true`. The episode requires exactly the events the spec implies, in order, all naming this certificate
   and the same closer.
3. **The residual is printed from the exported term.** The audit program of `qualification-audit-v1` reads the run's export in
   `--synthetic` mode, and its printing of `hpos`'s type is retained. Control 8 then runs the program in real mode with it.
   Binding the run to its export rests on the seal, the targets and the certificate.

## The modules (`experiments/r6/r6-015/`)

- **`replay_lock.py`**: admission, the approved rehearsals, the closure, the lock record and its verification.
- **`replay_bridge.py`**: the bridge at `476fab31`, from git, with R6's frozen overlays unchanged, then R6-015's:
  - `term_route`;
  - `closer_selected` in `closeConstrained`;
  - the constrained receipt;
  - the injection bypass, recorded as an event, for controls 1(b) and 4 only.

  The SDK, the checker and the assembler are R6's, from its base. R6's frozen setup is used with this build.
- **`replay_episode.py`**: one sealed episode per admitted spec:
  1. the packet, retained and checked against its source's seal; a mutation replaces only the coefficients;
  2. the independent check;
  3. capture and reconstruction under R6's site stage;
  4. the receipt and the frozen context;
  5. export, and the local and whole kernel replays;
  6. the residual from the export;
  7. the verdict, terminal event and seal, on every path.
- **`replay_campaign.py`**: `lock` (once), `run` (the plan, the lock verified before and after) and `control8`.
- **`rehearse_synthetic.py`** and **`rehearse_pinned.py`**: the two rehearsals.
- **`test_binding.py`**: control 8's binding, on sealed synthetic runs.

## Next, in the agreed order

1. Step 3: the mutation sets and their validity labels (exact arithmetic over the retained rows, and the checker), the control-5
   maps (identities, matches to the audited maps, expectation labels), and the plan.
2. The analysis program, frozen.
3. The lock (step 4), then the replay.
