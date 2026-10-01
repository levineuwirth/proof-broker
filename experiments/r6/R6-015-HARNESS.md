# R6-015 — replay harness, for review

**Harness revision 1**, 2026-10-01. It builds on step 2's bridge, [approved](reviews/2026-10-01/R6-015-BUILD-REVIEW-2.md) at
`476fab31`. It implements the replay of [the proposal, revision 5](R6-015-PROPOSAL.md) (step 5) and control 8, and carries the
three recorded harness requirements.

**Status:**
- **Nothing is locked, and no retained certificate has been replayed.** `run` and `control8` refuse without the R6-015 lock.
- **The harness was rehearsed on synthetic goals only**, through R6's own helpers
  ([record](reviews/2026-10-01/R6-015-HARNESS-REHEARSAL-SYNTHETIC.json)). The site path has not run; see the proposal at the end.
- **What was read:** the field names of one deterministic run's events (l170, the negative control), to rebuild deterministic
  packets. No certificate's coefficients were read for this build.
- R6's harness locks (`site-harness-v4`, `fixture-harness-v1`, the census lock) still verify. No R6 file was edited.

## The three requirements

1. **The option setting is frozen.** The reconstruction helper is R6's, with one call changed: `set_option
   proofBroker.term.constrained true in proof_broker_term [r6_fixture_witness]` (`replay_bridge.CONSTRAINED_CALL`). The lock
   binds it by digest. Every run also records the value the closers saw (`term_route`), and the receipt check requires it.
2. **The receipt names the constrained final step.** After `closeConstrained` returns, the overlay emits `reconstruction_finished`
   with this certificate, the closer, `final_step: constrained`, `residual_closer: constrained_normalization` and
   `constrained_option: true`. The episode requires exactly `term_route`, one `closer_selected` and that receipt, in order, after
   R6's reconstruction prefix, all naming this certificate and the same closer.
3. **The residual is printed from the exported term.** After the kernel replays, the audit program of `qualification-audit-v1`
   reads the run's export in `--synthetic` mode, and its printing of `hpos`'s type is retained as the run's `residual.txt`. Control
   8 then runs the program in real mode with that residual.
   - The binding therefore checks the printer and the export against each other.
   - Binding the run to its export rests on the seal, the targets and the certificate, as the review of revision 4 said.

## The modules (`experiments/r6/r6-015/`)

- **`replay_bridge.py`**: the bridge at `476fab31`, from git, with R6's frozen overlays unchanged
  (`consumption_overlay.lean_edits`: observations, packet delivery, closer observations), then R6-015's:
  - `term_route`, the option's value when the closers are reached;
  - `closer_selected` inside `closeConstrained`, before each closer runs;
  - the constrained receipt;
  - `R6_015_INJECT_UNVERIFIED=1` bypasses the bridge's own certificate gate, recorded as `certificate_gate_bypassed`, for
    controls 1(b) and 4 only.

  The SDK, the independent checker and the assembler are R6's, from its base. The SDK is byte-identical at both revisions.
  `setup` is R6's frozen setup with this build: environment and inventory checks, provenance and binaries.
- **`replay_episode.py`**: one sealed episode per spec. The steps are as follows.
  1. **Setup.**
  2. **The packet.** It is the retained one, checked against its run's seal: a learned run's `evidence.json`, or a deterministic
     run's packet rebuilt from its sealed, hash-chained events (`dispatch_started`, `dispatch_received`). A mutation replaces only
     the coefficients.
  3. **The independent check.** A rejection ends the episode, except under deliberate injection.
  4. **Capture and reconstruction,** under R6's site stage, with the packet delivered as in R6.
  5. **The receipt.**
  6. **The frozen context check.**
  7. **Export, and the local and whole kernel replays** (R6's `final_validation`, with the axiom delta).
  8. **The residual from the export.**
  9. **Verdict, terminal event and seal,** on every path. A failure is recorded with its stage, the events observed and the
     closer's error lines.
- **`replay_campaign.py`**:
  - `lock` writes the R6-015 lock once. It binds this harness, R6's harness locks, the bridge revision and the instrumented
    `Tactic.lean`, the plan, every planned episode's source seal and consumed artifact, the audit program and the exporter.
  - `run` replays the plan, verifying the lock before and after. The plan may contain only the constrained route.
  - `control8` evaluates revision 5's frozen predicate on every proof.

## The synthetic rehearsal

`rehearse_synthetic.py` builds the replay bridge and drives R6's preparation and reconstruction helpers directly, on a synthetic
mixed-carrier goal: `z + ↑n ≤ 5`, from `n ≤ m` and `z + ↑m ≤ 5`. The packets are assembled by R6's driver from witnesses written
for it.

| case | observed |
|---|---|
| valid witness, constrained | closes. Events: R6's prefix, then `term_route` (true), `closer_selected` (`term_mode_int`, constrained), and the receipt with `final_step: constrained`. The residual printed from the export binds (`matches_residual`), and **control 8 passes** (`certificate_alone`) |
| `neg_goal` doubled, constrained | the bridge's own gate refuses it (`farkasNotContradictory`); no closer runs |
| the same, injected | `certificate_gate_bypassed` is recorded; the constrained closer is selected and fails, the sum not cancelling |
| valid witness, pinned route | `term_route` records the option unset; R6's ℕ closer refuses the `Int` goal: **the refusal R6 met at the four sites**, reproduced synthetically |

The rehearsal also showed that R6's SDK refuses to prepare a goal with `Int` division. The goal is therefore division-free, unlike
the bridge's synthetic tests, which never run the SDK.

## For review

1. **The packets are the retained ones,** and preparation is not re-run. The reconstruct stage's guard requires the packet's input
   IR to equal the goal freshly reified by the new bridge, whose reifier is unchanged.
2. **A mutation changes only the multipliers.** The certificate envelope binds the final IR and the trace, not the coefficients;
   the independent checker then judges the mutated certificate.
3. **The injection bypass** is a harness overlay, set by an environment variable and recorded as an event. It is used only in
   controls 1(b) and 4.
4. **The audit program runs outside the site stage,** as a recorded subprocess with its digests. It reads only the export.
5. **The site path is unexercised.** The following steps have not run: the setup with the new modules, site-stage capture and
   reconstruction, retained-packet loading, final validation and the seal.

   **Proposed, not run without approval:** before the lock, two rehearsals **on the pinned route**, which runs no candidate
   closer:
   - l069 draw 1 (learned);
   - l069's deterministic run.

   Each should reproduce its recorded R6-014 result (`term_mode_nat`, proved). l069 draw 1's export was already read in the audit
   prototype. This is a replay of retained certificates, which is why it needs your decision.

## Next, in the agreed order

1. Step 3: the mutation sets and their validity labels (exact arithmetic over the retained rows, and the checker), the control-5
   maps (identities, matches to the audited maps, expectation labels), and the plan.
2. The analysis program, frozen.
3. The lock (step 4), then the replay.
