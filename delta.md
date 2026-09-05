# Roadmap delta: v1.0 → v1.1

**Subject:** Shared library implementation language
**Decision:** OCaml (revised from Rust)
**Decided by:** Authors of spec v1.0, in light of Phase 4 commitments and team composition
**Status:** Accepted; integrated into engineering plan; spec revisions tracked separately

---

## 0. Summary

The roadmap v1.0 recommended Rust as the implementation language for the
shared library hosting the IR rewriter, certificate verifier core,
dispatcher, and cache. After explicit consideration of (a) the seriousness
of the Phase 4 Rocq probe as an architectural validation step, and
(b) the implementing team's language profile, the decision is revised
to OCaml.

This delta document records:

1. Why the decision was revised.
2. What changes in the engineering plan as a result.
3. What changes in the spec as a result.
4. The conditions under which this decision should be reconsidered.

The original roadmap (v1.0) remains the baseline document. This delta
amends specific sections without superseding the whole. A future v1.1
roadmap may consolidate these changes; for now, both documents should be
read together.

---

## 1. Decision rationale

### 1.1 The deciding axes

Two axes, weighed against each other:

**Phase 4 seriousness.** The roadmap's Phase 4 (Rocq architectural probe)
is framed as the validation milestone for the entire architecture — the
point at which we find out whether the IR is genuinely cross-system or
accidentally Lean-shaped. It is one of three explicit decision points in
the roadmap, with revision triggers if the probe surfaces material schema
gaps. Treating Phase 4 as real — not as a checkbox — substantially
elevates the value of OCaml, because the Rocq plugin is OCaml-native and
direct linking eliminates an FFI boundary on the side of the architecture
where the validation actually happens.

**Team composition.** The implementing team has OCaml experience.
Rust would have imposed a re-tooling cost; OCaml does not. Were the team
Rust-strong, this axis would have weighed the other way and the decision
might have gone differently even with a real Phase 4.

Both axes resolved in OCaml's favor. The decision was therefore not close.

### 1.2 What this trades

The Lean plugin pays a C-FFI cost it would not have paid under Rust.
Rust's C ABI is cleaner than OCaml's, and Lean has a clean C interface;
the Rust scenario would have offered slightly less friction at the Lean
boundary. Under OCaml, Lean integration goes through a C shim that
marshals IR documents as serialized data (JSON in development, CBOR in
production) across the boundary, with `Callback.register` and
`caml_callback` handling the function-call mechanics. This is a known
engineering pattern, not a research project, but it is real work.

We also trade some ecosystem breadth. Rust's general-purpose library
ecosystem is broader than OCaml's, particularly for HTTP clients,
async runtimes, and binary serialization. None of the gaps are
disqualifying, but each will surface as an extra decision or extra
glue code at some point in implementation.

The trades are accepted. The Phase 4 win and the team-rampup avoidance
are individually larger than either trade; together they are decisive.

### 1.3 What was *not* considered

This decision does not address:

- Funding or sustainability of the OCaml ecosystem long-term.
- Future language migrations if OCaml's position in the proof
  engineering community changes substantially.
- Performance comparisons under specific workloads — both Rust and
  OCaml comfortably meet the latency budgets in the roadmap; no
  performance-driven choice was made.

---

## 2. Changes to the roadmap

### 2.1 Phase 0 (Foundations)

**Original recommendation (roadmap v1.0, §3):**
> Rust for the shared library, with explicit FFI for Lean (via Lean's C
> interface) and for OCaml (via standard FFI).

**Revised recommendation:**
> OCaml for the shared library, with direct linking for the Rocq plugin
> and a C-FFI shim for the Lean plugin. The C shim marshals IR documents
> across the boundary as serialized data (JSON during development;
> CBOR in production for performance at the FFI boundary).

**Async runtime: `lwt`.** Under Rust, the async runtime would have been
tokio without deliberation. Under OCaml, the choice was between `lwt`
and Janestreet's `async`. Decision: **`lwt`**, on grounds of lighter
dependency surface, broader community familiarity, and compatibility
with `cohttp-lwt-unix` (the HTTP client needed for the LLM-as-backend
adapter in Phase 3). Janestreet's `async` was rejected because the
Janestreet ecosystem coupling is not justified by our needs. The
decision is locked at the start of Phase 0; switching mid-implementation
is off the table absent a critical ecosystem failure (see §5).

> **Recorded reconsideration (Phase 3, concurrent dispatch).** Per
> §5's "do not silently revisit … the audit trail matters"
> discipline, this is an explicit, narrow amendment — not a
> reversal. The concurrent-dispatch deliverable (roadmap §Phase 3
> #5) races several **blocking solver subprocesses** and returns
> the first/highest-tier result. The adapters' `run_solver`
> already does blocking subprocess I/O
> (`Unix.open_process_args_full` + `Unix.select`), and OCaml's
> `Unix` blocking primitives release the runtime lock, so the
> right tool for *this* job is the stdlib **`Thread`** library:
> one thread per eligible adapter, a mutex-guarded mailbox the
> calling thread polls (the grace window is a wall-clock deadline
> the poller checks — no separate timer thread), and every spawned
> thread is joined before the call returns. The join discipline is
> not optional: the driver runs inside the FFI-embedded OCaml
> runtime, where a thread that outlives the synchronous dispatch
> call corrupts the host process's exit path (this surfaced as a
> `roundtripTest` CI regression and was fixed by joining, not by
> reverting the approach). It reuses every adapter's existing
> blocking code unchanged and touches only `dispatch.ml`.
> Rewriting all four adapters onto `Lwt_process` to honor the
> `lwt` lock here would be a large, higher-risk change for no
> behavioural gain on subprocess-bound work.
>
> **Scope of this amendment:** `Thread` is adopted *only* for
> parallel subprocess dispatch. `lwt` remains the locked async
> runtime for the genuinely-async work it was chosen for — the
> LLM-as-backend adapter's HTTP client (`cohttp-lwt-unix`) and any
> future async I/O. The two coexist: `Thread` for CPU/subprocess
> fan-out, `lwt` for network concurrency. No `lwt` code is removed
> (none exists yet); the Phase-0 lock is amended, not voided.
> This note is the recorded decision §5 requires.

> **Recorded reconsideration (Phase 3, LLM-as-backend transport).**
> Same §5 discipline; same shape as the concurrent-dispatch note.
> §2.1 named `cohttp-lwt-unix` as a reason `lwt` was chosen — the
> HTTP client for the LLM-as-backend adapter (roadmap §Phase 3
> #3). On building it, the HTTP transport is instead a **`curl`
> subprocess**: it adds zero OCaml dependencies (vs. the
> `cohttp`/`tls`/`x509`/`conduit`/`ca-certs` tree), reuses the
> exact subprocess pattern every solver adapter already uses
> (`open_process_args_full` + drain + parse), delegates TLS /
> proxy / cert handling to the system, and is trivially mocked by
> a local socket in tests — material for the "no LLM in CI"
> policy (roadmap §11). The FFI boundary is synchronous and the
> adapter makes a single blocking request, so `lwt`'s concurrency
> would be unused here regardless.
>
> **Scope:** `curl` is the transport for the LLM adapter only.
> `lwt` is *not* removed from the locked set — it remains the
> designated runtime for any genuinely-async work that later
> needs it; should that materialize, this note does not pre-empt
> revisiting `cohttp-lwt-unix` for it specifically. The API key
> is passed via `curl -K -` (config on stdin), never argv, so it
> is not exposed to `ps`. This note is the recorded decision §5
> requires.

**New Phase 0 deliverable: FFI round-trip spike (week 1–2).** Before
committing implementation effort downstream of the C-FFI assumption,
build the smallest possible end-to-end round trip: a non-trivial IR
document serialized in Lean, marshaled through the C shim into OCaml,
deserialized into the OCaml IR representation, re-serialized, returned
across the shim, and verified equal in Lean. The spike must also
exercise error propagation (an OCaml-side exception surfaces as an
actionable diagnostic in Lean) and rough GC stress (sustained call rate
without memory growth). Outcomes: (a) confirm the FFI surface area
assumed in §1.2 is buildable; (b) calibrate the Phase 1 Lean-plugin
estimate in §2.2 against measured serialization-marshaling cost;
(c) provide the first off-ramp from the OCaml decision before further
investment is sunk. If the spike takes more than two weeks or surfaces
architectural surprises, the language choice should be reconsidered
(see §5 condition 6).

**Spike outcome (recorded post-completion).** The spike landed
end-to-end on all three IR fixtures with parse-and-compare equality,
typed error propagation, and stable memory across 10⁵ iterations.
Measured per-call marshaling cost is ~54 µs on x86-64 Linux — small
enough that it does not move the §2.2 +20–30% estimate. Full
calibration table and toolchain notes live in
`sdk/FFI_CONVENTIONS.md` ("Phase-0 spike outcome"). §5 condition 6
did not trigger.

**New Phase 0 deliverable: distribution bundle scaffold for Lean.**
Under Rust, the shared library would have been a single static binary
with no runtime requirements on the Lean side. Under OCaml, the Lean
plugin must ship the OCaml runtime alongside its own code. The
distribution bundle scaffold establishes the per-platform build
pipeline before any of the Lean plugin code that depends on it.

**Supported platforms (v1):** macOS x86, macOS ARM, Linux x86, Linux
ARM. *(Audit #18 amendment, per §5: macOS-x86 has no CI coverage —
the `macos-13` (Intel) matrix entry was dropped in commit `39ffd0f`
after the GitHub Actions Intel-macOS runner pool stopped attaching;
`sdk-cross-platform` exercises macOS-aarch64 + Linux-aarch64 only,
with Linux-x86 via the primary `sdk` job. macOS-x86 remains a stated
v1 support intent but is currently unverified by CI; re-add the
runner if it becomes a real deployment target. Recorded here rather
than silently revised.)* **Windows is deferred to v2** unless implementation experience
shows the OCaml-on-Windows packaging story is materially better than
the current state of the art; the Phase 5 estimate in §2.6 assumes the
v1 platform list. If Windows is added back to v1, the Phase 5 estimate
should grow by at least one additional month.

This is a Phase 0 deliverable, not Phase 5 polish; getting it wrong
forces re-work later.

### 2.2 Phase 1 (Skeleton)

**New risk: FFI debugging ergonomics for Lean side. Severity: MED.**

The C-FFI boundary is where most subtle bugs will hide during early
Lean plugin development. Stack traces span language boundaries; GC
interactions can produce non-deterministic failures; marshaling errors
manifest as type mismatches at the OCaml side rather than at the Lean
call site. Mitigation: invest in an FFI test harness early in Phase 1
(round-trip serialization across the boundary, GC stress tests, error
propagation tests). Treat the first few FFI bugs as paradigmatic — fix
them and document the patterns rather than just fixing them.

**Lean plugin effort estimate: +20–30%** versus the Rust scenario,
absorbed in marshaling code and FFI debugging. **This number is a
preliminary engineering judgment, not measured.** It must be recalibrated
against the FFI round-trip spike's actual cost (§2.1) at Phase 0 exit;
if measured cost exceeds 40%, Phase 1 either grows by a month or sheds
goal coverage. Phase 1's three-month duration is held only against the
preliminary estimate; in either case, the final number affects internal
allocation — the Lean plugin's serializer should expect to consume a
meaningfully larger share of the phase than originally planned.

### 2.3 Phase 2 (Core)

**Net effect: slightly faster than the Rust scenario.**

OCaml's pattern matching maps onto the shell-calculus operations
(see spec §4.4) more directly than Rust's enum-and-match patterns. The
IR rewriter passes (especially `quotient_elimination`, where structural
manipulation is the bulk of the work) are roughly 10–15% less code in
OCaml than they would have been in Rust. The savings are real but
small; Phase 2's duration estimate (4 months) is unchanged.

**The HIGH risk on Alethe-to-Lean replayer scope is unchanged.** The
language of the replayer's host (OCaml) doesn't materially affect how
much Alethe coverage we get for how much engineering effort. This risk
is about the proof-replay problem itself, not its implementation
substrate.

**Property-based testing for inversion correctness.** OCaml's `qcheck`
library is a strong fit for the HIGH risk on quotient-elimination
inversion correctness flagged in roadmap v1.0 §5. Round-trip property
tests (original goal → rewritten → certificate → lifted = original)
match `qcheck`'s shrinking machinery cleanly; the OCaml decision makes
this mitigation slightly easier to set up than under Rust (where
`proptest` plays an analogous role). This is a small positive, not
load-bearing.

### 2.4 Phase 3 (Breadth)

**Async story is concrete.** The Vampire adapter and the LLM-as-backend
adapter both require concurrency for parallel speculative dispatch and
for HTTP client operations respectively. With `lwt` as the runtime
(per Phase 0 decision), this is straightforward. The OCaml HTTP client
ecosystem (`cohttp-lwt-unix` or similar) is mature enough for v1
needs.

No risk-register changes for Phase 3.

#### 2.4.1 Phase 3 progress (post-completion notes)

**M1 shipped: Vampire adapter + TPTP serializer + Tier-0
dispatch.** `sdk/lib/tptp.ml` serializes an `Ir.t` to TPTP, with
the dialect chosen by `logic_classification.order` (FOF for
first-order, THF for higher-order — the "Vampire-HOL" path the
exit criterion names). `sdk/lib/adapter_vampire.ml` mirrors the
z3 adapter shape (no-shell subprocess, SZS-status protocol) and
mints a Tier-0 oracle cert with `axiomatization` refinement
records; `examples/manifest-vampire.json` advertises FOL/HOL/UF
(deliberately *not* the arithmetic fragments, so capability
matching keeps routing LIA/LRA goals to the SMT adapters).
Validated end-to-end against real Vampire 5.0.1 (pinned +
SHA-256-checked in the `sdk` CI job, audit-M8 discipline).

**Two scope realities surfaced during M1, recorded here per §5's
"the audit trail matters" discipline — they were *not* named in
the original §2.4 and they reshape the remaining Phase-3
envelope:**

1. **The Tier-3 verifier is OCaml-side and large.** The Alethe
   precedent (`tier3_alethe.ml`) is ~1.6 kLOC with ~22 rule
   checkers; the home system only consumes the verdict and closes
   via a verdict-gated axiom-free closer (audit H1). The TSTP
   replayer (M2) mirrors that module against a proof format the
   original §2.4 risk list called out as MED ("succeed in Vampire
   but fail to replay"). M1 deliberately stops at Tier 0 so the
   heterogeneous-dispatch claim is validated before that cost is
   sunk.

2. **The Lean reifier is LIA-only.** `examples/example2-
   function-composition.json` is a hand-written spec fixture, not
   something `proof_broker` currently produces — closing it
   axiom-free (the roadmap exit criterion) additionally requires
   a higher-order reifier extension in Lean plus an HOL closer,
   which the original Phase-3 plan did not scope. This is tracked
   as M3 and is the bulk of the remaining calendar.

**Slack accounting (cf. §2.7).** No new slack; M1's effort was
the well-bounded SDK-side foundation. The M2/M3 split makes the
previously-implicit Lean-side cost explicit rather than absorbing
it silently — calendar-neutral, slack-negative continues to hold.

**M2 shipped: TSTP parser + Tier-3 provenance verifier +
fail-closed minting.** `sdk/lib/tptp_proof.ml` parses Vampire's
`--proof tptp` derivation (statement splitter + a shallow
annotation-term parser; formula bodies kept verbatim — depth-
bounded and `Stack_overflow`-backstopped like `alethe.ml`).
`sdk/lib/tier3_tptp.ml` is the soundness-critical piece, and the
honest scope boundary is recorded here per §5: it is **not** a
per-step re-derivation like the Alethe Tier-3 verifier. Vampire
emits superposition/resolution steps without the unifier, so
re-deriving them is the proof-search problem itself (the original
§2.4 MED risk). Instead the verifier checks the property that is
soundly and cheaply checkable — the TSTP analogue of
`Tier3_alethe.validate_top_level_assumes`: every leaf reachable
from the `$false` sink is one of our input formulas (matched by
the `--output_axiom_names` name, never a prover-`introduced`
definition nor a `file` leaf we did not send), the conjecture is
consumed only via a negation inference, the parent DAG is
well-formed, and every rule is in a reviewed allowlist.

`Verified_provenance` is therefore a sound **filter**, not a
kernel check: it never accepts a derivation that smuggled an
axiom, skipped the goal, or failed to reach `$false`, but it does
not assert each inference was re-checked. In the H1 model the M3
home-system closer re-proves the goal gated on this verdict and
**is** the kernel check; the cert advertises the boundary
explicitly via a `provenance_verified_only` dialect-feature tag
and a prose `trace_annotations` line, so no consumer is misled.
The Vampire adapter mints Tier-3 only on `Verified_provenance`
(one parse feeds gate and payload) and otherwise falls back to
the Tier-0 oracle — the same fail-closed discipline cvc5's
adapter uses. Validated end-to-end against real Vampire 5.0.1:
the worked FOF goal's derivation passes the gate and mints a
`tstp-fof` Tier-3 cert; `examples/cert-example4-tier3-tptp.json`
is the schema/cross-doc fixture.

**M3 shipped: Lean higher-order reifier + verdict-gated HOL
closer — the Phase-3 exit criterion is met.** The core (Mathlib-
free) Lean reifier was extended to the HO/FOL fragment:
parenthesized higher-order arrow types (`(Nat->Nat)->Prop`),
bare type constants as uninterpreted base sorts, `∀`/`→`
(`.forall_`/`.implies`), and applied global constants (e.g.
`Function.comp`) collected as IR `freeVars` with their
monomorphic types. A higher-order goal sets `order =
higher_order` / `firstOrderFragment = none`, which makes
`capability_match` skip the first-order SMT adapters and route
dispatch to Vampire (THF). The OCaml `Verifier.verify` now
dispatches `tstp-fof`/`tstp-thf` Tier-3 certs to `Tier3_tptp`,
surfacing the honest `verified_tier3_provenance` reason (its own
variant, not conflated with Alethe's per-step `verified_tier3`).
The bridge closer gained a `holCloser` `ReifierExt` slot;
`ProofBrokerMathlib` registers an `aesop`-based closer. Gating
follows the H1 contract exactly: the re-verified cert decides
*whether* to invoke the closer; `aesop` emits the kernel proof
term, so the cert never enters the trust footprint.

`Test/TacticMathlib.lean`'s `hol_function_composition_axiom_free`
is `examples/example2-function-composition.json`'s goal closed
`by proof_broker`, end-to-end through real Vampire: reify → THF
dispatch → SZS Theorem → Tier-3 `tstp-thf` mint → provenance
re-verify → `aesop`. Observed trust footprint: `[propext]` —
strictly inside the documented core ceiling (pinned in
`tools/axiom_allowlist.json`); zero `sorryAx`. The roadmap
§Phase-3 exit criterion ("a goal involving function composition
… succeeds via Vampire-HOL") is satisfied. With no
`ProofBrokerMathlib` import the core lib `throwError`s on a
certified HO goal rather than admit — identical discipline to
the LRA path.

**Slack accounting (cf. §2.7), final.** M3 was the predicted
large Lean-side slice; it landed without new calendar but it
*was* the previously-implicit cost the M1 note made explicit.
Calendar-neutral, slack-negative holds; Phase 3's three core
deliverables (Vampire adapter, TSTP Tier-3 verifier, the
heterogeneous-dispatch + HO reach this validates) are complete.
The remaining roadmap Phase-3 items (LLM-as-backend adapter,
LLM-assisted reconstruction, concurrent dispatch) are untouched
and tracked separately.

**Concurrent dispatch shipped.** `Dispatch.run_parallel`
(roadmap §Phase 3 #5): one `Thread` per capability-eligible
adapter, mutex/condition mailbox, first-valid-wins with a grace
window that prefers the highest `cert.tier`; latency-first at
`grace_window_ms = 0`. The `Thread`-vs-`lwt` reconsideration is
recorded in §2.1. Honest v1 cancellation (stop-waiting; orphans
bounded by their per-call solver timeout) is documented in the
driver, not silently approximated. FFI `dispatch_broker` uses it
(2 s grace when `prefer_higher_tier`, else 0); C ABI unchanged.

**LLM-as-backend adapter shipped (adapter-only slice).**
`Adapter_llm` (roadmap §Phase 3 #3): env-configured
(`PROOF_BROKER_LLM_ENDPOINT/_API_KEY/_MODEL`), fail-closed when
unset, renders the IR as Lean surface syntax, prompts an
OpenAI-chat-shaped endpoint over a **`curl` subprocess** (§2.1
records the transport reconsideration; the key travels via
`curl -K -`, never argv), and mints a Tier-3
`lean-tactic-script` cert. Because an LLM is an untrusted
oracle, `Verifier.verify` returns the new
`Tier3_replay_deferred` reason — envelope-ok, explicitly *not* a
soundness verdict; the cert carries an
`unverified_until_kernel_replay` tag and an honest annotation.
Tested without any network (mock local endpoint, forked
one-shot responder, `curl`-gated) per the §11 "no LLM in CI"
policy.

**LLM-script replay closer shipped (home-side completion of
§Phase 3 #3).** `ProofBroker.Tactic.replayLlmScriptOrFail`:
`closeOrFail` routes a `lean-tactic-script` cert whose verify
reason is `tier3ReplayDeferred` *past* the fragment-keyed closers
to a dedicated path that elaborates the script as `(by …)`
against the goal via `exact`, requires the goal actually closed,
then collects the **replayed proof term's** transitive axioms
(`collectAxioms` over `getUsedConstantsAsSet`) and accepts iff
they are a subset of `{propext, Classical.choice, Quot.sound}` —
the same classical ceiling every other closer already uses. A
hallucinated `sorry`/`admit` (⇒ `sorryAx`), `native_decide`
(⇒ `Lean.ofReduceBool`, compiler trust, not kernel-checked), or
any bespoke axiom is a tactic failure with the goal left OPEN,
never an admitted theorem (audit H1) — so the untrusted oracle
can never widen the trust base. CI exercises this with no network
or live model via a test-only `llm_replay_test "<script>"`
tactic that drives the identical closer with the string as the
cert payload (`Test/Tactic.lean`: a positive `omega` close plus
`sorry`/`native_decide`/non-closing/unparsable rejections, the
positive theorem pinned in `tools/axiom_allowlist.json`). With
this, the §Phase-3 exit criterion for the LLM path is reachable
end-to-end (live endpoint configured ⇒ adapter mints the cert ⇒
this closer kernel-checks it). **Deferred (separate slice):**
roadmap deliverable #4 (LLM-assisted reconstruction of
un-replayable Tier-3 traces).

**LLM-assisted Tier-3 reconstruction shipped (§Phase 3 #4).**
`sdk/lib/llm_reconstruct.ml` adds `Llm_reconstruct.translate (ir,
cert)` which reuses `Adapter_llm`'s curl transport, body builder,
and response extractor (no new dependencies, same `curl -K -`
secret discipline) but ships a different user prompt: the IR as
a Lean theorem skeleton followed by the original Tier-3 trace
verbatim, with the LLM asked to translate the trace into a Lean
tactic script. The translation is exposed via a new FFI method
`llm_translate_trace` (mirror of `verify_certificate`) and a
`runLlmTranslateTrace` Bridge call on the Lean side.
`ProofBroker.Tactic.closeOrFail` now wraps the primary
fragment-keyed closer chain in a try/catch: on any primary
failure with a Tier-3 cert in hand (and `trace_format` not
already `lean-tactic-script`), the reconstruction translator is
invoked and the candidate script is routed through the SAME
audit-H1 gate (`replayReconstructedScript` → `replayLlmScriptOrFail`,
kernel replay + axiom-footprint subset check against `{propext,
Classical.choice, Quot.sound}`). A successful reconstruction
emits a `logInfo` line ("closed via LLM Tier-3 reconstruction
(<format> trace → Lean tactic script, kernel-checked, audit
H1)") so the audit trail is visible in the build output. The
fallback is silent when `PROOF_BROKER_LLM_ENDPOINT` is unset (the
SDK returns a structured `llm_error` envelope; the primary
failure is re-raised) — i.e., CI without an LLM endpoint behaves
exactly as if this branch were not wired in. SDK tests:
prompt-rendering, non-Tier3 rejection, fail-closed, and an
end-to-end mock-HTTP-endpoint translate (mirroring
`test_adapter_llm`'s forked one-shot responder pattern). Lean
tests: a positive `omega`-translation closes axiom-free
(`llm_reconstruct_axiom_free` pinned in
`tools/axiom_allowlist.json`), and `sorry`/`native_decide`/
non-closing translations are rejected — exercised via a test-only
`llm_reconstruct_test "<format>" "<script>"` tactic that feeds
the candidate script directly into the production-path
`replayReconstructedScript`, bypassing the FFI translate call
(no network needed; the audit gate is identical to the live path).

With these, **Phase 3 (Breadth) is structurally complete on the
Lean side**: every roadmap deliverable (Vampire adapter +
TPTP→Lean replayer + HOL closer; LLM-as-backend adapter and
home-side replay closer; concurrent dispatch; LLM-assisted
Tier-3 reconstruction; refined capability matching) has landed.

**Phase 3 Rocq parity shipped in four milestones** (PRs #37/#38/
#39, May 2026 — see `RETROSPECTIVES/phase-3-rocq-parity.md`).
Because the SDK is shared (adapters, dispatch driver, TSTP and
Alethe verifiers, `Llm_reconstruct`), Rocq parity was almost
entirely plugin-side wiring plus one round of SDK bridge-
awareness:

* **M1** added the Rocq HO reifier (`Prod`→`Forall`/`Implies`,
  parenthesized arrow domains, `Eq` at function type, HOL
  fragment detection); a fragment-keyed HOL/FOL closer hook
  (`proof_broker_hol_closer` Ltac, default fails with a clear
  directive); the `ProofBrokerHammer` opt-in package
  (`coq-hammer-tactics`-backed `hauto`, mirror of
  `ProofBrokerMathlib`'s aesop opt-in); and the worked-example
  test `pb_hol_function_composition_axiom_free` (closed
  axiom-free by `hauto` under the Tier-3 TSTP provenance gate).

* **M2** added a Rocq-side LLM-replay closer
  (`rocq-bridge/src/llm_replay.ml`) using Rocq's kernel
  `Assumptions` API for the audit-H1 axiom-footprint gate — the
  same API `Print Assumptions` calls internally. Sentinel
  `VarRef` "owner" + dummy `indirect_accessor` (safe under
  `add_opaque:false`) gave us the same semantic gate Lean's
  `collectAxioms` provides, in ~60 lines of plugin code.

* **M3** made the SDK's `Adapter_llm` and `Llm_reconstruct`
  bridge-aware: a new `dialect` record (system_prompt,
  render_prompt, ty, term, trace_format, …) dispatched by
  `ir.source_system.name`. Lean home systems → Lean syntax +
  `lean-tactic-script` certs (preserved); Rocq home systems →
  Rocq Stdlib syntax + Ltac + `rocq-tactic-script` certs.
  `Verifier.verify` extended to recognize both formats →
  `Tier3_replay_deferred`. The reconstruction-fallback
  `Proofview.tclORELSE` wrap on Rocq's `close_or_fail` mirrors
  Lean's `closeOrFailPrimary`+`closeOrFail` split from PR #36:
  primary failure triggers a lazy `Llm_reconstruct.translate`
  call and routes the candidate through the same audit-H1
  replay gate from M2 (no separate trust path).

* **M4** is this `delta.md` sync and the README update; the
  `fragment_of_logic` consolidation flagged in
  `RETROSPECTIVES/phase-4.md` had already shipped during an
  earlier audit pass.

**Phase 3 (Breadth) is now structurally complete on both bridges.**
The architectural payoff predicted in §1.1 ("the IR is genuinely
cross-system or accidentally Lean-shaped") materialized:
every shared SDK piece worked on the Rocq side unchanged, and
the only cross-bridge surface that needed bridge-awareness was
the LLM prompt rendering, which consolidated into a single
`dialect` record in `Adapter_llm`. Remaining Phase-3 work is
polish (latency tuning, prompt iteration, additional adapters,
BV/UF reach on Rocq pending a Stdlib BitVec library) tracked
in the per-phase retrospectives rather than in this delta.

### 2.5 Phase 4 (Probe)

**This is where the language choice pays off.**

The Rocq plugin and the shared library are both OCaml. The Rocq probe
involves no FFI marshaling, no C shim, no GC interaction debugging —
though dune workspace setup, OCaml version compatibility coordination
between the shared library and Rocq's own OCaml version, and
shared-runtime considerations remain real friction. They are well
within OCaml-ecosystem norms but should not be hand-waved as "free."
The Phase 4 effort drops from approximately 2 months to approximately
1 month.

**Risk register changes:**

- Phase 4 "Plugin cost" risk: downgraded from MED to LOW. The Rocq
  plugin's engineering effort is comparable to the Lean plugin's
  serializer alone, since there is no FFI tax.
- Phase 4 "Schema fit" risk: **unchanged at HIGH.** This is the central
  point. The language choice does not affect whether the IR has
  Rocq-shaped gaps; it only affects how cheap it is to find out. The
  reason for the language choice was to make the validation efficient,
  not to alter what we'll learn.

**Calendar effect.** Saving 1 month in Phase 4 enables either: (a)
extending Phase 5 to absorb the new Phase 5 risks (see §2.6); or (b)
allocating buffer to the Phase 1 spec revision checkpoint, which has
been chronically under-budgeted in similar projects. Recommendation: (b),
unless Phase 5 is tracking ahead by Phase 4 exit.

#### 2.5.1 Phase 4 outcome (post-completion notes)

Phase 4 has shipped end-to-end. `rocq-bridge/` hosts a Rocq plugin
that direct-links the SDK, reifies LIA + LRA goals into the same
`Ir.t` Lean produces, dispatches through the same broker, verifies
the same way, and closes via cert-gated `lia` / `lra` (Phase 4.5)
or term-mode reconstruction (Phase 4.6). The plugin-cost prediction
held — total Rocq-side engineering effort came in close to the
1-month estimate, dominated by Rocq plugin API spelunking rather
than IR work. Specific friction surfaced and recorded in
`RETROSPECTIVES/phase-4.md`: the `whd_all`-vs-folded-definition trap
(twice — `Z.ge` and `IZR`), `Global.env`-during-init prohibition,
and dune's `(using rocq …)` extension being announced but
unimplemented.

The schema-fit prediction also held — at LOW in practice, not the
HIGH the original §2.5 anticipated. The IR survived the second
source language without restructuring; the typeclass-flavored shell
vocabulary (`HAdd.hAdd`, `LE.le`, …) ports verbatim from Lean to
Rocq's `Z` arithmetic. The `examples/example1-lia-typeclass.json`
fixture round-trips through both bridges identically.

What the probe surfaced instead is a different class of risk that
the original §2.5 didn't name: **theory-portability asymmetry driven
by source-language standard libraries.** Lean's `BitVec n` is in
core with full typeclass-overloaded arithmetic + `DecidableEq`,
making BV reach a 30-minute reifier extension on the Lean side that
closes axiom-free via `decide`. Rocq Stdlib's `Bvector` is
deprecated, has only bitwise ops, and lacks any width-indexed BV
type — so the Rocq BV slice was deferred. The asymmetry isn't about
the IR; it's about what each home system's standard library
provides. UF reach has the same shape: shipped on Lean
(closes axiom-free via `subst_eqs; rfl`), pending on Rocq.

**Carried scope.** Three follow-on pieces went in alongside the
core probe and weren't in the original §2.5 envelope:

* **Term-mode Tier 1 Farkas reconstruction** (Rocq):
  `proof_broker_term` builds an explicit Rocq proof term from a
  Tier 1 Farkas witness's coefficients via a `farkas_le_2` helper
  + `ring`. The cert IS the proof — no `lia` along this path. The
  Lean side has the same play queued but not yet wired.
* **AxiomCheck CI gate** (`tools/check_axioms.py`): parses build
  output for Lean's `#print axioms` and Rocq's `Print Assumptions`
  blocks, fails CI if any allowlisted theorem grows beyond
  `tools/axiom_allowlist.json`'s ceiling. Currently 6 Lean + 11
  Rocq theorems pinned, all axiom-free or carrying only documented
  core axioms.
  *(Audit #18: "6 Lean + 11 Rocq" is the Phase-4-close snapshot. The
  count has since grown — see `tools/axiom_allowlist.json` for the
  live ceiling; README §Status carries the current figure. This
  §2.5.1 line is intentionally left as the frozen historical record
  per §5's "the audit trail matters" discipline.)*
* **rocq-bridge CI job**: standalone CI lane that installs
  `rocq-runtime` + cvc5 + z3 and runs the Rocq build under the
  same trust-footprint gate.

These shifted what would have been Phase 5 work earlier — the
buffer-to-Phase-5 calendar effect noted above is not realized; the
saved Phase 4 month was spent on the carried-scope items rather
than added to slack.

**Risk-register update for §2.7's slack accounting:** the
calendar-neutral / slack-negative summary still holds — we have not
gained slack relative to the original v1.0 plan. The shape of the
slack-spending shifted (CI / trust-footprint gating absorbed it
instead of cross-platform packaging), but the total isn't different.

### 2.6 Phase 5 (Polish)

**Update (post-completion): Phase 5 scope shifted to term-mode parity.**
The Phase 4 retrospective carried forward term-mode reconstruction —
translating Farkas / case-split witnesses directly into Lean / Rocq
proof terms rather than routing verified certs to `lia` / `lra` /
`omega` / `linarith` — as the next direction. That carried-forward
work expanded into a full term-mode parity push that consumed the
Phase 5 calendar slot: end-to-end Tier 1 + Tier 2 reach across LIA +
LRA, the full inequality vocabulary including negations, equality
hypotheses with signed coefficients, rational coefficient support,
arity-N premises and arity-N case-split disjunctions. See
`RETROSPECTIVES/phase-5.md` for the post-mortem. The cross-platform
distribution work originally budgeted here moves to Phase 6.

**Original Phase 5 scope, deferred to Phase 6:** Cross-platform OCaml
runtime distribution for Lean users. Severity: MED.

Lean users typically do not have an OCaml toolchain installed.
The Lean plugin must ship a precompiled bundle including the OCaml
runtime and the shared library, per platform. This is a real packaging
project: per-platform builds, runtime version pinning, signed
distribution for macOS, Windows-specific complications around the
OCaml/Windows ecosystem.

**Mitigation:** the distribution bundle scaffold from Phase 0 is the
foundation. Phase 6 work is to harden it (signing, package manager
integration, update mechanisms). If Phase 0 cuts corners on the
scaffold, Phase 6 inherits a larger problem.

**Phase 5 duration: held to original 3-month estimate** (term-mode
reach + polish landed inside the calendar slot). Phase 6 inherits the
cross-platform distribution work as a fresh 1-month allocation that
wasn't reflected in roadmap v1.0.

### 2.7 Total duration and budget

**Calendar:** unchanged. Phase 4 saves one month, Phase 5 costs one
month, total remains 15 months from Phase 0 start.

**Slack:** reduced. Phase 0 absorbs new deliverables (FFI spike,
distribution bundle scaffold, async-runtime lock, supported-platforms
list) without budget growth. Phase 1 absorbs a preliminary +20–30%
Lean-plugin hit without duration extension. Phase 5's added month is
fully consumed by new packaging work, leaving no buffer for the
dashboard or the Tier 2 demotion contingency. The honest summary is
**calendar-neutral, slack-negative**: every phase except 4 is more
committed than under the Rust scenario, even though the dates on the
wall haven't moved. Resourcing should reflect this.

---

## 3. Cross-phase concerns: additions

### 3.1 FFI testing strategy

Roadmap v1.0 §11 describes test coverage strategy in language-agnostic
terms. The OCaml decision adds a new test category that should be
called out explicitly:

**FFI boundary tests.** Distinct from unit, integration, property, and
regression tests. Specifically:

- **Round-trip marshaling tests.** IR documents serialized in Lean,
  deserialized in OCaml, re-serialized in OCaml, deserialized in Lean,
  must equal the original. Same for certificates and refinement records.
- **GC stress tests.** Repeated FFI calls under memory pressure to
  surface OCaml GC interaction bugs that don't appear in light testing.
- **Error propagation tests.** Errors raised at the OCaml side
  surface as actionable diagnostics on the Lean side, not as opaque
  segfaults or untyped exceptions.
- **Platform compatibility matrix.** Every supported platform builds
  and passes the FFI test suite. CI runs the matrix on every shared
  library change.

This category is owned by the Lean plugin team but has runtime cost
on the shared library. Both teams should be aware of it.

### 3.2 Cache implementation under OCaml's process model

Spec §8.5 envisions an optional shared-cache configuration for team or
CI use. OCaml's single-threaded GC and process model do not naturally
support multi-process shared on-disk caches without additional
engineering — typical patterns (file locking, single-writer-multi-reader
schemes via `lmdb` or similar, or out-of-process cache servers) all
require deliberate design rather than falling out of the language's
standard tooling. **This is a Phase 5 concern, not Phase 0**, but
whoever scopes the cache subsystem should know it's coming. The
project-local cache (Phase 5 default) is unaffected; only the optional
shared cache is implicated, and it may want its own design memo when
implemented.

### 3.3 Versioning policy: addition

Roadmap v1.0 §11.4 covers spec, schema, and registry versioning. The
OCaml decision adds:

**Shared library API versioning.** The OCaml shared library exposes a
public API (entry points called from C-FFI, entry points called from
the Rocq plugin). This API has its own version, distinct from the
spec version. Breaking changes to the API require coordinated updates
to both home-system plugins. Mitigation: the API should be deliberately
narrow — the smallest set of entry points that the home-system plugins
actually need. Treat API surface as cost, not as feature.

---

## 4. Spec revisions required

The spec (v1.0) was written to be language-agnostic and largely
succeeds. Three sections leak language assumptions that should be
revised. These are minor edits, listed here for completeness and for
the spec revision tracker.

### 4.1 Spec §3.1 (Architectural overview, Components)

**Current text** (paraphrased): The IR Rewriter is "implemented as a
shared library callable from any component."

**Revised text:** The IR Rewriter is "implemented as an OCaml library;
the Rocq plugin links it directly, and the Lean plugin invokes it via a
C-FFI shim with serialized-data marshaling. Callable from any
component through one of these two mechanisms."

### 4.2 Spec §9 (Reconstruction layer, per-home-system responsibilities)

The current section discusses serializers and deserializers in
language-neutral terms. A short subsection should be added making the
integration mechanism concrete:

> **Integration mechanism.** The Rocq plugin links the shared library
> directly. The Lean plugin invokes the shared library through a
> C-FFI shim that marshals IR documents and certificates as serialized
> data across the boundary. JSON marshaling is acceptable for v1
> development; CBOR is recommended for production performance at the
> FFI boundary.

### 4.3 Spec Appendix B (Open questions)

The "Binary serialization format" item is currently flagged as deferred
to implementation. **JSON remains the canonical specification format**;
the revision is to promote the *implementation* priority of CBOR support
to a Phase 0/1 deliverable, on grounds that the C-FFI boundary on the
Lean side benefits from a fast binary format. This is a change in
operational priority, not in canonical format. Spec Appendix B should be
updated to reflect this distinction explicitly.

### 4.4 Versioning of these spec revisions

These are minor revisions (no semantic changes to schemas, tier
behavior, or soundness invariants). They should be incorporated into a
spec v1.1 release alongside any other findings from Phase 0 and
Phase 1. They do not require an immediate respin of the spec
document.

---

## 5. Conditions for reconsideration

This decision should be reconsidered if any of the following occur:

1. **The implementing team changes substantially.** If the team becomes
   Rust-strong without retaining OCaml fluency, the rampup cost
   calculation changes. Reconsider before committing further investment.

2. **Phase 4 is materially de-prioritized.** If a future planning
   decision moves Rocq production support from a v2 commitment to a
   maybe-someday item, the primary motivation for OCaml weakens.
   Reconsider whether to migrate the shared library.

3. **The OCaml ecosystem fails to meet a critical need.** Specifically:
   if the chosen async runtime, the HTTP client, or the binary
   serialization library cannot meet performance or reliability
   requirements that emerge in implementation, the language choice may
   need to be revisited.

4. **Phase 1 or Phase 4 surfaces architectural changes that disrupt
   FFI assumptions.** If the spec revision following Phase 1 changes
   the IR's structure substantially, the FFI surface area may grow
   beyond what was budgeted; if Phase 4 reveals that direct linking is
   not actually faster than the Rust scenario would have been, the
   primary justification weakens.

5. **Lean compiler ABI churn.** Lean 4 is still evolving rapidly. A
   future Lean release that breaks the C-ABI assumptions our shim
   relies on (calling-convention changes, runtime-integration shifts,
   or changes to the `Callback`-style mechanisms on the Lean side)
   would force re-engineering of the FFI boundary. If this happens
   during v1, evaluate whether OCaml + C-shim remains the best answer
   or whether the disruption is large enough to justify migrating the
   shared library to a different language altogether.

6. **The Phase-0 FFI round-trip spike (§2.1) takes substantially
   longer than two weeks or reveals architectural surprises.** This is
   the proactive off-ramp: the spike is the first place this decision
   meets reality, and a bad result there is the cheapest possible
   reconsideration trigger. Specifically: marshaling cost above the
   40% threshold cited in §2.2, GC interaction bugs that don't yield
   to standard mitigations, or platform compatibility surprises
   should each prompt a written reconsideration rather than a quiet
   adjustment.

In any of these cases, this delta document should be amended (or
superseded) with an explicit reconsideration. Do not silently revisit
the language choice; the audit trail matters.

### 5.1 Reconsideration record — condition 5 tripped (2026-08-30, R0.5)

**Trigger.** Lean toolchain bump `v4.30.0-rc2` → `v4.32.0` (Mathlib
`v4.32.0`), forced by the downstream consumer: a Lake workspace has one
toolchain and one Mathlib chosen by the root project, and the R4 demo
project pins `v4.32.0`, so the bridge must compile there.

**What broke.** Not the C shim, not the OCaml boundary: the Lean-side
*dynlib plumbing* around precompiled modules, i.e. exactly the
`lakefile.lean` block at lines 100–125 that condition 5 warned about.
Under Lean 4.30 the `ProofBrokerMathlib` lib was `precompileModules :=
true`, which made Lake build Mathlib's shared library and load it into
the elaborator; that load needed `libLake_shared.so`, and because
Lake's `LD_LIBRARY_PATH` augmentation did not reach the elaborator on
every system the lakefile computed an absolute
`--load-dynlib=$LEAN_SYSROOT/lib/lean/libLake_shared.so` at eval time
(`libLakeSharedDynlibArg`) and added it to every Mathlib-using lib.
Under Lean 4.32 / Lake 5.0 the mechanism changed again: Lake no longer
passes per-import `--load-dynlib` arguments but hands the module a
setup file listing the library `.so`s to load as plugins, topologically
ordered — and loading `libmathlib_Mathlib.so` then fails with
`symbol lookup error: … undefined symbol:
initialize_proofwidgets_ProofWidgets_Component_RefreshComponent`
(the library `.so`s are not linked against each other on Linux, and
the plugin loader does not expose an earlier library's symbols to a
later one's lazy binding). The FFI-bearing core `ProofBroker` lib,
`Test.Tactic` and `roundtripTest` built unchanged; only
`ProofBrokerMathlib.TermMode` failed.

**What changed.** `ProofBrokerMathlib` is no longer precompiled
(`precompileModules := false`) and the `libLake_shared.so` workaround
is deleted. Nothing in that lib needs native code — its `initialize`
registration of the `Real` reifier and the `linarith` / `aesop` closers
runs in the interpreter, and the `@[extern]` FFI surface lives in the
still-precompiled core lib. Consequences, as dated measurements on the
R0.5 tree (`dacae65`, rebased unchanged as `13cf414`; Lean v4.32.0,
Mathlib cache fetched; the job count is a property of the build state,
not of the tree): `lake build` schedules 878 jobs (incremental `lake
build` at `dacae65`, 2026-08-30; 885 from `lake clean` on the same
tree) instead of 17,382 (`lake build` with the Mathlib precompile, same
day — the ~17k Mathlib `.c.o` compiles were the bulk of the lean-bridge
CI job, 15m09 on the last green `main` run, `0a5ae40`, 2026-06-19); the
trust gate is unchanged — `check_axioms.py --bridge lean`: every
allowlisted theorem (count in the README status table) within ceiling,
`hol_function_composition_axiom_free` at `[propext]` through live
Vampire.

**Verdict on condition 5.** The disruption is real but confined to
Lake configuration; the C-ABI assumptions of the shim
(`pb_lean_call`, the string-envelope calling convention, `-l:proof_broker_ffi.so`
+ `-rpath` + `--allow-shlib-undefined`) survived 4.30 → 4.32 intact.
OCaml + C-shim remains the answer; what is retired is the idea that the
Mathlib-flavored lib should be precompiled at all. Standing rule from
this record: a Lean bump is a toolchain-refresh task with its own PR,
and the first thing it re-validates is the dynlib block, not the shim.

### 5.2 Decision record — Tier-3 mint-gate reach for `hole` (2026-08-31, R1.2)

**Question** (roadmap R1.2). cvc5 wraps its theory-rewrite family in
`hole` / `rare_rewrite` steps; the mint gate's `check_hole` verified
only a narrow equality-rewrite set, so half the corpus traces could
never become Tier-3 certs on the live path. Either widen the checker
to what the walkers actually discharge, or make the gate name-based
for `hole`/`rare_rewrite` and record in the cert's
`trace_dialect_features` that leaf re-derivation is home-side.

**Decision: stay check-based; no name-based bypass.** The whole-proof
verifier (`Tier3_alethe.verify_parsed`) remains the mint gate, and
every `hole` / `rare_rewrite` equality is still verified independently
of its trust tag (the `:args ("TRUST_THEORY_REWRITE" …)` annotation is
never consulted). What widened, each a sound, tag-independent check:

- linearization treats non-arithmetic applications as opaque atoms
  (the standard UF abstraction), unlocking UFLIA;
- comparison evaluation generalizes from constant operands to
  constant operand *differences* (`(< x x) = false`,
  `(= (f y) (f y)) = true`);
- classical Prop normalization: deep double-negation collapse plus
  the exists-duality `(exists B P) = (not (forall B (not P)))`;
- equality-to-bounds: `(= t c) ↔ (and …)` of the two `Le`
  half-spaces, modulo LIA tightening;
- `la_generic` falls back to a standalone Farkas-tautology check when
  its literals match no known input (the step's validity is
  context-free per the Alethe spec; common inside subproofs);
- `resolution` pairs `¬X` with `¬¬X` in either orientation and
  accepts cvc5's chain-resolution duplicate-literal merging (extra
  premise copies of a literal the conclusion retains);
- `subproof` closes accept an empty body clause rendered as the
  literal `false` (both reify to the bottom Prop).

The name-based alternative was rejected: it would have made the gate
vacuous for exactly the rule (168 of 1061 corpus steps are holes)
whose shapes carry the real risk, and nothing forced it — every
corpus hole proved decidable at mint time.

**Measured** (2026-08-31, branch `r1/walker-live-path`, R1.2 commit,
command: `dune runtest sdk`, test `corpus-mintability` in
`test_tier3_alethe`): 16/16 corpus traces verify shape-level against
their goal IRs. Before R1.1, 8/16 failed the rule-NAME gate alone;
after R1.1 closed the name gap, 9/16 still failed shape-level (4 on
unreachable assume validation — UF/quantified hypotheses the
IR-to-Sexp translation could not render — 4 on hole shapes, 1 on a
subproof-internal `la_generic`); each class is now closed and pinned
by unit tests plus the corpus sweep.

---

### 5.3 Decision record — pipeline placement, envelope hashes, identity-trace guard (2026-09-01, R2)

**Question** (roadmap R2). The rewriter had never run on the live
path: both bridges dispatched the reified IR directly, every cert
carried the all-zeros `rewrite_trace_hash` sentinel, and the envelope
addressed the pre-rewrite IR — spec §6.1's cross-document hash
contract was unimplemented wherever it mattered.

**Decision 1 — the pipeline runs inside the SDK dispatch driver.**
`Dispatch.run` / `run_parallel` call `Pipeline.run` on the input IR
(default: prop-simp + definition unfolding configured from the
registry's `always_unfold_for_dispatch` per spec §5.4, not from user
directives), dispatch adapters on the rewritten `final_ir`, and
return `(final_ir, trace)` to the caller. Placing it in the driver —
rather than in each bridge — means no bridge or FFI path can reach an
adapter without a trace, by construction; the single-adapter FFI
method runs the same pipeline. The SDK carries the always-unfold list
as a baked-in constant two-way-pinned to the registry JSON by
`tools/check.py` (no runtime file dependency).

**Decision 2 — spec §6.1 conformance restored.** Adapters take a
required `rewrite_trace_hash` argument (the canonical hash of the
dispatch trace) and mint `dispatch_context_hash` over the IR they
were actually handed — `final_ir`, the post-rewrite document, as
§6.1 specifies. The sentinel is deleted from all eleven mint sites
and `Verifier.envelope_check` rejects it unconditionally
(`trace_hash_sentinel`); with a trace supplied the verifier also
requires `trace.final_ir_hash` to equal the verified IR's hash, so a
cert minted on `final_ir` can never be replayed against the original
goal — the mismatch is structural. Related honesty fixes ride along:
`resources.wall_time_ms` is the measured solver wall clock (was: the
timeout budget), and `resources.memory_peak_kb` becomes optional in
`certificate.schema.json` — nothing measures it, and absence is the
honest encoding, never a fabricated `0`. That schema relaxation is a
v1.1-bound spec delta recorded here.

**Decision 3 — identity-trace guard (R2 soundness rule).** The
term-mode and walker closers consume the cert's content against the
ORIGINAL goal, but the cert now addresses `final_ir`. Until lifting
lands (R3), both bridges gate those closers on
`Trace.is_identity`: every pass skipped/no-op AND equal
per-entry and endpoint hashes (outcome check included so an
apply-then-invert pair can't masquerade as identity). Non-identity
dispatches fall back to the decision-procedure closers on the
original goal — sound regardless, since those closers are the proof
— while the strict entry points (`proof_broker_walker`,
`proof_broker_term`) fail closed with a named guard error. The guard
is removed pass-by-pass in R3 as each inversion lands.

**Measured** (2026-09-01, branch `r2/cert-load-bearing`, command:
full harness per RESUME §3): all four legs green with the pipeline
live — lean 120 allowlisted theorems within ceiling + 37 round-trips,
rocq 134 within ceiling from a clean build, corpus byte-identical,
sdk 29 suites. The guard's fallback theorem
(`pb_guard_nonidentity_falls_back_axiom_free`, a `True ∧ P` prop-simp
redex) closes on both bridges with footprint `[propext, Quot.sound]`
(Lean) / axiom-free (Rocq) — the decision procedure, not the walker,
emitted the proof.

### 5.4 Decision record — ℕ→ℤ specialization and the first lifting (2026-09-01, R3-M1)

**Question** (roadmap R3-M1). The architecture's central bet —
metadata-bearing IR, refinement records with real soundness
witnesses, and lifting back — had never met a real goal: reifiers
were `Int`-only, `Refinement.run` fabricated its witness string, and
no lifting code existed. M1 makes ℕ the first specialized carrier,
end to end, on both bridges.

**Decision 1 — the reifier emits the ℤ image, documented in the IR.**
A ℕ goal reifies as what `zify` produces: every ℕ atom occurrence
sits under the shared IR cast symbol `Int.ofNat` (Lean normalizes
`Int.ofNat`/`Nat.cast`, Rocq `Z.of_nat`, to it), literals become Int
numerals (closed `^` constant-folds, so `2^24`-scale literals ride
as numerals; Rocq additionally folds its `of_num_uint` decimal
representation), and one `_pb_nonneg_<atom>` hypothesis per ℕ atom
carries the ℕ-ness into the image. Free vars stay declared at their
TRUE carrier `"Nat"`; the SDK treats the cast as transparent
(`Farkas.linearize`, `Tier3_alethe.shell_to_sexp`, `Smtlib.emit`) —
sound because a Farkas combination over the atoms is valid over all
of ℤ and the range constraints are explicit hypotheses. A product
with no literal factor (the R4-D1 `Zmax * zhigh` shape) is atomized
to a spec-§4.4 `Opaque` node — a fresh Int atom, nonneg like every
ℕ atom, its origin recorded in `goal.payloads` — the first live
producer of `Opaque`. Fail-fast scope (the R3 attack surface): ℕ
subtraction, division, modulo, and nested ℕ quantifiers are named
reifier errors (a leading `∀ (n : ℕ)` goal binder is introduced by
the tactic front-end instead); the refusal holds inside atomized
products too, as a named-head scan over the core ℕ arithmetic
vocabulary — the notation heads, the directly-spelled `Nat.sub`/
`Nat.div`/`Nat.mod`, and `Nat.pred` (C3a rounds 1–2) — while an
opaque FUNCTION application inside an atom stays an honestly opaque,
uninterpreted atom; ℕ does not compose with UF/BV/HO/Real carriers
yet.

**Decision 2 — spec §4.6 kind + real witnesses (fail closed).** The
metadata entry for ℕ uses the **`primitive` kind** (the
`type_variable` alternative requires a typeclass-instance object ℕ
does not have), with `theory_tags` carrying the embed tag plus
`embedding_witness:<name>` tags naming the lemmas the lift actually
applies (`Int.ofNat_le/lt/inj`, `Int.natCast_nonneg`; Rocq
`Nat2Z.inj_le/lt/inj/is_nonneg`), each backed by a
`library_provenance` entry with a real content hash (statement
SHA-256, via the new `content_hash` FFI on Lean). `Refinement.run`
no longer fabricates: `soundness_witness` is the joined witness-tag
payloads — for the primitive path AND the pre-existing
`type_variable` path — and **no witness tag means no
specialization**; likewise a `specialization_targets` entry without
its (new, v1.1-bound, additive-optional) `soundness_witness` field
emits no method record. `check.py`/`validate.py` require every
witness token to resolve in `library_provenance`, on IR fixtures and
on paired certs.

**Decision 3 — the lift, and the specialization gate.** The
cert-consuming closers rebuild the ℕ proof from the ℤ certificate by
term construction: comparison goals enter through decidable-byContra
wrappers (`natLeViaLt`/`nat_le_via_lt`; equality splits via
`le_antisymm`), every witness-named hypothesis is cast to its ℤ
image through per-shape shims applying exactly the recorded witness
lemmas, `_pb_nonneg_*` facts are proved outright, and the ordinary
Int machinery (Farkas fold / Alethe walker with a cast-mapped atom
context) runs over the images. Lean leans on kernel defeq for cast
distribution (core's `natCast_add/mul` are `rfl`); Coq's `Z.of_nat`
does not reduce on open terms, so the Rocq push is explicit
constructive lemma chains (`nat_push_*`) — which is why the **Rocq
ℕ term-mode footprint is EMPTY** (the M1 Rocq gate) while Lean's is
`[propext, Quot.sound]` (the fold's omega residual). The R2
identity-trace guard's discipline extends to refinement, with the
same two-mode semantics: the strict entry points (`proof_broker_term`,
`proof_broker_walker`, both Tier-1 and Tier-2 arms) verify the cert's
recorded specializations are exactly those this bridge inverts
(today: the one `Nat → Int` record, required present in ℕ mode) and
fail closed with a named error on anything else; plain
`proof_broker`'s walker attempts SKIP the cert on a non-invertible
record and fall back to the decision-procedure closer, which
re-proves the original goal itself. Both branches of the gate are
pinned by synthetic-cert fail-closed tests on both bridges
(`spec_gate_test` / `pb_spec_gate_test`).

**Measured** (2026-09-01, branch `r3/nat-specialization`, full
harness per RESUME §3): 7 new ℕ corpus goals (2^24 literals, a
`∀ n : ℕ` instance, the D1 nonlinear-atom shape included) close
live-strict via `proof_broker_walker` on BOTH bridges — corpus
live-mintable 24/24; term-mode ℕ theorems close on both bridges
(Lean `pb_nat_term*` at `[propext, Quot.sound]`, Rocq
`pb_nat_term*_axiom_free` "Closed under the global context");
gates "all 135 within ceiling" (lean) / "all 169 within ceiling"
(rocq). Scoped follow-ups: the static `CorpusReplay.v` walker has
no cast layer (ℕ goals carry `static_replay_skip`; the live suites
are their ground truth), and cvc5 mints Tier-1 Farkas only for
shapes whose proofs contain `la_generic` — corpus goal shapes and
the term-mode tests were chosen accordingly.

**Known limitation — Rocq plain-decimal literal scale** (2026-09-01,
found by CI, post-C3a): the Rocq lift discharges the literal leaf
`Z.of_nat <lit> = <lit>%Z` by kernel conversion, and for a PLAIN
decimal ℕ literal that normalizes `Nat.of_num_uint` through the unary
numeral — cost linear in the literal's VALUE. Measured standalone
(`Goal Z.of_nat <lit> = <lit>%Z. reflexivity.`): 65535 → 0.7s/0.4GB;
1048575 → 8s/0.9GB; 16777215 → 153s/7.4GB per coqc. Two 2^24-scale
test files at `dune -j4` OOMed the 16GB `ubuntu-latest` runner (step
SIGTERM, exit 143, no output). Closed pow forms are exempt:
`2^k` bridges via `nat_push_pow` + binary ℤ computation (the D1
goals keep `2^24` untouched). Disposition: the exercised plain-decimal
scale is capped at 2^16 (`nat_pow_bound`, `pb_nat_walker_pow_axiom_free`);
Lean keeps its own 2^24 theorems (binary literals — cheap; they pin
the `defEqCapped`/`tryCatchRuntimeEx` maxRecDepth regressions).
Real fix, deliberately deferred past M1: prove
`Z.of_nat (Nat.of_num_uint d) = Z.of_num_uint d` by decimal induction
(no stdlib lemma exists) and route big literal leaves through it —
touches `term_mode.ml` leaf construction, so it takes its own review.

**RESOLVED** (2026-09-02, post-R3 side PR, branch `r3/decimal-leaf`;
scope completed after its ROUND 1 Med): the deferred fix landed.
`nat_of_num_uint_dec` (via `of_lu_agree` — the `DecimalNat`/
`DecimalPos` `of_lu` folds are digit-wise identical and `N.of_nat`
is a semiring hom — and `of_nat_of_uint`; all axiom-free) bridges
the decimal structurally, and `push_nat_to_z` routes
`Nat.of_num_uint (UIntDecimal _)` leaves through
`eq_trans (nat_of_num_uint_dec d) eq_refl`, leaving only the BINARY
`Z.of_num_uint` computation to the kernel. The pow arm rides the
same route: ROUND 1 found that `nat_push_pow`'s bare-`refl`
hypothesis re-opened the wall for a big-decimal BASE under a folded
pow (in-contract for any exponent ≤ 256; measured 6.0GB/139s at
16777216^2 scale), so the plugin now applies the cast-premise
`nat_push_pow_cast`, whose base leaf recurses through the
structural route (the exponent is always a cheap S-chain, ≤ 256 <
the notation threshold). Both cert consumers share the leaves (term
mode and the walker's cast layer).

Scale restored and extended, with pins on every route:
`nat_pow_bound` + `pb_nat_walker_pow_axiom_free` back at 2^24
(walker), `pb_nat_term_big_dec_axiom_free` at the D2-scale
2^64−2^32+1 plain decimal (term; unreachable by unary
normalization at ~10^19 constructors), and
`pb_nat_term_big_pow_axiom_free` at `16777216 ^ 2` (term, the
ROUND 1 probe shape). Decimal only, matching the reifier's literal
fold (a hexadecimal literal hits the named reifier refusal and
never reaches the lift); S-chain literals below the notation
threshold keep the plain `eq_refl` leaf.

Measured (2026-09-02, this branch, 58GB/16-core machine; memory
figures are qualified because the R3-M1 CI OOM was about TOTALS):
standalone leaf probe (`coqc` on a scratch file holding the 2^24
and 2^64 goals as `etransitivity; apply nat_of_num_uint_dec;
reflexivity`, measured by zsh `time` with `%M`): 0.89s / 0.41GB for
both together, vs 153s / 7.36GB for the 2^24 one alone by bare
`reflexivity`. Full tree from `dune clean`, measured by
`systemd-run --user --scope -p MemoryAccounting=yes` reading the
scope's `memory.peak` (whole-build TOTAL) alongside zsh `%M` (max
SINGLE process): at `-j4` (the CI runner's width) total 2.07GB,
wall 18.4s; at `-j16` total 7.09GB (parallelism × the ~0.5GB
per-coqc stdlib baseline — no single heavy file), wall 17.7s; max
single-process RSS 0.54GB at either width.

### 5.5 Decision record — polymorphic α and the replay-at-α lift (2026-09-01, R3-M2)

**Question** (roadmap R3-M2). Spec Example 1 *as written* — a goal
over a type variable `α` with ordered-comm-ring class instances —
had never been producible live: the reifier rejected every carrier
but the concrete ones, and the `type_variable` refinement path was
exercised only by the authored `example1-lia-typeclass.json`
fixture.

**Decision 1 — the class spelling.** The roadmap names
`[LinearOrderedCommRing α]`; Mathlib's 2025 ordered-algebra
refactor removed that bundled class, and it is absent from the
pinned Mathlib v4.32.0. The implemented qualification is its modern
spelling — `[CommRing α] [LinearOrder α] [IsStrictOrderedRing α]`,
exactly the instances the lift family
(`ProofBrokerMathlib/TermModePoly.lean`) is stated over. A local
`α : Type u` qualifies iff all three synthesize; class-instance
locals are metadata, not hypotheses (skipped by the LCtx walk —
dropping an assumption only weakens the solver, never soundness).
One type variable per extraction; α does not compose with
ℕ/UF/BV/HO/Real carriers (named errors). The IR names the variable
canonically `"alpha"` (spec Example 1's name; keeps non-ASCII
binder names out of the wire format — the substitution applies to
type tags, so the choice is invisible to the user).

**Decision 2 — the witness discipline carries over.** The emitted
`type_variable` metadata carries one `Instance` entry per required
class (real content hash of the class signature) and, on the
ordered-ring entry, `embeds_into:Int_for_universal_LIA` plus
`embedding_witness:` tags naming the lift-family lemmas the closer
actually applies (`pLeViaLt`, `pLtViaLe`, `pFarkasContradictN`,
`pFarkasContradictNStrict`), each backed by a `library_provenance`
entry (`proof-broker-bridge`, real content hashes). The
pre-existing SDK refinement path (`type_var_witness`, R3-M1's
fail-closed rule) substitutes alpha → Int FOR THE SOLVER and
records the specialization with that witness.

**Decision 3 — inversion = replay at α, and the +1-trick
boundary.** The cert's Farkas coefficients are replayed AT α
through the class-polymorphic family — the α→Int specialization
never touches the delivered proof term. The α fold is
strictness-preserving like the Real one and NEVER applies the LIA
+1 trick: α may be dense, so a witness whose contradiction depends
on integrality (SDK-valid over the Int image) fails the α replay's
residual check (`ring_nf` + `norm_num` on the literal-coefficient
ring identity) — a tactic failure, never an unsound closure. The
specialization gate becomes mode-keyed: the term-mode path requires
exactly the alpha → Int record on an α extraction (pinned by
synthetic-cert tests, `spec_gate_test poly *`); the walker paths
keep refusing α certs (no walker inversion at α). Plain
`proof_broker` routes α extractions to the same replay (omega is
Int/ℕ-only) — and the replay CONSUMES the cert, so the plain route
carries the R2 trace requirement exactly as term mode does. An α
extraction CAN emit unfolding equations (a ℕ-typed hypothesis over
numeral-body constants fills the unfold table without tripping ℕ
mode), so admission means identity OR extraction-emitted definition
unfolds — inverted on the plain α route exactly as on the term-mode
entry (pinned by a committed α+ℕ-def positive) — and any other
rewritten trace is a named refusal (pinned by a committed prop-simp
negative). Tier-2 case-split at α is a named refusal.

**Measured** (2026-09-01, branch `r3/poly-lifting`, full harness per
RESUME §3): `pb_poly_example1` — Example 1's goal stated with a type
variable — closes `by proof_broker_term [z3]` at
`[propext, Classical.choice, Quot.sound]` (the Mathlib classical
baseline; z3 pinned for native Tier-1 Farkas, the LRA-suite
convention — cvc5 prefers Tier-3 alethe, which no α closer
consumes). The Int-only witness `{h:1, neg_goal:1}` for
`0 < n ⊢ 1 ≤ n` is refused by the replay (`poly_replay_test`
negative; live probes on z3/cvc4/bare refuse the same shape). An α
merely in scope over an Int goal stays on the core path at
`[propext, Quot.sound]`.

**Rocq port: DEFERRED** (per D3's "Lean leads; Rocq ports at phase
gates" and the R3 gate row "M2/M3 Rocq: deferral entry allowed").
Reconsideration: when a Rocq consumer needs section-variable
polymorphic goals, port the recognition (typeclass-instance
detection differs — Rocq's ordered-ring vocabulary is
`ring`-theory-based, not Mathlib's mixin classes) and mirror
`TermModePoly` as constructive lemma chains like the M1 shims. The
SDK side is shared and already live (the α fixture dispatches in
`test_adapter_cvc4`).

### 5.6 Decision record — definitional metadata and def-unfold inversion (2026-09-01, R3-M3)

**Question** (roadmap R3-M3, the R4-D2 prerequisite). A goal
against a named numeral constant (`def P : ℕ :=
18446744069414584321`) previously dispatched with `P` opaque —
unprovable — or not at all; the definition-unfolding pass existed
but nothing on the live path emitted `definitional_metadata`, and
no inversion existed.

**Decision 1 — reifier scope: numeral-body ℕ definitions.** A
`defnInfo` constant of type `Nat` whose elaborated body is a
numeral reifies as an opaque `App` leaf (no cast wrapper — the
leaf sits at the Int-numeral position of the ℤ image) plus a
`defined_function` metadata entry whose `definitional_equation` is
`c = <numeral>` at the image type, `concept_tag:
numeral_definition`, and a `library_provenance` entry hashing the
definition body. Theorems, opaques, axioms and non-numeral bodies
decline into the named unsupported-term error (fail closed). If
the unfold does NOT fire, the SMT script references an undeclared
symbol and dispatch fails — never a silent misreading.

**Decision 2 — the pass fires through BOTH spec §5.4 channels.**
`numeral_definition` joins the registry's
`always_unfold_for_dispatch` (two-way-pinned to `pipeline.ml` by
check.py; a nullary-def unfold through the DEFAULT dispatch
pipeline is unit-pinned) AND the reifier stamps the user directive
(`enable_definition_unfolding: ["numeral_definition"]`) — which now
survives the walker-strict `tier_preference` override (merged, not
replaced).

**Decision 3 — the guard is lifted for exactly this pass, and the
inversion is `Eq.mpr`.** The R2 identity-trace guard's term-mode
form becomes `termTraceError?`: a non-identity trace is admitted
iff every non-identity entry is an APPLIED `definition_unfolding`
whose `inversion_data.unfolded_symbols` are all constants this
extraction emitted equations for; failed passes, foreign symbols,
and any other applied pass (prop-simp) stay named refusals — all
pinned branch-by-branch on synthetic traces (`trace_guard_test`).
Before the closer consumes the cert, `invertDefUnfolds` rewrites
the goal with `c = <numeral>` — proved by `rfl`, checked by the
kernel via delta reduction, visible in the lifted term as the
`Eq.mpr` the roadmap asks for — and defeq-swaps the type of every
hypothesis mentioning the constant. Plain `proof_broker`'s
cert-gated omega applies the same inversion first (omega cannot
see through a non-reducible def); the WALKER paths remain
identity-only (no walker inversion in M3 — walker-strict on a
def-unfold dispatch is a named failure).

**Measured** (2026-09-01, branch `r3/poly-lifting`, full harness
per RESUME §3): the D2 gate `Zmax ≤ 2^16 ⊢ Zmax < P` with `def P :=
18446744069414584321` closes `by proof_broker_term` at
`[propext, Quot.sound]` — load-bearing evidence the unfold fired
(with `P` opaque the goal is unprovable, so no cert could exist)
and was inverted; plain-mode and hypothesis-position variants close
identically. Lean gate `OK: all 165 allowlisted theorem(s) within
their axiom ceiling.`

**Rocq port: DEFERRED** (same D3 rule as §5.5). Reconsideration:
with the M1 push-cast machinery in place the Rocq inversion is a
`change`/`Tactics.convert` over the unfolding equation. The §5.4
plain-decimal scale limitation that once bounded any big-literal
def on Rocq is RESOLVED (the decimal-induction lemma landed on
`r3/decimal-leaf` — see §5.4's RESOLVED record), so scale no longer
blocks this port; only the D3 consumer trigger does.

---

---

### 5.7 Decision record — downstream consumability and the verinf obligation shapes (2026-09-03, R4)

**Context.** R4's target is verinf's bracket spike
(`lean/BracketSpike/BracketSpike/Bracket.lean`, branch
`lean-bracket-spike`), consumed from a separate Lake project.

**Decisions.**

1. **Manifest discovery is package-anchored.** `defaultManifestDir`
   keeps `$PROOF_BROKER_EXAMPLES_DIR` (verbatim, no probe) and
   `<cwd>/../examples`, then falls back to a directory derived from
   where `ProofBroker.Tactic.olean` was loaded from. The cwd
   candidate is stepped over only when it holds none of the four
   manifest names — i.e. exactly where the previous code raised "no
   manifests found". Without this, every downstream call died unless
   the user exported the variable by hand.

2. **`--load-dynlib` paths are absolute**, computed from Lake's
   `__dir__`, behind a named `proofBrokerLeanArgs`. The previous
   cwd-relative spelling only resolved when the build ran from
   `lean-bridge/`. A downstream project cannot import a lakefile
   definition, so `lean-bridge/CONSUMERS.md` carries the
   copy-pasteable block; the two are kept in step by hand.

3. **Closed ℕ arithmetic folds to one numeral** (`natClosedNumeral?`,
   bounds `natFoldMaxExp = 256`, `natFoldMaxBits = 4096`).
   Recognizing only `OfNat` literals made `2^16 * 2^16` atomize into
   an unbounded `Opaque` atom, and made `Zmax * 2^16` a fake-opaque
   atom although it is linear — the "Opaque atom that is not
   actually opaque" the R4 attack surface names. A closed power that
   leaves the bounds is a named error, not an atom.

4. **Atomization extends to applied functions and to Int.** An
   applied ℕ-valued function (`x.val`) and an Int term with no
   fragment reading (a projection at an undeclarable argument type,
   a nonlinear product) become `Opaque` atoms. Sound for any meaning
   of the term — replacing a subterm by a fresh constant generalizes
   the goal — at a cost in completeness. The R3-M1 ℕ-truncation
   contract is preserved inside atoms on both sides
   (`natAtomForbiddenOp?`, and its type-aware Int sibling
   `natOpInsideIntAtom?`).

5. **Locals are alpha-renamed to SMT-safe names before reification.**
   Primed names are idiomatic Lean and pervasive in the target
   (`c'`, `h1'`); the serializer refuses them. Renaming on the GOAL
   rather than mapping names inside the IR keeps one name for one
   thing across reifier, certificate, `fvarOfName` and walker
   context, so no inverse map has to be trusted at lift time.

6. **A hypothesis outside the fragment is dropped, not fatal**, and
   recorded in `skippedLocals` (reported by `proof_broker?`).
   Dropping only weakens the assumption set. The GOAL is never
   dropped, so the ℕ-truncation fail-fast still applies to
   everything the certificate reads. This CHANGED shipped behaviour:
   a nested-ℕ-∀ hypothesis used to abort the tactic.

7. **Def-unfold inversion is a defeq `change`, restricted to value
   positions.** `rewrite` needs a motive, which does not typecheck
   when the constant also indexes a type in the goal
   (`x.val + z.val < P` with `x : ZMod P`). And rewriting occurrences
   inside a type is a kernel bomb: `ZMod P` → `ZMod <2^64-scale
   numeral>` makes the next defeq check reduce `Nat.rec` at that
   literal. `constOnlyInValuePositions` gates both the goal (named
   error) and the hypothesis swaps (skip).

**DEFERRED — Rocq port.** None of items 3–7 has a Rocq counterpart.
R4's ROADMAP row says "Rocq port: none" because D3 is Lean-only, but
the two reifiers have now diverged further than that row anticipated.
Trigger to revisit: any Rocq-side consumer of the ℕ→ℤ path meeting
a closed-numeral product, an applied-function atom, or a primed
identifier.

**FIXED — exponential materialization in the internal Farkas search
(originally recorded here, wrongly, as "unbounded allocation on the
cvc4 path").** C4 ROUND 1 falsified this record's first
characterization in every material respect, and the corrected
mechanism is: `Farkas_search.try_close` materialized the entire
coefficient space (`cartesian`, 4 candidates per inequality input, 7
per equality) before searching — 4^13 ≈ 67M candidates ≈ 4.7GB at
the 13 inputs `m_full.lean` sends (7 user hypotheses + 5 synthetic
ℕ-nonnegativity facts + neg_goal), 4^15 ≈ 76GB at the demo's
15-input goals (`D1_78`/`D2_62`), which is the observed 57GB OOM.
Post-dispatch, not pre- (cvc4 IS spawned and answers unsat in
7.6ms); bounded-but-exponential per input count, not unbounded; and
NOT cvc4-specific — the search is the internal Tier-1 fallback for
all three SMT adapters and reproduces identically via cvc5 whenever
its proof extraction fails. Pre-existing SDK code (untouched by R4);
R4's atomization added +2 inputs on exactly the demo's goal shape,
which is what made it reachable at machine-killing scale.

Disposition (C4 ROUND 1 prescription, both parts landed in the fix
round): the enumeration now STREAMS in the identical order (O(n)
live memory, first-hit witness pinned, order equivalence proven
exhaustively to 4^8), and a saturating size check refuses spaces
above its candidate cap with a named
`search_space_exceeded` error. The second part is a deliberate,
recorded behavior change: a goal whose coefficient space exceeds
the cap no longer gets a Tier-1 rescue when
solver proof extraction fails — it falls through to the Tier 0
oracle cert, exactly the pre-existing fallback. Regression-tested
(13-input IR returns immediately). The cap's VALUE was re-derived at
C4 ROUND 2/3 (Levi 2026-09-03): the initial 100k was inherited from
the comment that had justified materialization; the shipped value is
2,000,000 — a measured time budget (4^10 sweep = 0.77s CPU / 1.3MB
live; basis recorded in the module comment) — so the refusal
threshold is ≳11 inequality inputs, and the demo's `D1/70` (4^10)
is rescued while `D2/62`/`D1/78` (4^14+) stay refused. "Drop cvc4
from the default adapter list" was considered and rejected: it
removes the most reliable trigger while leaving the defect live
behind cvc5/z3.

**FIXED — reifier accumulator race under parallel elaboration**
(2026-09-03, C4 ROUND 3 High; fix round of the same day, Levi's
explicit call to fix rather than defer behind a workaround).
Symptom: the demo's headline file failed 10/33 elaborations and 1/6
forced builds with `unsupported_symbol: Bracket.P`. Cause: the
reifier's four module-level accumulation refs (applied consts, ℕ
atoms, Int atoms, numeral defs) assumed "single-goal reification is
sequential" — false under Lean v4.32, which elaborates a module's
(named) declarations in parallel; concurrent `buildIR` calls
interleaved resets and pushes. Snapshot-threading alone (the R3-M1
`natAtoms` patch) is insufficient — the refs were shared DURING
accumulation — so the fix makes accumulation itself per-call: each
`buildIR` creates a fresh `ReifyAcc` and the reify family threads
it explicitly; the module refs are deleted (`reifierExt` remains as
documented set-once registration). Not a soundness defect (the
failure is fail-closed), but it sat on R4's gate path. Verified by
a 33-elaboration + 6-forced-build protocol on a quiesced tree: 0
failures at bridge `259ada9` (the fix commit; the fix-round
protocol's demo tree was not recorded at the time — later rounds
re-verified at recorded pairs. Baselines, both repos' trees from
the ROUND records: 10/33 probes and 1/6 forced builds both measured
by ROUND 3 at bridge `c6805c0` / demo `858485c`; the re-share
replay re-derived 9/33 at ROUND 4's pair `960ca26`/`c2dc119`, where
ROUND 4 also confirmed reification semantics byte-identical across
the refactor on 8 shapes; ROUND 6 re-ran 3/3 forced builds green at
`6618587`/`1f51610`).
Pinned in THREE parts (the split
found at C4 ROUND 6 Med 1; the load-bearing third added at ROUND 8
Med 1 after the textual gate lost a spelling per round):
`reify_callsite_isolation_test` is the LOAD-BEARING pin — it runs
the real `buildIRWithAcc` twice and observes ALIASING between the
accumulators the reifications actually used (run 1's atom table
must survive run 2; a marker in run 2's must not appear in run 1's)
— red under any spelling that leaves `buildIRWithAcc` returning
the accumulator it accumulated into, which every single-accumulator
mutation does (mutation-verified: `initialize`-backed shared
accumulation with `fresh` intact, per-field). KNOWN RESIDUAL
(ROUND 9; corrected at ROUND 11 — the ROUND 10 form was inverted
on both halves): the surviving residual is a DECOY mutant
(accumulate in shared state, return a copied accumulator —
invisible to any return-value pin by construction) composed with
any store or spelling that the gate's
best-effort lexer mishandles: ROUND 10's M′ used a string-literal
blinding (closed by the string-aware stripper), ROUND 11's M″ used a
Char-literal parity flip (a known unhandled lexing edge — the gate's
lexer is approximate by design and further edges exist: raw strings,
interpolation nesting). A synonym-hidden store, by contrast, IS
caught (invariant (2) errors on unrecognized initializers — ROUND 9
NOT CONFIRMED #5). The residual is covered by REVIEW only;
`reify_acc_isolation_test` pins the
constructor at runtime (all four fields independently since
ROUND 5; red on every run under any re-sharing inside
`ReifyAcc.fresh`, mutation-verified per field), and
`check_lean_reify_isolation` in `tools/check.py` is DEFENSE IN
DEPTH — a comment-stripped scan of every .lean file under
lean-bridge/ for module-level `IO.Ref` initializers (`initialize`,
`builtin_initialize`, `@[init]`, any indentation) beyond
`reifierExt`, unrecognized initializers, and stray
`ReifyAcc.fresh` sites; it fails LOUD with a named location at
review time, and a spelling it cannot see is caught by the
call-site pin instead (negative controls in `test_check.py`, 73); the
`Test/TacticStress.lean` herd exercises concurrent per-call
accumulators under real async elaboration but is NOT a reliable
catcher — measured pre-fix catch rates 0/30 builds
(anonymous-example form, C4 ROUND 4), then on the shipped
named-theorem form at ROUND 5: 0/20 under the all-four-shared
mutation and 0/10 under the natDefs-only one, each by restoring
shared refs and force-rebuilding `ProofBrokerTest` on this
16-core/58GB machine at the then-current `r4/demo` tip;
dispatch-free `buildIR` windows are ~1.5ms (ROUND 4's
`stress_window` probe at `960ca26`); the demo file raced because
its windows span live solver round trips. The constructor pin's
coverage was itself reviewed twice: ROUND 5 found it asserting one
field of four (a `natDefs`-only re-share escaped every pin while
the demo file failed 4/27 at `52dbff1`/`ac32ee1`), and ROUND 9
found the
call-site pin repeating the same one-field mistake (its
`natDefs`-only call-site re-share put the demo at 9/27 at
`37fda79`/`b449733`); both pins now assert all four fields independently,
mutation-verified per field.

## 6. References

- **Spec v1.0:** `proof-brokerage-spec-v1.pdf`. The architectural
  specification this delta amends only superficially.
- **Roadmap v1.0:** `proof-brokerage-roadmap.pdf`. The engineering plan
  this delta amends in §§2–3.
- **Reference card v1.0:** `proof-brokerage-refcard.pdf`. Unaffected by
  this delta; language choice does not surface in the reference
  vocabulary.

---

*End of delta document.*
