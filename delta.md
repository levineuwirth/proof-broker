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

---

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
