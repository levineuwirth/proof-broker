# Checkpoint 2 — exact-coefficient recovery, implemented

**Status: implementation and campaign committed as `e627efe`; reporting
amended 2026-09-07.** Campaign directory
`experiments/c1-cert-recovery/`, branch `r6/c1-cert-recovery`, pass
`20260907-113052`. Continues `reports/checkpoint-1.md` after its review; the three
corrections that review required are applied there and summarized in §1 here.

## Outcome, in a paragraph

The repair works, is additive, cost nothing the SDK could do before, and — after
a second review found six defects — the evidence for it is now produced by
binaries that actually contain it. All four original carry obligations
reconstruct in term mode (`CarryLiftPBTerm` 4/4, in file, in context,
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`), against the
previously refused site 2. On the 24 cases present in both the pre-repair and
final passes, term mode improves from 4 closures to 20: **16 recoveries**, with
no regression in any of seven closers on those paired cases. The final
26-case corpus also includes two added preservation controls, both closed,
bringing its total to 22 closures (§4.2). The held-out set, run once after the
design was fixed, matches all six checkpoint-1 predictions: five true goals
reconstruct and the false control is refused. Coverage flagged by the first
review is preserved by construction: exact recovery runs only where the enumerating search returned an
error, and `V1_chain_support5` still routes through the dense enumeration and
still reconstructs. The second review's six findings are fixed and each is now
pinned: `support_count` no longer overflows past its own cap (regression to
`max_int / 2`); a work budget accounting for matrix rows and coefficient size
bounds the running time the support cap never did (the review's adversarial IR
went from >30 s to a named refusal); every diagnostic executable is rebuilt and
hashed inside the gate; a failing expectation generator now fails the gate;
both verification interfaces are asserted rather than one asserted and one
printed; and `Lt(0)` is classified as the contradiction it is. The regenerated
battery is 224 mutations over 28 cases with `Farkas.verify` and
`Verifier.verify` each agreeing 224/224. Nine new SDK tests cover what exact
recovery finds, all three of its refusal boundaries, and that it returns the
enumerated witness byte for byte where the enumeration succeeds. What this does
**not** show, and the report says so in §4.4: any improvement in solver-proof
extraction. All four consumed carry-site witnesses are SDK-synthesized and then
reconstructed in Lean; the two extraction gaps from checkpoint 1 are untouched.

## 1. The three corrections from the review

All three were reproduced here before anything was changed.

**(1) The proposed repair would have lost existing certificates.** The
checkpoint-1 text said "keep the support bound, drop the magnitude bound",
which reads as replacing the enumerating search with a support-≤4 exact solve.
The support bound is not the enumerating search's — `max_support = 4` governs
only the *sparse rescue* that runs when the dense space is over budget, and
the dense path has no support limit at all. Reproduced on the review's case,
`x₀ ≤ x₁ ≤ x₂ ≤ x₃ ≤ 0 ⊢ x₀ ≤ 0`: the witness is coefficient 1 on all four
hypotheses *and* `neg_goal` (support 5), variable cancellation forces all five
equal so nothing smaller exists, and the dense path finds it today (4⁵ = 1024
candidates). The change implemented here is therefore **strictly additive** —
exact recovery runs only where the enumerating search returned an error, so no
witness the old code produced can change, by construction rather than by
measurement. The case is frozen into the corpus as `V1_chain_support5`, with
`V2_chain_support7` pinning coverage further above the bound.

**(2) The explanation of `O1`'s accepted mutations was wrong.** The battery's
"load-bearing" test was "the compiled form contains a variable", which
classifies the ground contradiction of a variable-free goal as vacuous;
selection fell back to `hP`, whose compiled form after definition unfolding is
the identically-zero `Eq(0 = 0)`. The five accepted mutations had changed a
term carrying no proof content, and the real inequality was never touched.
Corrected: `checkpoint-1.md` §6 is rewritten, target selection now prefers an
input with variables and then a *non-vacuous* one, the reported flag is derived
from the target actually chosen, and the expectation for every mutation is
**computed** rather than assumed — the gate asserts the shipped verifier agrees
in both directions. With the target corrected, `O1`'s zero/negate/drop
mutations are rejected and only the positive rescaling stays valid, matching
the review's independent run. The over-broad claim that every fallback witness
names `hP` is corrected to the four of five that do (`O4`'s does not).

**(3) The negative-check runner did not enforce its gate.** Reproduced, and
worse than reported: `cmd && echo ok || echo FAIL` made every failure a
successful `echo`, and the script also exited 0 with no `logs/STAMP` at all.
`negcheck.exe` now exits nonzero on any disagreement with the expectation or
any envelope mutation not refused as `hash_mismatch`; the runner fails on a
nonzero exit, a missing or unreadable result, a `gate.ok` that is false, a case
with an expectation but no captured IR, and a case declared unreifiable that
unexpectedly has one. The gate is self-tested by fault injection
(`NEGCHECK_BIN=tools/negcheck_fault_stub.sh`, a stub that exits 42) and by
removing `logs/STAMP`; `logs/negcheck_gate_selftest.txt` records both exiting
nonzero.

## 1b. The six corrections from the second review

All six were reproduced here before anything was changed. Three were defects
in the SDK change itself; three were defects in the gate that was supposed to
police it.

**(1) `support_count` could overflow and bypass its own cap.** The total
saturated but the running binomial did not, so `support_count 80000` returned
`-599304339613513951` — negative, which passed the `> max_exact_supports`
admission check and let the search run with no cap at all. Reproduced exactly.
Every multiplication is now guarded before it happens and the loop stops as
soon as the count is known to exceed the cap; there is never a reason to
compute the exact size of a space already refused. Regression test covers
`n` up to `max_int / 2`. The review is also right that the cap admits **47**
columns, not 46; the constant's comment said 46 and now says 47.

**(2) The support cap did not bound the running time, and the benchmark could
not have shown that it did.** The sweep used forms mentioning few variables
each, so every support's matrix was small. On the review's IR — 46 columns,
forms over 64 variables — exact recovery ran past 30 s here, under the support
cap throughout. Two changes:

* the matrix build was O(rows × k × |coeffs|) per support, because variables
  were collected with `List.mem` and cells filled with `List.assoc_opt`. It is
  now a hash table and one pass over each column's already-sparse coefficient
  list.
* rows are now a *budgeted* dimension. `max_exact_work` bounds
  `(rows + 1) · k² · bit_weight` summed over the supports examined, where
  `bit_weight` carries the size of the numbers involved, with
  `Exact_search_work_exceeded` as its named refusal. Deterministic — no wall
  clock — so a witness is found or refused identically on every machine.

The cost sweep now runs **two** shapes (`logs/exact_budget.txt`). At the cap
the worst observed wall time across both is **387 ms**, against >30 s
unguarded; the review's own IR is refused by name in well under a second.
And 387 ms is stated as *the maximum measured on these two shapes*, not a
ceiling: coefficient growth during elimination is not captured, and the
constant's comment says so.

**(3) The recorded gate ran a stale binary — and so did the tracer.** The
review found `negcheck.exe` predating the repair. Checking further, `diag.exe`
was stale too, in a different way: it predated the *budget* change and still
reported the 20,000 cap. So checkpoint 2's §6 numbers (56 mutations over 7
cases) were the old SDK's, and the route table was produced by a binary
carrying a superseded constant. All artifacts are regenerated (§4).

*Corrected again after the final review.* The first fix wired the build into
`run_negchecks.sh` only, while the report claimed "every runner calls it
first" — `capture_ir.sh` still launched the tracer directly, and `run.py`,
`run_carrylift.sh`, `run_heldout_broker.sh` and `probe.sh` had no preflight at
all. The claim is now implemented and tested:

* `tools/build_diag.sh` builds `sdk/ffi`, `sdk/lib` and all three executables
  and writes their hashes to `logs/diag_binaries.txt`. **All five entry
  points** — `capture_ir.sh`, `run.py`, `run_carrylift.sh`,
  `run_heldout_broker.sh`, `run_negchecks.sh` — call it before any timing or
  probing and exit 2 if it fails.
* `tools/probe.sh` calls `build_diag.sh --verify` on the paths it has
  actually resolved (§1c.2), for all three shared objects it loads: a hash
  check against the ledger, no dune. It costs ~12 ms per run (0.3% of a
  ~3.5 s probe, and outside the `tactic execution` figure the cost table
  reports), and it means no probe can load a shared object the ledger does not
  record — the failure this whole thread is about.
* `run_negchecks.sh` used to skip its preflight whenever `NEGCHECK_BIN` was
  set, so any caller supplying an executable bypassed the build check. Found
  by the new test's own positive control; the preflight now always runs.
* `tools/test_runner_preflight.sh` is the focused test the review asked for.
  For each entry point it asserts BOTH halves — nonzero exit **and** zero
  probe/tracer invocations, counted by canaries substituted through the
  `PROBE_BIN` / `DIAG_BIN` / `NEGCHECK_BIN` seams — and it runs a **positive
  control** first, so the test cannot pass because a seam is dead. 5 entry
  points × 2 halves, all green (`logs/runner_preflight_selftest.txt`).

**(4) A failing expectation generator still let the gate pass.** Reading the
manifest from a process substitution discarded the generator's exit status:
with it stubbed to exit 42 the runner printed "0 case(s) passed the gate, 0
failure(s)" and exited 0. Reproduced. The manifest is now produced by a
checked command into a file, validated (non-empty, every line
`<id> sat|unsat|no-ir`), and only then consumed; the runner additionally
fails if the number of cases it actually reached differs from the manifest's
length. Both fault modes — generator exits nonzero, generator succeeds but
emits nothing — now exit 2.

**(5) The gate checked one verification interface and only printed the
other.** `Verifier.verify`'s verdict was recorded and never asserted, baseline
included. Reproduced the review's injection: forcing `Verified_farkas` for
every mutant left `gate.ok` true. Both interfaces are now asserted, for every
mutation and for the baseline, in both directions — a witness mutation leaves
the envelope untouched, so `Verifier.verify` must return `verified_farkas`
exactly when the oracle expects acceptance. The same injection now produces 8
violations and exit 1.

**(6) The vacuity fix still misread a strict contradiction.** `Lt` of the zero
form is `0 < 0` — false, hence a contradiction on its own, and the supplier of
the LRA strictness clause — but classification looked only at the form's
constant and called it vacuous. Target selection then fell back to a genuinely
vacuous `Eq(0)` and five mutations "passed" without the contradiction ever
being touched. Reproduced. Strictness lives in the *relation*, so
classification now reads it: vacuous means no variables, zero constant, **and**
not strict. On the review's IR the target is now the `Lt(0)` input and 7 of 8
mutations must be rejected. Frozen as fixture `F1_lra_strict_ground`
(`tools/make_fixtures.py`), alongside `F2_eq_negative_multiplier`, which pins
that the ± column split really does reach a negative equality multiplier.

## 1c. Two harness corrections from the final review

The SDK findings were cleared; both of these are defects in the campaign
harness, and the first is one the harness inflicted on its own evidence.

**(1) The preflight self-test overwrote the campaign's artifacts.**
`tools/test_runner_preflight.sh` ran its *positive controls* — the ones that
prove the `PROBE_BIN` / `DIAG_BIN` seams are live — by invoking the real
runners against the real `logs/STAMP`. Canary output therefore replaced
production output, and the test exited 0 while doing it. Measured damage to
pass `20260906-233806`, recorded in `runs/20260906-233806/DAMAGED/README.md`
with a compact inventory beside it in `DAMAGED/INVENTORY.md` (the damaged
outputs themselves are omitted from the repository):

| artifact | after the self-test |
|---|---|
| `results.json` | 1 case of 26 (`B1_true_2p21` only) |
| `carrylift/*.log` | 10 of 10 emptied |
| `heldout/*.log` | 42 of 42 emptied |
| `irlogs/*.log` | 26 of 26 emptied |
| corpus `logs/*.log` | 7 of 182 emptied |
| `*.negcheck.json` | 30 of 30 deleted |
| `*.report.json` | 29 intact (the tracer was never invoked) |

Fixed three ways, and the regeneration is verified against the last intact
full pass: **identical across all seven closers of all 26 cases, 182 runs**,
so nothing about the results turned on the damage. The test now builds a
**temporary campaign root** per case
(`setup_temp_campaign`: its own `tools/`, `logs/STAMP`, and one placeholder
fixture per loop) and runs every control and every check inside it. It then
**snapshots `runs/`, `raw/` and `logs/`** — 2,686 files — before and after
itself and fails if a single path, size or mtime moved; that guard is not
vacuous, a one-line stray write makes it fire. And the damaged pass is
**regenerated under a new stamp**, with the damage record kept rather than
quietly overwritten. Pass `20260906-215904` was never touched and keeps its
original provenance — retained complete, with the stale diagnostics of §1b.3
flagged in `runs/20260906-215904/CAVEAT.md`; its closure results are citable,
its tracer and negative-check outputs are not, and nothing here cites them.

**(2) The probe verified one shared object and could load another.**
`build_diag.sh --verify` checked the repository-default FFI; `probe.sh` then
resolved `PROOF_BROKER_REPO` / `PROOF_BROKER_FFI_DIR` and could load a
different file. Verifying a path nobody loads checks nothing.

`probe.sh` now resolves its paths **first** and verifies exactly those, and it
verifies all three shared objects it loads, not just one — the FFI plus the
bridge's `libpbglue.so` and `libproof_x2dbroker_x2dbridge_ProofBroker.so`,
both of which `PROOF_BROKER_REPO` also swings. `build_diag.sh --verify` takes
explicit paths and matches them against the ledger by basename, and the ledger
records all three. Tested: with `PROOF_BROKER_FFI_DIR` pointed at an
unrecorded file, the probe exits 2 and prints both hashes before Lean is
reached.

### What this says about the result

The distinction the review asks to keep explicit: this work demonstrates that
**SDK certificate synthesis, followed by Lean reconstruction, supplies all four
consumed carry-site witnesses**. It does *not* demonstrate improved
solver-proof extraction. The two extraction gaps diagnosed at checkpoint 1
(G1, z3's mixed-polarity clause; G2, integer-tightened literals) are untouched
and remain open.

## 1d. Closing cleanup

One trailing space inside a doc comment in `farkas_search.ml` (line 465),
flagged non-blocking in the final review, is removed. It is a comment, so
nothing it touches is semantic — but removing it recompiles the library, which
relinks `proof_broker_ffi.so` and moves its hash, and this campaign's whole
argument is that evidence produced against one binary must not be reported
against another. So the pass was regenerated once more against the binary that
is actually committed, rather than reasoning that a comment cannot matter.

The preflight self-test also needed one fix of its own: its
before/after snapshot covered `logs/`, so redirecting the test's output into
`logs/runner_preflight_selftest.txt` made it detect *its own log* and fail. The
snapshot now excludes that one path, which is the test's output rather than
the campaign's evidence.

## 2. The algorithm

`sdk/lib/farkas_search.ml`, `try_close_exact`. The review asked for three
things to be specified rather than gestured at: how the feasibility problem is
actually solved, how rank-deficient systems and freely-signed equality
coefficients are handled, and what the work limit is. Taking them in order.

### The problem

Find rational multipliers `λ₁…λₙ` over the compiled inputs with

* `λᵢ ≥ 0` on `Le`/`Lt` inputs, `λᵢ` free on `Eq` inputs;
* `Σ λᵢ·fᵢ` has zero variable part — call its constant `k`;
* `k > 0`, **or**, under LRA only, `k = 0` with `λᵢ > 0` on some `Lt` input.

That last clause is the LRA behavior the review flagged. `try_assignment` and
`Farkas.verify` both implement it, and a positive-constant-only implementation
would regress goals the enumerating search closes today; exact recovery
implements the same disjunction, taken from the same place.

### Freely-signed equality coefficients

Each `Eq` input becomes **two columns**, carrying `+f` and `−f`, both with a
nonnegative multiplier; the input's coefficient is recovered at the end as
`μ⁺ − μ⁻` (and an `Eq` input whose halves cancel drops out of the witness
entirely). After that split every column is sign-constrained the same way, and
the search space is the nonnegative cone

    C = { μ ≥ 0 : A μ = 0 }

with one row of `A` per variable. Splitting is what makes the sign check on a
candidate ray meaningful rather than vacuous.

### Solving, and rank-deficient systems

Enumerate supports `S ⊆ columns` with `|S| ≤ max_exact_support` (4), size
ascending and lexicographic within a size, so the first hit is deterministic.
For each `S`, row-reduce `A_S` **exactly over the rationals** — no floating
point anywhere, which is the point: a multiplier of 262144 has to come out as
262144 — and read its null space. Then:

* **nullity 0** — only the zero multiplier. Skip.
* **nullity 1** — the null space is a line. Take its generator `u`, clear
  denominators, divide out the gcd (a positive rescaling changes neither the
  sign discipline nor the sign of `k`), and test `u` and `−u` against the sign
  condition and then the contradiction condition above.
* **nullity ≥ 2** — **skipped by design, and this is the answer to "how are
  rank-deficient systems handled".** An extreme ray of `C` whose support is
  exactly `S` forces `nullity(A_S) = 1`; a support with nullity ≥ 2 therefore
  carries no extreme ray of its own, and the rays inside it live on proper
  subsets, which the enumeration also visits. Skipping them loses nothing the
  support bound admits.

Solving the homogeneous system alone indeed does not select a witness — the
review is right — which is why the sign test and the contradiction test are
applied to the *ray*, and why the ray is the object enumerated rather than the
solution space.

### Completeness, stated exactly

If any Farkas witness exists over the compiled inputs, some **extreme ray** of
`C` is itself a witness. Writing a witness `μ = Σⱼ νⱼ rⱼ` over extreme rays
with `νⱼ ≥ 0`, the constant part is `Σⱼ νⱼ (c·rⱼ)`; either some `c·rⱼ > 0` and
that ray is a witness, or every positively-weighted one has `c·rⱼ = 0`, and
then the ray carrying the strict input is an LRA witness. So the **only**
incompleteness is the support bound: a witness all of whose extreme rays need
more than `max_exact_support` columns is not found, and
`Exact_search_exhausted` says so by name, with the number of supports
examined.

### Where it runs

`try_close_then_exact` is `try_close` first, unchanged, and exact recovery only
on its `Error` paths. The four adapter call sites
(`adapter_z3.ml`, `adapter_cvc4.ml`, `adapter_cvc5.ml` ×2) switch to it;
`try_close` itself is byte-identical, so the unit tests that pin its first-hit
order still pin exactly that.

## 3. Budget

Two caps, because the review was right that one of them bounds the wrong
thing.

**`max_exact_supports = 200_000`** bounds the SIZE OF THE SPACE, refusing with
`Exact_search_space_exceeded`. It admits IRs up to 47 columns; the largest in
this corpus is 22. Its counter is overflow-safe and stops as soon as the count
is known to exceed the cap (§1b.1).

**`max_exact_work = 12_000_000`** bounds the RUNNING TIME, refusing with
`Exact_search_work_exceeded`. The unit is `(rows + 1) · k² · bit_weight`
summed over the supports examined — Gaussian elimination on the support's
variable matrix, weighted by the size of the numbers in it. Rows are the
dimension the support cap misses entirely, and the review's IR (46 columns,
64-variable forms) is exactly the shape that exploits the gap.

Measured on both shapes, witness-free so the whole admitted space is swept
(`diag/exact_budget.ml`, output in `logs/exact_budget.txt`):

| | shape A: few variables per form | shape B: 64 variables per form |
|---|---|---|
| sweeps its whole space up to | 44 columns (103 ms) | 30 columns (792 ms) |
| first work refusal | 46 columns (111 ms) | 32 columns |
| first space refusal | 48 columns | 48 columns |
| worst observed wall time | 112 ms | 409 ms |

**387 ms is the worst time observed across both sweeps at this cap** — against
more than 30 seconds for shape B with no work guard at all. It is a measured
maximum on two shapes, **not a proven ceiling**: `bit_weight` is computed from
the input coefficients, so coefficient growth *during* elimination is not
captured, and a shape whose intermediate rationals blow up beyond its inputs
would cost more per work unit than either sweep shows. The constant's comment
in `farkas_search.ml` says this.

Both caps sit on a path that runs only after solver proof extraction *and* the
enumerating search have already failed, so they add to a failure path, never
to a success. Observed exact-recovery time on every corpus case: 0–1 ms.

## 4. Results

Pass `20260907-113052`, regenerated after the second review and **regenerated again** after the final one: the pass `20260906-233806` artifacts were destroyed by this campaign's own preflight self-test (§1c.1), and its damage record is kept at `runs/20260906-233806/DAMAGED/`. The
intervening regeneration `20260907-104934` is retained as
`runs/20260907-104934/COMPARISON.md` alone — binary hashes and the 182-run
comparison showing identical outcomes; its bulk outputs are omitted. Every diagnostic executable
was rebuilt and hashed by `tools/build_diag.sh` first
(`logs/diag_binaries.txt`), so nothing here comes from a binary that predates
the code it is reporting on.

**Neither the six fixes nor the two harness corrections changed a corpus
outcome.** Comparing all seven closers of all 26 cases against the last intact
full pass: zero differences, 182 runs. That is what
should happen — the fixes concern an overflow at column counts no corpus case
approaches, the cost of building matrices, and the gate's own correctness. The
Lean results were always produced against a correctly rebuilt FFI; it was the
*diagnostic artifacts* that were stale, and those are what is regenerated.

### 4.1 The primary gate: the four original carry obligations

| copy | closes | closers / tiers at sites 1–4 (pass 2) | tactic execution, whole file |
|---|---|---|---|
| `CarryLift` (omega) | 4/4 | — | 142 ms, 129 ms |
| `CarryLiftGrind` | 4/4 | — | 125 ms, 118 ms |
| `CarryLiftPB` | 4/4 | `gated_omega` ×4 | 870 ms, 913 ms |
| `CarryLiftPBTerm` | **4/4** | `term_mode_nat` ×4, all tier 1 farkas | 863 ms, 881 ms |

`carry_stage_lift_production` closes with
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no `native_decide`.
Site 2, which the completed VerInf case study records as refused, reconstructs.

### 4.2 Closure, by case and closer

`closed` = the closer closed the original goal and the file elaborated (probe EXIT=0). Everything else is that run's own named outcome; none of it is a counterexample.

The paired repair comparison uses the saved results from
[`20260906-204453`](../runs/20260906-204453/results.json) (pre-repair) and
[`20260907-113052`](../runs/20260907-113052/results.json) (final). They share
24 case IDs: 22 true obligations and two deliberately false controls. All
168 generated Lean files for those cases (24 × 7 closers) are byte-identical
between the two passes. Matching by case ID and closer gives:

| closer | pre-repair closures, same 24 cases | final closures, same 24 cases | recovered cases | regressions |
|---|---|---|---|---|
| `omega` | 22 | 22 | 0 | 0 |
| `grind` | 22 | 22 | 0 | 0 |
| `pb` | 20 | 20 | 0 | 0 |
| `pbterm` | 4 | 20 | 16 | 0 |
| `pbterm_z3` | 4 | 20 | 16 | 0 |
| `pbterm_cvc5` | 3 | 19 | 16 | 0 |
| `pbterm_cvc4` | 3 | 19 | 16 | 0 |

Thus term mode improves from **4/22 to 20/22 on the shared true obligations**;
neither false control closes. `V1_chain_support5` and `V2_chain_support7`
were added as preservation controls after the original pass. Both close in
the final pass, but neither has a row in that pre-repair run, so they are
reported separately from the 16 recoveries. The expanded corpus below has
26 cases (24 true, two false), of which term mode closes 22. The earlier
headline "22 (from 4 before the repair)" mixed these populations; this paired
comparison corrects that wording without changing either run's artifacts.

| case | truth | omega | grind | pb | pbterm | pbterm_z3 | pbterm_cvc5 | pbterm_cvc4 |
|---|---|---|---|---|---|---|---|---|
| `O5_site2_isolated` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `O6_E4` | TRUE | closed | closed | closed | closed | closed | refused(tier0) | refused(tier0) |
| `V1_chain_support5` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `V2_chain_support7` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C1_coef_1` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C2_coef_2` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C3_coef_3` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C4_coef_4` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C5_coef_5` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C6_coef_8` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C7_coef_2p10` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `C8_coef_2p18` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `P1_decimal_coef` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `P2_operand_order` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `P3_le_pred` | TRUE | closed | closed | refused(reify) | refused(reify) | refused(reify) | refused(reify) | refused(reify) |
| `P4_prime_literal` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `P5_plain_nat` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `P6_hyp_le` | TRUE | closed | closed | failed | refused(no cert) | refused(no cert) | refused(no cert) | refused(no cert) |
| `R1_reorder` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `R2_redundant3` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `R3_site2_in_context` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `R4_redundant6` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `B1_true_2p21` | TRUE | closed | closed | closed | closed | closed | closed | closed |
| `B2_false_2p22` | FALSE | failed | failed | failed | refused(no cert) | refused(no cert) | refused(no cert) | refused(no cert) |
| `B3_false_wide_bound` | FALSE | failed | failed | failed | refused(no cert) | refused(no cert) | refused(no cert) | refused(no cert) |
| `B4_true_exact` | TRUE | closed | closed | closed | closed | closed | closed | closed |

### 4.3 Where each certificate came from

`route`: **extracted** from the backend's own proof, **enumerated** by the bounded coefficient search, **exact** by exact support-bounded recovery, **none** if nothing produced one. It is not the same question as `minted tiers`: cvc5 may prefer its own tier-3 trace over a tier-1 witness it could also have produced, and the parallel driver then picks among the minted certs.

`need` is the largest multiplier in the smallest witness the existence probe found over the dispatched IR, re-checked by the SDK's own `Farkas.verify`. `route` is explained above.

| case | inputs | witness exists | support | need | z3 route | cvc5 route | cvc4 route | minted tiers | where lost |
|---|---|---|---|---|---|---|---|---|---|
| `O1` | 10 | witness_exists | 1 | 1 | enumerated | enumerated | enumerated | z3=t1 cvc5=t3 cvc4=t1 | —(recovered: z3 via enumerated) |
| `O2` | 13 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `O3` | 16 | witness_exists | 3 | 262144 | extracted | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via extracted) |
| `O4` | 21 | witness_exists | 2 | 1 | enumerated | extracted | enumerated | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via enumerated) |
| `O5_site2_isolated` | 4 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `O6_E4` | 11 | witness_exists | 6 | 68719214592 | extracted | none | none | z3=t1 cvc5=t0 cvc4=t0 | —(recovered: z3 via extracted) |
| `V1_chain_support5` | 5 | witness_exists | 5 | 1 | extracted | enumerated | enumerated | z3=t1 cvc5=t3 cvc4=t1 | —(recovered: z3 via extracted) |
| `V2_chain_support7` | 7 | witness_exists | 7 | 1 | extracted | enumerated | enumerated | z3=t1 cvc5=t3 cvc4=t1 | —(recovered: z3 via extracted) |
| `C1_coef_1` | 4 | witness_exists | 2 | 1 | enumerated | extracted | enumerated | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via enumerated) |
| `C2_coef_2` | 4 | witness_exists | 2 | 2 | enumerated | enumerated | enumerated | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via enumerated) |
| `C3_coef_3` | 4 | witness_exists | 2 | 3 | enumerated | enumerated | enumerated | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via enumerated) |
| `C4_coef_4` | 4 | witness_exists | 2 | 4 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `C5_coef_5` | 4 | witness_exists | 2 | 5 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `C6_coef_8` | 4 | witness_exists | 2 | 8 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `C7_coef_2p10` | 4 | witness_exists | 2 | 1024 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `C8_coef_2p18` | 4 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `P1_decimal_coef` | 4 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `P2_operand_order` | 4 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `P3_le_pred` | — | — | — | — | — | — | — | — | reification (no IR captured) |
| `P4_prime_literal` | 4 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `P5_plain_nat` | 4 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `P6_hyp_le` | 3 | no_witness_exists | — | — | none | none | none | z3=FAILED cvc5=FAILED cvc4=FAILED | backend search (z3=sat,cvc5=sat,cvc4=sat) |
| `R1_reorder` | 4 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `R2_redundant3` | 10 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `R3_site2_in_context` | 13 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `R4_redundant6` | 16 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `B1_true_2p21` | 4 | witness_exists | 2 | 2097152 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |
| `B2_false_2p22` | 4 | no_witness_exists | — | — | none | none | none | z3=FAILED cvc5=FAILED cvc4=FAILED | backend search (z3=sat,cvc5=sat,cvc4=sat) |
| `B3_false_wide_bound` | 4 | no_witness_exists | — | — | none | none | none | z3=FAILED cvc5=FAILED cvc4=FAILED | backend search (z3=sat,cvc5=sat,cvc4=sat) |
| `B4_true_exact` | 4 | witness_exists | 2 | 262144 | exact | exact | exact | z3=t1 cvc5=t1 cvc4=t1 | —(recovered: z3 via exact) |

### 4.4 A provenance shift, stated as the review asks

The per-backend routes did not degrade — no `extracted` route became internal.
But *which* certificate the tactic consumes did change: the four
`CarryLiftPBTerm` sites went from `cvc4 / — / z3 / cvc4` at checkpoint 1 to
`cvc4 / cvc4 / cvc4 / cvc4`. cvc4 has no proof-trace path at all, so **all four
consumed witnesses are now SDK-synthesized and then reconstructed in Lean**.

Stated plainly, and kept out of the headline: this work demonstrates
**certificate synthesis inside the SDK, followed by Lean reconstruction**. It
demonstrates **no improvement in solver-proof extraction**. The two extraction
gaps diagnosed at checkpoint 1 — G1 (z3's mixed-polarity Farkas clause) and G2
(integer-tightened literals that are not rescalings of the IR's) — are
untouched. z3's extracted witness for site 3 still exists, while the recorded
term-mode calls select cvc4's SDK-synthesized witness. That establishes which
evidence was consumed, but does not establish that cvc4 finished first.

[`Dispatch.run_parallel`](../../../sdk/lib/dispatch.ml) selects among
certificates available at its decision point, applying the caller's tier
preference, then numeric tier, then manifest input order. Equal-tier ties
therefore favor the earlier manifest, regardless of which certificate arrived
first. The stage tracer's separate sequential executions do not establish
completion order in the actual tactic calls. The earlier explanation that
z3 lost to a "faster backend" is withdrawn; attributing that selection to speed
would require arrival times and the selection state from the same episode.

### 4.5 Costs

Solver / extraction / fallback-search / Lean-side numbers are from different instruments and are NOT summable: the first three are the stage tracer's own timings of one sequential replay, the last two are the bridge's per-call report and Lean's profiler inside the probe. `n/a` = not measured.

The dispatch driver joins every spawned runner before returning, even after
its certificate selection is fixed. Consequently, `dispatch_ms` includes that
wait and does not measure the selected certificate's arrival time. This
campaign does not measure the decision time and subsequent join wait
separately. R6 should record certificate arrivals, manifest order, tier
preferences, the selection reason, decision time, and return time within the
same episode.

| case | z3 solve ms | z3 extract ms | enumerate ms | exact ms | `pbterm` dispatch ms | `pbterm` verify ms | `pbterm` tactic ms | `omega` tactic ms |
|---|---|---|---|---|---|---|---|---|
| `O5_site2_isolated` | 7 | 0 | 0 | 0 | 21 | 0 | 30.5 | 2.13 |
| `O6_E4` | 10 | 0 | 33 | 1 | 89 | 1 | 104.0 | 3.85 |
| `V1_chain_support5` | 8 | 0 | 0 | 0 | 22 | 1 | 26.9 | 2.05 |
| `V2_chain_support7` | 8 | 0 | 3 | 0 | 26 | 1 | 32.3 | 2.05 |
| `C1_coef_1` | 25 | 0 | 0 | 0 | 32 | 0 | 43.0 | 1.84 |
| `C2_coef_2` | 8 | 0 | 0 | 0 | 21 | 0 | 35.8 | 1.83 |
| `C3_coef_3` | 8 | 0 | 0 | 0 | 21 | 1 | 38.7 | 1.82 |
| `C4_coef_4` | 7 | 0 | 0 | 0 | 21 | 0 | 30.9 | 2.17 |
| `C5_coef_5` | 8 | 0 | 0 | 0 | 21 | 1 | 31.8 | 1.85 |
| `C6_coef_8` | 8 | 0 | 0 | 0 | 22 | 0 | 34.6 | 2.41 |
| `C7_coef_2p10` | 7 | 0 | 0 | 0 | 22 | 0 | 33.0 | 1.93 |
| `C8_coef_2p18` | 8 | 0 | 0 | 0 | 21 | 0 | 30.1 | 2.22 |
| `P1_decimal_coef` | 7 | 0 | 0 | 0 | 21 | 0 | 35.6 | 1.95 |
| `P2_operand_order` | 10 | 0 | 0 | 0 | 22 | 0 | 33.2 | 2.05 |
| `P3_le_pred` | n/a | n/a | n/a | n/a | n/a | n/a | 0.223 | 2.56 |
| `P4_prime_literal` | 8 | 0 | 0 | 0 | 21 | 0 | 34.4 | 1.75 |
| `P5_plain_nat` | 7 | 0 | 0 | 0 | 21 | 1 | 31.4 | 1.69 |
| `P6_hyp_le` | 9 | n/a | 0 | 0 | n/a | n/a | 27.4 | 1.59 |
| `R1_reorder` | 8 | 0 | 0 | 0 | 22 | 0 | 31.7 | 1.95 |
| `R2_redundant3` | 8 | 0 | 1643 | 0 | 5541 | 0 | 5550.0 | 3.89 |
| `R3_site2_in_context` | 7 | 0 | 57 | 0 | 216 | 0 | 227.0 | 3.59 |
| `R4_redundant6` | 13 | 0 | 95 | 0 | 325 | 1 | 338.0 | 2.58 |
| `B1_true_2p21` | 8 | 0 | 0 | 0 | 21 | 1 | 32.9 | 1.84 |
| `B2_false_2p22` | 10 | n/a | 3 | 0 | n/a | n/a | 28.8 | 0.953 |
| `B3_false_wide_bound` | 8 | n/a | 0 | 0 | n/a | n/a | 28.3 | 0.684 |
| `B4_true_exact` | 8 | 0 | 0 | 0 | 21 | 1 | 31.4 | 1.58 |

## 5. Held-out cases — out of sample

Defined at checkpoint 1, deliberately not run there, and run after the repair
was designed (`tools/run_heldout_broker.sh`, `logs/heldout_broker.txt`).

| case | truth | `omega` | `proof_broker` | `proof_broker_term` | predicted at checkpoint 1 |
|---|---|---|---|---|---|
| `H1_hyp_succ_form` | TRUE | closes | tier 1 | **closes**, tier 1 | reconstructs |
| `H2_coef_2p36` | TRUE | closes | tier 1 | **closes**, tier 1 | reconstructs |
| `H3_two_large_coefs` | TRUE | closes | tier 1 | **closes**, tier 1 | reconstructs |
| `H4_mixed_small_large` | TRUE | closes | tier 1 | **closes**, tier 1 | reconstructs |
| `H5_false_2p19` | FALSE | fails | fails | refused | refused with `sat` |
| `H6_other_limb_width` | TRUE | closes | tier 1 | **closes**, tier 1 | reconstructs |

Six for six against the prediction. `H3` is the sharpest: two multipliers at
once (`2^18·a + 2^36·b < P`), both far above the enumeration bound. `H5` is
false and every closer including `omega` declines it; its falsity comes from
`tools/truth_check.py`, not from those failures.

## 6. Negative checks

`tools/run_negchecks.sh`, now a gate that builds its own executables first.
**32 cases passed, 0 failures, exit 0.**

* **False goals** — `B2_false_2p22` and `B3_false_wide_bound` get
  `sat_returned` from all three adapters and mint nothing. Exact recovery
  manufactures nothing: on `B2` the tracer records `exact_search_exhausted`.
* **Corrupted certificates** — 28 cases carry a genuine tier 1 cert;
  **224 witness mutations**, and **both** shipped interfaces agree with the
  independently computed expectation on **224/224**, in both directions
  (`Farkas.verify` 224/224, `Verifier.verify` 224/224). 222 are classified
  `invalid_mutation` and all are rejected; 2 are `valid_transformation`
  (positive rescalings of a ground contradiction) and both are accepted, as a
  correct verifier must. Both envelope mutations are refused as
  `hash_mismatch` on the named field, in every case.

  The earlier figure of 56 mutations over 7 cases came from the stale binary
  and is superseded.
* **Fixtures** — `F1_lra_strict_ground` pins that a strict ground
  contradiction (`Lt(0)`) is the mutation target rather than a neighbouring
  vacuous `Eq(0)`; `F2_eq_negative_multiplier` pins that the ± column split
  really reaches a negative equality multiplier (`heq: -1`, verified).
* **Gate self-tests**, recorded in `logs/negcheck_gate_selftest.txt`, all
  exiting nonzero: a faulty executable (`NEGCHECK_BIN` stub exiting 42) → 1;
  a missing `logs/STAMP` → 2; an expectation generator that exits 42 → 2; one
  that succeeds but emits nothing → 2; a failing build preflight
  (`BUILD_DIAG` stub exiting 42) → 2; and a ledger whose recorded FFI hash no
  longer matches the shared object on disk → `probe.sh` exits 2 without
  invoking Lean. Separately, the review's injection forcing `Verified_farkas`
  for every mutant produces 8 violations and exit 1, and
  `tools/test_runner_preflight.sh` covers all five entry points
  (`logs/runner_preflight_selftest.txt`).
* **`P6_hyp_le`** is named on every run as a true goal on which all three
  adapters answered `sat` — because the reified IR was weakened, not because
  the goal is false.

## 7. Changes to shipped files

Everything else in the campaign directory is diagnostic and touches nothing the
SDK builds. These are the files under `sdk/` that changed.

| file | change |
|---|---|
| `sdk/lib/farkas_search.ml` | **additive.** `max_exact_support`, `max_exact_supports`, `max_exact_work`, three new error variants with their kind/detail strings, the column model, exact rational RREF and null space, `try_close_exact`, `try_close_then_exact`. `try_close` and everything it calls are untouched. |
| `sdk/lib/adapter_z3.ml` | one call site `try_close` → `try_close_then_exact`; ladder comment updated |
| `sdk/lib/adapter_cvc4.ml` | same, one call site |
| `sdk/lib/adapter_cvc5.ml` | same, two call sites |
| `sdk/test/test_farkas_search.ml` | **+9 tests**, a new `exact` group — see below |
| `sdk/test/test_adapter_z3.ml` | **a shipped test's expectation changed — see below** |
| `sdk/test/test_adapter_cvc4.ml` | same |
| `sdk/test/dune` | `unix` added (the work-cap test times its own refusal) |

**Eight files under `sdk/`**, not six: the four library files above plus
`test_farkas_search.ml`, `test_adapter_z3.ml`, `test_adapter_cvc4.ml` and
`dune`. The commit's scope is those eight plus
`experiments/c1-cert-recovery/`; the two-line `README.md` pointer to
`experiments/r6/`, and `experiments/r6/` itself, belong to a different
campaign and stay out.

Campaign tooling added for the preflight (all under
`experiments/c1-cert-recovery/`, none of it built by the SDK):
`tools/build_diag.sh` (+`--verify`), `tools/test_runner_preflight.sh`,
`tools/build_fault_stub.sh`, `tools/canary_probe.sh`,
`tools/expectations_fault_stub.sh`, `tools/make_fixtures.py`.

### The new tests

The `exact` group covers what the stage finds, what it refuses, and that it
changes nothing the enumerating search already did:

* finds a witness the enumeration cannot reach (the 262144 multiplier), and
  the witness verifies;
* a **negative multiplier on an equality** — the ± column split; a split that
  dropped the negative half would still pass every other case;
* **LRA strict with a zero constant residual** — the acceptance clause a
  positive-constant-only implementation would regress;
* refuses above the **support bound** (`exact_search_exhausted`);
* `support_count` **saturates and never goes negative**, up to `max_int / 2` —
  the overflow regression, with 47 admitted and 48 refused pinned;
* refuses above the **support-space cap** (`exact_search_space_exceeded`);
* refuses above the **work cap**, and does so promptly (asserted < 3 s) — the
  wide-row shape the support cap alone admits;
* `try_close_then_exact` returns the **enumerated witness byte for byte**
  where the enumeration succeeds — the additivity property;
* and reaches the exact stage where it does not.

### The two changed tests, called out deliberately

`test_dispatch_unsat_beyond_closer_bound_falls_back_to_oracle` (z3 and cvc4)
pinned that `7n ≤ 6 ∧ 1 ≤ n ⊢ False` — witness coefficient 7, above the
enumeration bound — **degrades to a Tier 0 oracle**. That is the limitation
this work removes, so each is split in two: the same IR now asserts tier 1 +
`Verified_farkas`, and a new test pins that exceeding *both* closers still
degrades to Tier 0 (support 6 **and** coefficient 7, so neither reaches it).
`test_farkas_search.ml`'s pre-existing pins on `try_close`'s first-hit order
and on `~bound:0` exhausting are untouched and still pass.

Full SDK suite green (`dune build @sdk/test/runtest --force`).

## 8. Reproduction

```bash
cd experiments/c1-cert-recovery

# Builds sdk/ffi, sdk/lib and the three diagnostic executables, and records
# their hashes. Every entry point runs this itself and refuses to proceed if it
# fails, so this line is for the ledger, not for correctness.
tools/build_diag.sh
tools/test_runner_preflight.sh                         # that refusal, tested
                                                       # (runs in temporary
                                                       # campaigns; asserts the
                                                       # real one is untouched)
tools/baseline.sh > baseline/artifacts-c2-before.txt   # hashes, not HEADs

(cd ../.. && dune build @sdk/test/runtest --force)     # SDK suite
../../_build/default/experiments/c1-cert-recovery/diag/exact_budget.exe 50 \
  > logs/exact_budget.txt                              # the budget sweep

date +%Y%m%d-%H%M%S > logs/STAMP
python3 tools/gen.py runs/$(cat logs/STAMP)
tools/probe.sh ir/CarryLiftDump.lean > logs/ir_carrylift_dump.log 2>&1
tools/capture_ir.sh > logs/capture_ir.txt              # IR capture + stage trace
tools/run_carrylift.sh > logs/carrylift.txt            # the four-copy comparison
python3 tools/run.py runs/$(cat logs/STAMP)            # 26 cases x 7 closers
tools/run_heldout_broker.sh > logs/heldout_broker.txt  # out-of-sample, run ONCE
tools/run_negchecks.sh                                 # the gate; exits nonzero on failure
python3 tools/summarize.py runs/$(cat logs/STAMP)
tools/baseline.sh > baseline/artifacts-c2-after.txt
```

Gate self-test (must exit nonzero, both of them):

```bash
NEGCHECK_BIN=tools/negcheck_fault_stub.sh tools/run_negchecks.sh ; echo $?
mv logs/STAMP /tmp/ && tools/run_negchecks.sh ; echo $? ; mv /tmp/STAMP logs/
```

The single case, before and after:

```bash
tools/probe.sh runs/<stamp>/lean/O5_site2_isolated.pbterm.lean
../../_build/default/experiments/c1-cert-recovery/diag/diag.exe \
    ir/O5_site2_isolated.json /tmp O5      # .backends.z3.fallback_search.route
```

## 9. Remaining uncertainties

1. **The completeness argument rests on the extreme-ray decomposition, which
   is standard but is not machine-checked here.** The claim "if any witness
   exists, some extreme ray is a witness" is proved in §2 in two lines and the
   implementation follows it, but nothing in the campaign verifies the
   implementation against an independent LP over the same inputs on a broad
   input distribution. What *is* checked, on every corpus case, is that the
   witness exact recovery emits passes the SDK's own `Farkas.verify` — so a
   bug here costs recall, never soundness.

2. **The support bound is inherited, not derived.** `max_exact_support = 4`
   was chosen to match the sparse rescue's existing bound, and the corpus
   happens to need at most 3. Nothing here establishes that 4 is the right
   number for obligations outside this family, and the budget measurement
   shows the cap is not what constrains it — raising the support bound would
   raise the support count combinatorially, which is the real limit.

3. **Which certificate wins has shifted, and that is a provenance change, not
   only a recall change.** See §4: with exact recovery available, cvc4 — which
   has no proof-trace path at all — now supplies the consumed tier-1 witness
   at site 3, where z3's *extracted* witness was previously consumed. This
   change follows the recorded selections; it does not establish a speed
   advantage, because equal-tier ties use manifest order (§4.4). All four
   consumed carry-site witnesses are now derived by the SDK. Selection policy
   therefore affects evidence provenance and needs to be recorded explicitly.

4. **Checkpoint 1's §9.1 experiment is still not run.** Why z3 emits the
   mixed-polarity clause shape for single-variable conflicts and the direct
   shape otherwise remains an observed pattern. It matters less now — exact
   recovery does not depend on the solver's proof shape — but it is still the
   open question behind the extraction gaps G1 and G2, which are untouched.

5. **The corpus is still one obligation family.** Every non-`V` case is a
   range-check bound over the Goldilocks prime. The held-out set (§5) is
   out-of-sample only in the sense that it was written before the repair and
   run once after it; it is drawn from the same family.

6. **`P6_hyp_le` is unchanged and remains tracked separately.** A true goal
   whose range check the reifier drops (truncated ℕ subtraction) still reaches
   the solvers as a weakened IR and still comes back `sat`. Nothing in this
   work touches it; `tools/run_negchecks.sh` names it on every run so it
   cannot quietly become normal.
