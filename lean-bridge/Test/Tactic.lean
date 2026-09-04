/-
End-to-end tactic-elaboration tests for `ProofBroker.proof_broker`.

Each `example` below is a real Lean goal closed by the broker:
the tactic reifies the goal + Prop hypotheses into a LIA IR, hands
it to `runDispatchBroker` (consulting the cvc4/cvc5/z3 manifests
under `examples/`), re-checks the minted Tier 1 Farkas cert via
`runVerifyCertificate`, and closes the goal — for the LIA Tier 1
case via core Lean's `omega` (axiom-free, gated on cert
verification), for other fragments via an axiom-free closer
(`decide`/`subst_eqs`/`linarith`); a certified goal with no
sound closer is a tactic failure, never an admitted theorem
(audit H1 — the former trust axiom was removed).

Build success of this library *is* the test: any failure to
elaborate `by proof_broker` (no available adapter, cert that
fails to re-verify, reified IR shape outside the LIA fragment)
fails the build. The library has no precompile output and is
not imported by anything else; its sole purpose is to exercise
the elaboration-time FFI path.

Pre-condition: the test must be invoked with cwd =
`lean-bridge/`, so that the tactic's manifest loader finds
`../examples/manifest-{cvc4,cvc5,z3}.json`. Override via the
`PROOF_BROKER_EXAMPLES_DIR` env var if needed.
-/

import ProofBroker

-- The broker closes the goal with an axiom keyed on the goal
-- proposition; the resulting proof term doesn't textually mention
-- the hypotheses that were Farkas-combined inside the cert, so
-- Lean's unused-variable linter would otherwise flag every test.
set_option linter.unusedVariables false

namespace ProofBroker.Test

/-- Closed-form Farkas: `n + m = 10` and `0 ≤ m` together force `n ≤ 10`.
    Coefficients (h1=1, h3=1, neg_goal=1) sum to a contradiction. -/
example (n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker

/-- Single-hypothesis bound transfer. -/
example (n : Int) (h : n ≤ 5) : n ≤ 10 := by
  proof_broker

/-- Trivial transitive case. -/
example (a b c : Int) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  proof_broker

/-- Equality propagated through addition. -/
example (x y : Int) (h : x = y) : x + 1 ≤ y + 1 := by
  proof_broker

/-- Adapter-list syntax: restrict dispatch to a single adapter. -/
example (n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker [cvc5]

/-- Adapter-list syntax with order: input order is respected
    (preferHigherTier=false), so cvc4 is tried first even though
    cvc5 has a higher max-tier capability. -/
example (n : Int) (h : n ≤ 5) : n ≤ 10 := by
  proof_broker [cvc4, cvc5]

/-- Verbose form: `proof_broker?` emits a `logInfo` summary of the
    extraction path (IR shape, dispatch attempts + timing, cert
    tier/format, verify outcome) and then closes the goal as
    normal. The build will print one info line per invocation. -/
example (n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker? [cvc4]

/-- Named LIA goal proven via the default `proof_broker` form,
    which `preferHigherTier := true` floats to cvc5's Tier 3
    alethe-2024 path. The Lean-side Alethe walker now elaborates
    the trace into a kernel proof term ("cert IS the proof") —
    this is the first test in the suite where a real cvc5
    dispatch closes walker-first rather than via the omega
    fallback. Footprint is `[propext, Classical.choice,
    Quot.sound]` because cvc5's trace uses boolean-cleanup rules
    (`equiv_pos1` / `equiv_pos2`) whose proof terms invoke
    `Classical.em`; same classical baseline as the
    `proof_broker_term` paths. Verified inline by `#print axioms`
    below. -/
theorem lia_axiom_free
    (n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker

#print axioms lia_axiom_free

/-- End-to-end production path through the Alethe walker, walker-STRICT.

    `proof_broker_walker` runs the full live pipeline (reify →
    dispatch to cvc5 → verify) and then closes ONLY via
    `walkProofIntoGoal` on the minted cert, with NO `omega` fallback.
    `lia_axiom_free` above uses plain `proof_broker`, whose
    `walker-then-omega` order silently masks any regression in the
    LIVE walker path (cert shape, trace extraction, the walk); this
    removes the mask, so a green build proves the walker reconstructs
    a *real* live cvc5 cert into a kernel term — not a committed
    fixture (the corpus replay covers that). Same classical-baseline
    footprint as `lia_axiom_free`; that the footprint is non-empty
    (vs `omega`'s axiom-free closure) is itself corroboration the
    walker, not a fallback, produced the term. -/
theorem lia_walker_live_axiom_free
    (n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker_walker

#print axioms lia_walker_live_axiom_free

/-- Same theorem pinned through cvc4 (Tier 1 Farkas) — confirms
    the dispatch-on-fragment closer doesn't regress on the
    original Tier 1 path that motivated the omega-based closure
    in the first place. -/
theorem tier1_lia_axiom_free
    (n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m) : n ≤ 10 := by
  proof_broker [cvc4]

#print axioms tier1_lia_axiom_free

/-- BV vertical-slice gate: a closed `BitVec 8` arithmetic
    equality routes through the broker (QF_BV → cvc5/z3 oracle
    → cert-gated `decide`). The broker is overkill for a trivially
    decidable goal — the architectural payoff is showing the BV
    pipeline runs end-to-end (reifier emits `BitVec(8)` / `BV.add`,
    SMT-LIB serializer emits `(_ bv5 8)` / `bvadd`, the cvc5 / z3
    adapter dispatches under QF_BV, the verifier envelope-checks,
    the closer fires `decide`). `decide` is axiom-free, so this
    theorem's transitive axiom set should match the LIA path's
    `[propext, Quot.sound]` (or fewer) — verified by `#print
    axioms` below. -/
theorem bv_axiom_free : (5 : BitVec 8) + 3 = 8 := by
  proof_broker

#print axioms bv_axiom_free

/-- BV comparison ops (`<` / `<=`) over `BitVec` resolve to the
    unsigned variants in Lean's typeclass setup, so the reifier
    emits `BV.ult` / `BV.ule` rather than the polymorphic `LT.lt`
    / `LE.le`. The closer's `decide` path discharges this just as
    cleanly as the additive case. -/
theorem bv_compare_axiom_free : (3 : BitVec 8) < 5 := by
  proof_broker

#print axioms bv_compare_axiom_free

/-- Term-mode Tier 1 Farkas: `5 ≤ x ∧ x ≤ 3 ⊢ False`. Pinned through
    `[z3]` because z3 mints native Tier 1 Farkas certs (cvc5 mints
    Tier 3 alethe-2024 which the term builder doesn't yet consume,
    cvc4 mints Tier 0 oracle). The closer reads the witness's
    coefficients and applies `farkasContradict` from
    `ProofBroker.TermMode`; only the strictly-positive
    linear-combination subgoal goes through `omega` (a narrower
    role than the LIA closer's full goal-discharge omega call).
    Mirror of Rocq's `pb_term_axiom_free`. -/
theorem pb_term_axiom_free
    (x : Int) (h1 : 5 ≤ x) (h2 : x ≤ 3) : False := by
  proof_broker_term [z3]

#print axioms pb_term_axiom_free

/-- Term-mode arity-3 Tier 1 Farkas. The fold-based closer builds
    `c1*a1 + c2*a2 + c3*a3 ≤ 0` step by step via
    `Int.mul_nonpos_of_nonneg_of_nonpos` + `Int.add_nonpos`, then
    applies `farkasContradictN` to discharge the strict-positivity
    with `omega`. Lifts the closer's arity ceiling from 2 to N
    (every entry in the witness flows through as an explicit Int
    literal coefficient in the proof term). z3 mints the
    3-coefficient Farkas witness for this transitive chain. Mirror
    of Rocq's `pb_term_arity3_axiom_free`. -/
theorem pb_term_arity3_axiom_free
    (x y : Int) (h1 : 5 ≤ x) (h2 : x ≤ y) (h3 : y ≤ 3) : False := by
  proof_broker_term [z3]

#print axioms pb_term_arity3_axiom_free

/-- Term-mode Tier 1 Farkas with a non-`False` goal. The witness
    has one real-hypothesis entry plus a `neg_goal` slot the closer
    discharges via the unified `intLeViaLt` wrapper (which wraps
    `Decidable.byContradiction` over `Int.decLe`, axiom-free) then
    folds into the arity-N False-fold. The cert minted by z3 carries
    coefficients on both `h` and `neg_goal`; the closer builds the
    proof term explicitly, omega-discharging only the strict-
    positivity polynomial identity. The `[propext, Quot.sound]`
    footprint matches the omega-closure path — no `Classical.choice`. -/
theorem pb_term_goal_axiom_free
    (n : Int) (h : n ≤ 5) : n ≤ 6 := by
  proof_broker_term [z3]

#print axioms pb_term_goal_axiom_free

/-- Term-mode with strict-`<` goal: closer routes through the
    `intLtViaLe` wrapper into the arity-N fold (no LIA +1 trick —
    `¬(n < 5) ↔ 5 ≤ n` via `Int.not_lt`). -/
theorem pb_term_lt_axiom_free
    (n : Int) (h : n ≤ 4) : n < 5 := by
  proof_broker_term [z3]

#print axioms pb_term_lt_axiom_free

/-- Term-mode with `≥` goal: `GE.ge n 4` reduces by instance to
    `LE.le 4 n`, so the closer routes through `intLeViaLt` with arg
    swap and the resulting `4 ≤ n` proof term unifies with the
    `n ≥ 4` goal definitionally. -/
theorem pb_term_ge_axiom_free
    (n : Int) (h : 5 ≤ n) : n ≥ 4 := by
  proof_broker_term [z3]

#print axioms pb_term_ge_axiom_free

/-- Term-mode with strict-`>` goal: `GT.gt n 3` reduces to
    `LT.lt 3 n`; same routing as `≥` but through `intLtViaLe`. -/
theorem pb_term_gt_axiom_free
    (n : Int) (h : 5 ≤ n) : n > 3 := by
  proof_broker_term [z3]

#print axioms pb_term_gt_axiom_free

/-- Term-mode with strict-`<` hypotheses (no comparison goal). The
    normalizer routes each `h : a < b` through `ltToLe0` (LIA +1
    trick: `(a + 1) - b ≤ 0`), then the False-goal fold runs as
    usual. Two strict hypotheses → witness `[(h1, 1), (h2, 1)]`,
    residual `K = 2`. Mirror of Rocq's `pb_term_lt_hyp_axiom_free`.
    `Int.add_one_le_of_lt` + `Int.sub_nonpos_of_le` (the building
    blocks of `ltToLe0`) are axiom-free, so closure stays at
    `[propext, Quot.sound]`. -/
theorem pb_term_lt_hyp_axiom_free
    (x : Int) (h1 : 5 < x) (h2 : x < 5) : False := by
  proof_broker_term [z3]

#print axioms pb_term_lt_hyp_axiom_free

/-- Term-mode mixing strict and non-strict hypotheses on a transitive
    chain. Strict `0 < x` and `y < 1` use the +1 trick; non-strict
    `x ≤ y` uses plain `leToLe0`. Demonstrates that the fold treats
    them uniformly once normalized — the witness arity rises to 3
    (`farkasContradictN`'s territory) and coefficients flow through
    explicitly. -/
theorem pb_term_lt_mixed_axiom_free
    (x y : Int) (h1 : 0 < x) (h2 : x ≤ y) (h3 : y < 1) : False := by
  proof_broker_term [z3]

#print axioms pb_term_lt_mixed_axiom_free

/-- Term-mode with equality goal: the closer pre-splits via
    `Int.le_antisymm` (since `¬(a = b)` is a disjunction outside
    single-witness Farkas scope) and runs the existing ≤-shape
    term-mode on each direction. Two solver dispatches, two
    `intLeViaLt`-routed applications, one `Int.le_antisymm`. The
    axiom footprint stays `[propext, Quot.sound]` — splitting adds
    no new trust delta over the single-direction case. -/
theorem pb_term_eq_axiom_free
    (n : Int) (h1 : n ≤ 5) (h2 : 5 ≤ n) : n = 5 := by
  proof_broker_term [z3]

#print axioms pb_term_eq_axiom_free

/-- Arity-3 comparison goal (LIA, Le): transitive chain
    `x ≤ y ∧ y ≤ 5 ⊢ x ≤ 6`. The unified closer applies
    `intLeViaLt`, introduces `neg_goal : 6 < x`, and feeds the
    full arity-3 witness (h1 + h2 + neg_goal) through the existing
    arity-N False-fold. No special arity-2 helper involved — same
    code path as the False-goal arity-3 test, just with one extra
    Le entry coming from the (+1-trick-normalized) neg_goal. -/
theorem pb_term_arity3_goal_axiom_free
    (x y : Int) (h1 : x ≤ y) (h2 : y ≤ 5) : x ≤ 6 := by
  proof_broker_term [z3]

#print axioms pb_term_arity3_goal_axiom_free

/-- Arity-3 comparison goal (LIA, Lt): same shape with strict goal.
    Wrapper is `intLtViaLe`, neg_goal compiles as Le (no +1 trick on
    the `c ≤ b` negation of `b < c`). -/
theorem pb_term_arity3_lt_axiom_free
    (x y : Int) (h1 : x ≤ y) (h2 : y ≤ 4) : x < 5 := by
  proof_broker_term [z3]

#print axioms pb_term_arity3_lt_axiom_free

/-- Eq hypothesis in the witness: `(h1 : x = 5) (h2 : x ≤ 3) ⊢ False`.
    Solver-emitted certs combine Eq hypotheses with signed coefficients
    to capture both directions of the equality in a single witness slot.
    For this goal the natural cert is `[(h1, -1), (h2, 1)]` with
    residual K = 2 — the Eq contribution is 0 symbolically (since
    `x - 5 = 0` from h1) but the linear-form combination needs the
    Eq slot to cancel `x` against h2.

    The closer pre-processes the signed coefficient: `c = -1` on an
    Eq hyp triggers the flipped direction (`5 - x ≤ 0` via `eqToLe0Flipped`)
    with `|c| = 1` as the positive coefficient in the fold. The rest
    of the path is identical to the inequality-only case. -/
theorem pb_term_eq_hyp_axiom_free
    (x : Int) (h1 : x = 5) (h2 : x ≤ 3) : False := by
  proof_broker_term [z3]

#print axioms pb_term_eq_hyp_axiom_free

/-- Not-hypothesis in the witness: `(h1 : ¬(x ≤ 5)) (h2 : x ≤ 3) ⊢ False`.
    `¬(x ≤ 5)` semantically means `x > 5`. Combined with `h2 : x ≤ 3`,
    contradiction. The closer routes the Not hypothesis through
    `notLeToLe0` to get `(5 + 1) - x ≤ 0 = 6 - x ≤ 0` (LIA +1 trick on
    the strict `5 < x` derived from the negation), then folds with h2's
    `x - 3 ≤ 0` to produce a strictly-positive sum `6 - x + x - 3 = 3
    > 0`. Trust footprint: `[propext, Quot.sound]` from omega-closed
    polynomial-identity subgoals; the Not helpers themselves are
    axiom-free via omega. -/
theorem pb_term_not_hyp_axiom_free
    (x : Int) (h1 : ¬(x ≤ 5)) (h2 : x ≤ 3) : False := by
  proof_broker_term [z3]

#print axioms pb_term_not_hyp_axiom_free

/-- UF vertical-slice gate: a congruence-style goal with an
    uninterpreted function `f : Int → Int` and an equality hypothesis
    routes through the broker (QF_UFLIA → cvc5 oracle → cert-gated
    `subst_eqs; rfl` closer). The reifier walks the function-typed
    free var into the IR's free_vars list with `ty = "Int->Int"`,
    the SDK serializer emits `(declare-fun f (Int) Int)` plus
    `(f x)` / `(f y)` use sites, the verifier envelope-checks, and
    the closer's `subst h; rfl` chain discharges constructively.
    `subst_eqs` is axiom-free; this theorem's transitive axiom set
    matches the LIA / BV paths' [propext, Quot.sound] (or fewer). -/
theorem uf_axiom_free
    (f : Int → Int) (x y : Int) (h : x = y) : f x = f y := by
  proof_broker

#print axioms uf_axiom_free

/-- Multi-arg UF: a binary uninterpreted function. Reifier walks
    `Int → Int → Int` into the type-ref `"Int->Int->Int"` and the
    SDK's `parse_arrow_type` splits to `(declare-fun f (Int Int) Int)`.
    Closer: `subst_eqs` rewrites `b → a`, leaving `f a a = f a a`
    for `rfl`. -/
theorem uf_two_arg_axiom_free
    (f : Int → Int → Int) (a b : Int) (h : a = b) : f a b = f a a := by
  proof_broker

#print axioms uf_two_arg_axiom_free

/-- Composed / nested UF: function composition `f (g x)` with an
    equality hypothesis. Reifier emits nested `App "UF.f" [App "UF.g" [x]]`;
    closer chain (`subst_eqs; rfl`) handles the depth uniformly. -/
theorem uf_composed_axiom_free
    (f g : Int → Int) (x y : Int) (h : x = y) : f (g x) = f (g y) := by
  proof_broker

#print axioms uf_composed_axiom_free

/-- Predicate-valued UF: `P : Int → Prop`, modus-ponens-style goal.
    Exercises the reifier on `Prop` as an arrow codomain (SDK maps to
    `Bool`) and the closer on a non-equality goal. -/
theorem uf_predicate_axiom_free
    (P : Int → Prop) (x y : Int) (hp : P x) (h : x = y) : P y := by
  proof_broker

#print axioms uf_predicate_axiom_free

/- ============================================================
   LLM-as-backend (roadmap §Phase 3 #3) — home-side replay closer.

   `Adapter_llm` fail-closes without `PROOF_BROKER_LLM_ENDPOINT`,
   so the live broker path can't run in CI. `llm_replay_test`
   drives the *exact* `replayLlmScriptOrFail` closer the broker
   uses for an LLM `lean-tactic-script` cert, feeding the string
   as the cert payload — no network, no model. These tests pin the
   audit-H1 contract: a script the home kernel accepts under the
   classical footprint closes the goal; a `sorry`/`native_decide`/
   non-closing/unparsable script is a tactic FAILURE, never an
   admitted theorem.
   ============================================================ -/

/-- Positive: a script the kernel independently accepts (axiom-free
    `omega`) closes the goal via the LLM-replay path. The proof
    term is produced by Lean, not the cert (audit H1). -/
theorem llm_replay_axiom_free (n : Int) (h : n + 1 = 3) : n = 2 := by
  llm_replay_test "omega"

#print axioms llm_replay_axiom_free

/-- audit H1: a hallucinated `sorry` "closes" the goal but the
    replay gate sees `sorryAx` outside the classical allowlist,
    throws, and the goal is never admitted (`fail_if_success`
    confirms the tactic errored; `rfl` then closes it honestly). -/
example : (1 : Int) = 1 := by
  fail_if_success (llm_replay_test "sorry")
  rfl

/-- audit H1: `native_decide` is compiler trust (`Lean.ofReduceBool`,
    not kernel-checked) — REJECTED even though it would "close" the
    goal. -/
example : (2 + 2 : Nat) = 4 := by
  fail_if_success (llm_replay_test "native_decide")
  rfl

/-- A script that runs without error but does not discharge the
    goal is a tactic failure (goal left OPEN), not a silent pass. -/
example : (1 : Int) = 1 := by
  fail_if_success (llm_replay_test "skip")
  rfl

/-- A script that doesn't parse as a Lean `by` block is a tactic
    failure, not an admitted theorem. -/
example : True := by
  fail_if_success (llm_replay_test "@@@ not lean @@@")
  trivial

/- ============================================================
   LLM-assisted Tier-3 reconstruction (roadmap §Phase 3 #4).

   `llm_reconstruct_test "<traceFmt>" "<script>"` simulates a
   successful `llm_translate_trace` FFI call (an LLM was asked to
   translate an un-replayable Tier-3 trace and returned the
   script) and routes the candidate through the SAME audit-H1
   gate the production fallback uses. The translation step itself
   is a pure I/O wrapper around an untrusted oracle — no soundness
   contribution — so swapping the live FFI for a literal script is
   faithful to what's actually being tested: that a candidate
   script makes it through `replayReconstructedScript` →
   `replayLlmScriptOrFail`, with the audit-H1 gate firing
   identically.
   ============================================================ -/

/-- Positive: a translated script the kernel independently
    accepts under the classical footprint (axiom-free `omega`)
    closes the goal via the reconstruction fallback's replay
    closer. The build log carries the
    `closed via LLM Tier-3 reconstruction ...` audit line. -/
theorem llm_reconstruct_axiom_free
    (n : Int) (h : n + 1 = 3) : n = 2 := by
  llm_reconstruct_test "alethe-2024" "omega"

#print axioms llm_reconstruct_axiom_free

/-- audit H1: a hallucinated `sorry` "translation" closes the
    goal but the audit gate rejects `sorryAx`; the tactic
    fails so the goal is left OPEN. -/
example : (1 : Int) = 1 := by
  fail_if_success (llm_reconstruct_test "tstp-fof" "sorry")
  rfl

/-- audit H1: a `native_decide` translation routes through the
    compiler-trust axiom `Lean.ofReduceBool`, which is outside
    the classical allowlist — rejected. -/
example : (2 + 2 : Nat) = 4 := by
  fail_if_success (llm_reconstruct_test "alethe-2024" "native_decide")
  rfl

/-- A translation that doesn't actually close the goal is a
    tactic failure, never a silent pass. -/
example : (1 : Int) = 1 := by
  fail_if_success (llm_reconstruct_test "alethe-2024" "skip")
  rfl

/- ============================================================
   Alethe walker (M1.β — clausal layer).

   `alethe_walker_test "<trace>"` parses a hand-written
   alethe-2024 trace via the SDK FFI and walks it into a kernel
   proof term — the "cert IS the proof" play for Tier-3
   alethe-2024 certs. M1.β covers the clausal rules (assume /
   resolution / or / false); the arithmetic and equality rule
   clusters land in follow-up PRs. Build success is the test:
   the walker must produce a well-typed proof term the kernel
   accepts. -/

/-- Clausal walker: `A` and `¬A` in scope resolve to the empty
    clause (`False`). The walker reconstructs the proof term
    `hNA hA` from the trace's `assume` + `resolution` steps —
    no decision procedure, no axiom. -/
theorem alethe_walker_clausal_axiom_free
    (A : Prop) (hA : A) (hNA : ¬A) : False := by
  alethe_walker_test
    "( (assume a0 A) (assume a1 (not A)) \
       (step t0 (cl) :rule resolution :premises (a0 a1)) )"

#print axioms alethe_walker_clausal_axiom_free

/-- Same, with the resolution premises in the opposite order —
    exercises the `elabResolution` symmetric branch (premise
    order in the trace is not fixed). -/
theorem alethe_walker_clausal_flipped_axiom_free
    (P : Prop) (hP : P) (hNP : ¬P) : False := by
  alethe_walker_test
    "( (assume a0 (not P)) (assume a1 P) \
       (step t0 (cl) :rule resolution :premises (a0 a1)) )"

#print axioms alethe_walker_clausal_flipped_axiom_free

/- Alethe walker — arithmetic layer (`la_generic` / `la_mult_neg`).

   These rules are LIA-tautology *leaves*: the step's clause is a
   linear-arithmetic tautology, discharged by a scoped `omega`
   call (the walker reconstructs the proof skeleton from the
   cert; the arithmetic leaves are decided). cvc5 emits
   `la_generic` clauses as disjunctions whose negation is
   LIA-unsat. -/

/-- `la_generic` leaf producing a one-literal unconditional
    tautology clause: `0 ≤ 5`. The walker discharges it via
    omega; the proof term is omega's, footprint
    `[propext, Quot.sound]`. -/
theorem alethe_walker_la_generic_lit : (0 : Int) ≤ 5 := by
  alethe_walker_test
    "( (step t0 (cl (<= 0 5)) :rule la_generic :args ()) )"

#print axioms alethe_walker_la_generic_lit

/-- `la_generic` leaf producing a multi-literal disjunction
    clause — the shape cvc5 actually emits. `¬(x ≥ 3) ∨ (x ≥ 1)`
    is a conditional LIA tautology (its negation
    `x ≥ 3 ∧ x < 1` is unsat). Exercises the `cl`→`∨` chaining
    in `sexpToExpr` and omega's negated-disjunction hypothesis
    handling. -/
theorem alethe_walker_la_generic_disj (x : Int) :
    ¬(x ≥ 3) ∨ (x ≥ 1) := by
  alethe_walker_test
    "( (step t0 (cl (not (>= x 3)) (>= x 1)) \
        :rule la_generic :args (1/1 1/1)) )"

#print axioms alethe_walker_la_generic_disj

/- Alethe walker — multi-literal resolution.

   `resolution` is now n-ary: a left-fold of binary resolutions,
   each cancelling one complementary literal pair (the walker
   finds the pivot; cvc5 does not list it). Intermediate
   resolvents can carry several literals — the proof term is the
   `Or.elim` cascade `casesClause` builds, with each non-pivot
   literal injected into the resolvent by `injectLit`. -/

/-- Three-clause propositional refutation exercising the full
    resolution machinery: `or` flattens the disjunctive assumes
    into clauses; `t2` resolves two 2-literal clauses into the
    2-literal resolvent `B ∨ C`; `t3`/`t4` chain down to the
    empty clause. Closes `False` axiom-free — the proof term is
    the reconstructed `Or.elim` cascade, no decision procedure. -/
theorem alethe_walker_resolution_axiom_free
    (A B C : Prop)
    (hAB : A ∨ B) (hAC : ¬A ∨ C) (hnB : ¬B) (hnC : ¬C) : False := by
  alethe_walker_test "( \
    (assume a0 (or A B)) \
    (assume a1 (or (not A) C)) \
    (assume a2 (not B)) \
    (assume a3 (not C)) \
    (step t0 (cl A B) :rule or :premises (a0)) \
    (step t1 (cl (not A) C) :rule or :premises (a1)) \
    (step t2 (cl B C) :rule resolution :premises (t0 t1)) \
    (step t3 (cl C) :rule resolution :premises (t2 a2)) \
    (step t4 (cl) :rule resolution :premises (t3 a3)) )"

#print axioms alethe_walker_resolution_axiom_free

/-- Double-negation resolution pivot: a negated literal `¬P` must
    resolve against its complement `¬¬P` (`= (not ¬P)`). The pivot
    search compares literal forms syntactically — `negateLit` would
    strip `¬P` to `P` and miss the `¬¬P` partner. This is the shape
    of `uf_lia_mix`'s `t38`. Axiom-free. -/
theorem alethe_walker_resolution_double_neg_axiom_free
    (P : Prop) (h0 : ¬P) (h1 : ¬¬P) : False := by
  alethe_walker_test
    "( (assume a0 (not P)) \
       (assume a1 (not (not P))) \
       (step t0 (cl) :rule resolution :premises (a0 a1)) )"

#print axioms alethe_walker_resolution_double_neg_axiom_free

/- Alethe walker — equality cluster (`refl` / `symm` / `trans` /
   `cong`).

   These rules are how cvc5's `alethe-2024` walks
   uninterpreted-function and equality reasoning. None of them
   touch a decision procedure (unlike `la_generic`): the proof
   term is reconstructed kernel-side from the premise proofs
   directly, so the resulting theorems are axiom-free (no
   `propext` / `Classical.choice`, just `Eq.rec` underneath). -/

/-- `refl`: a leaf rule concluding `t = t` for any `t`. No
    premises, just `Eq.refl t`. -/
theorem alethe_walker_refl_axiom_free (a : Int) : a = a := by
  alethe_walker_test
    "( (step t0 (cl (= a a)) :rule refl) )"

#print axioms alethe_walker_refl_axiom_free

/-- `symm`: flips an equality. Premise `a = b`, conclusion
    `b = a`; proof term is `Eq.symm h`. -/
theorem alethe_walker_symm_axiom_free
    (a b : Int) (h : a = b) : b = a := by
  alethe_walker_test
    "( (assume a0 (= a b)) \
       (step t0 (cl (= b a)) :rule symm :premises (a0)) )"

#print axioms alethe_walker_symm_axiom_free

/-- `trans`: chains equalities. Premises `a = b`, `b = c`;
    conclusion `a = c`; proof term is the left-fold of
    `Eq.trans`. Exercises the n-ary premise list. -/
theorem alethe_walker_trans_axiom_free
    (a b c : Int) (h1 : a = b) (h2 : b = c) : a = c := by
  alethe_walker_test
    "( (assume a0 (= a b)) \
       (assume a1 (= b c)) \
       (step t0 (cl (= a c)) :rule trans :premises (a0 a1)) )"

#print axioms alethe_walker_trans_axiom_free

/-- `cong` over a unary UF symbol: `x = y ⊢ f x = f y`. The
    walker's generic application case translates `(f x)` /
    `(f y)` by looking up `f` in the local context; the proof
    term is `mkCongr (Eq.refl f) h` — i.e., `congrArg f h`. -/
theorem alethe_walker_cong_axiom_free
    (f : Int → Int) (x y : Int) (h : x = y) : f x = f y := by
  alethe_walker_test
    "( (assume a0 (= x y)) \
       (step t0 (cl (= (f x) (f y))) :rule cong :premises (a0)) )"

#print axioms alethe_walker_cong_axiom_free

/-- `cong` over a 2-arg UF symbol: `a = c ∧ b = d ⊢ f a b = f c d`.
    The `mkCongr` left-fold builds the curried cascade
    `(f a) b = (f c) d` via two `mkCongr` steps. -/
theorem alethe_walker_cong_two_arg_axiom_free
    (f : Int → Int → Int) (a b c d : Int)
    (h1 : a = c) (h2 : b = d) : f a b = f c d := by
  alethe_walker_test
    "( (assume a0 (= a c)) \
       (assume a1 (= b d)) \
       (step t0 (cl (= (f a b) (f c d))) \
        :rule cong :premises (a0 a1)) )"

#print axioms alethe_walker_cong_two_arg_axiom_free

/-- End-to-end UF refutation: combine `cong` with the clausal
    layer. From `x = y` and `f x ≠ f y`, derive `False` via
    `cong` (to get `f x = f y`) + `resolution` against the
    inequality. The walker reconstructs the full proof skeleton
    axiom-free — UF reasoning all the way down. -/
theorem alethe_walker_cong_refutation_axiom_free
    (f : Int → Int) (x y : Int)
    (h : x = y) (hne : ¬(f x = f y)) : False := by
  alethe_walker_test
    "( (assume a0 (= x y)) \
       (assume a1 (not (= (f x) (f y)))) \
       (step t0 (cl (= (f x) (f y))) :rule cong :premises (a0)) \
       (step t1 (cl) :rule resolution :premises (t0 a1)) )"

#print axioms alethe_walker_cong_refutation_axiom_free

/- Alethe walker — trust-tagged leaves (`hole` / `rare_rewrite`).

   cvc5 emits these for clauses it admits without finer-grained
   proof — `hole` for `TRUST_THEORY_REWRITE`-annotated rewrites,
   `rare_rewrite` for steps justified by its RARE rewrite system.
   Audit H1 forbids trusting either tag: the walker re-derives the
   clause from scratch via omega, ignoring the annotation. The
   `[propext, Quot.sound]` axiom footprint matches the `la_generic`
   path — omega is axiom-free, and the cvc5 annotation contributes
   no trust delta. -/

/-- `hole`: cvc5 emits a `TRUST_THEORY_REWRITE`-annotated leaf for
    `0 ≤ 5`. The walker ignores the annotation and re-derives via
    omega, producing an axiom-free proof. -/
theorem alethe_walker_hole_axiom_free : (0 : Int) ≤ 5 := by
  alethe_walker_test
    "( (step t0 (cl (<= 0 5)) :rule hole) )"

#print axioms alethe_walker_hole_axiom_free

/-- `rare_rewrite`: same omega-discharge policy. Mid-proof
    trust-tagged step the walker re-verifies independently. -/
theorem alethe_walker_rare_rewrite_axiom_free (x : Int) :
    ¬(x ≥ 3) ∨ (x ≥ 1) := by
  alethe_walker_test
    "( (step t0 (cl (not (>= x 3)) (>= x 1)) :rule rare_rewrite) )"

#print axioms alethe_walker_rare_rewrite_axiom_free

/-- End-to-end: a `hole` clause feeding into resolution. The
    walker discharges the trust-tagged leaf via omega (the clause
    is the LIA-tautological implication `n ≥ 6 → n ≥ 5`), then
    the clausal layer composes it against the hypotheses to close
    `False`. Confirms `hole` slots into the existing resolution
    machinery the same way `la_generic` does. -/
theorem alethe_walker_hole_refutation_axiom_free
    (n : Int) (h1 : n ≥ 6) (h2 : ¬(n ≥ 5)) : False := by
  alethe_walker_test
    "( (assume a0 (>= n 6)) \
       (assume a1 (not (>= n 5))) \
       (step t0 (cl (not (>= n 6)) (>= n 5)) :rule hole) \
       (step t1 (cl (not (>= n 6))) :rule resolution :premises (t0 a1)) \
       (step t2 (cl) :rule resolution :premises (t1 a0)) )"

#print axioms alethe_walker_hole_refutation_axiom_free

/-- audit H1: a `hole` whose clause is *not* in fact valid (not
    an omega-tautology, not implied by the hypotheses) must FAIL
    rather than be admitted on the trust tag. `(>= n 100)` from no
    premises is false in general; the walker's omega re-derivation
    fails, the tactic errors, and the goal is left OPEN. This is
    the contract that makes `hole` H1-safe: cvc5's annotation is
    advisory, never license. -/
example (n : Int) : True := by
  fail_if_success
    (alethe_walker_test
      "( (step t0 (cl (>= n 100)) :rule hole) )")
  trivial

/- Alethe walker — boolean-cleanup cluster (`implies` / `equiv1`
   / `equiv2` / `not_and` / `and_neg`).

   These rules flatten implications, propositional equivalences,
   and conjunctions into clausal form for the resolution layer.
   Proof terms are constructed by `Classical.em` case analysis on
   the relevant Props, so the footprint is `[propext,
   Classical.choice, Quot.sound]` — the standard classical
   baseline, no new trust delta. `equiv_simplify` was deferred
   from this cluster (its propositional-equality tautologies need
   propext + Iff reflexivity rather than omega-discharge) and has
   since landed — see the `equiv_simplify` section below. -/

/-- `implies`: from premise `a → b`, derive `¬a ∨ b`. The walker
    builds the proof by case-splitting `a`: if `a`, the premise
    gives `b`; if `¬a`, that is the left disjunct. -/
theorem alethe_walker_implies_axiom_free
    (a b : Prop) (h : a → b) : ¬a ∨ b := by
  alethe_walker_test
    "( (assume a0 (=> a b)) \
       (step t0 (cl (not a) b) :rule implies :premises (a0)) )"

#print axioms alethe_walker_implies_axiom_free

/-- `equiv1`: forward direction of propositional equivalence —
    from `h : a = b`, derive `¬a ∨ b`. -/
theorem alethe_walker_equiv1_axiom_free
    (a b : Prop) (h : a = b) : ¬a ∨ b := by
  alethe_walker_test
    "( (assume a0 (= a b)) \
       (step t0 (cl (not a) b) :rule equiv1 :premises (a0)) )"

#print axioms alethe_walker_equiv1_axiom_free

/-- `equiv2`: backward direction — from `h : a = b`, derive
    `a ∨ ¬b`. -/
theorem alethe_walker_equiv2_axiom_free
    (a b : Prop) (h : a = b) : a ∨ ¬b := by
  alethe_walker_test
    "( (assume a0 (= a b)) \
       (step t0 (cl a (not b)) :rule equiv2 :premises (a0)) )"

#print axioms alethe_walker_equiv2_axiom_free

/-- `not_and` binary: from `¬(a ∧ b)`, derive `¬a ∨ ¬b`. De
    Morgan's law in classical form. -/
theorem alethe_walker_not_and_axiom_free
    (a b : Prop) (h : ¬(a ∧ b)) : ¬a ∨ ¬b := by
  alethe_walker_test
    "( (assume a0 (not (and a b))) \
       (step t0 (cl (not a) (not b)) :rule not_and :premises (a0)) )"

#print axioms alethe_walker_not_and_axiom_free

/-- `not_and` ternary: exercises the recursive `buildNotAnd`
    helper over a right-associated `a ∧ (b ∧ c)` premise,
    producing the right-associated `¬a ∨ (¬b ∨ ¬c)`. -/
theorem alethe_walker_not_and_ternary_axiom_free
    (a b c : Prop) (h : ¬(a ∧ b ∧ c)) : ¬a ∨ ¬b ∨ ¬c := by
  alethe_walker_test
    "( (assume a0 (not (and a b c))) \
       (step t0 (cl (not a) (not b) (not c)) :rule not_and :premises (a0)) )"

#print axioms alethe_walker_not_and_ternary_axiom_free

/-- `and_neg` binary: tautology `(a ∧ b) ∨ ¬a ∨ ¬b`. No
    premises — constructed purely by case analysis. -/
theorem alethe_walker_and_neg_axiom_free
    (a b : Prop) : (a ∧ b) ∨ ¬a ∨ ¬b := by
  alethe_walker_test
    "( (step t0 (cl (and a b) (not a) (not b)) :rule and_neg) )"

#print axioms alethe_walker_and_neg_axiom_free

/-- `and_neg` ternary: tautology `(a ∧ b ∧ c) ∨ ¬a ∨ ¬b ∨ ¬c`.
    Exercises the recursive `buildAndNeg` helper. -/
theorem alethe_walker_and_neg_ternary_axiom_free
    (a b c : Prop) : (a ∧ b ∧ c) ∨ ¬a ∨ ¬b ∨ ¬c := by
  alethe_walker_test
    "( (step t0 (cl (and a b c) (not a) (not b) (not c)) :rule and_neg) )"

#print axioms alethe_walker_and_neg_ternary_axiom_free

/-- End-to-end refutation combining boolean cleanup with
    resolution: from `h : a → b`, `ha : a`, `hnb : ¬b`, derive
    `False`. `implies` flattens `h` to `¬a ∨ b`; two resolution
    steps cancel the literals against the hypotheses. -/
theorem alethe_walker_implies_refutation_axiom_free
    (a b : Prop) (h : a → b) (ha : a) (hnb : ¬b) : False := by
  alethe_walker_test
    "( (assume a0 (=> a b)) \
       (assume a1 a) \
       (assume a2 (not b)) \
       (step t0 (cl (not a) b) :rule implies :premises (a0)) \
       (step t1 (cl b) :rule resolution :premises (t0 a1)) \
       (step t2 (cl) :rule resolution :premises (t1 a2)) )"

#print axioms alethe_walker_implies_refutation_axiom_free

/- Alethe walker — negation-of-connective cluster (`not_not` /
   `not_or`). The two premise-light boolean rules cvc5 emits when
   refuting a negated disjunction (see the `lia_disjunction`
   corpus trace). `not_or` is constructive; `not_not` case-splits
   with `Classical.em` and lands at the classical baseline. -/

/-- `not_or`: from `h : ¬(a ∨ b)` and `ha : a`, derive `False`.
    `not_or` projects `¬a` out of the negated disjunction
    (index 0); resolution cancels it against `ha`. Constructive —
    no `Classical`. -/
theorem alethe_walker_not_or_refutation_axiom_free
    (a b : Prop) (h : ¬(a ∨ b)) (ha : a) : False := by
  alethe_walker_test
    "( (assume a0 (not (or a b))) \
       (assume a1 a) \
       (step t0 (cl (not a)) :rule not_or :premises (a0) :args (0)) \
       (step t1 (cl) :rule resolution :premises (t0 a1)) )"

#print axioms alethe_walker_not_or_refutation_axiom_free

/-- `not_not`: tautology `(cl (¬¬¬p) p)`. With `hnp : ¬p` and
    `hnnp : ¬¬p`, resolution cancels `p` (against `hnp`) then
    `¬¬¬p` (against `hnnp`) to close `False`. Footprint: classical
    baseline (`not_not` case-splits with `Classical.em`). -/
theorem alethe_walker_not_not_refutation_axiom_free
    (p : Prop) (hnp : ¬p) (hnnp : ¬¬p) : False := by
  alethe_walker_test
    "( (assume a0 (not p)) \
       (assume a1 (not (not p))) \
       (step t0 (cl (not (not (not p))) p) :rule not_not) \
       (step t1 (cl (not (not (not p)))) :rule resolution :premises (t0 a0)) \
       (step t2 (cl) :rule resolution :premises (t1 a1)) )"

#print axioms alethe_walker_not_not_refutation_axiom_free

/- Alethe walker — connective-introduction tautology cluster
   (`and_pos` / `or_neg` / `implies_neg1` / `implies_neg2` /
   `implies_simplify`). Each tautology is asserted directly as the
   goal. The `em`-based four land at the classical baseline;
   `implies_simplify` closes by `rfl` and is genuinely axiom-free. -/

/-- `and_pos` (index 0): `¬(a ∧ b) ∨ a`. -/
theorem alethe_walker_and_pos_axiom_free (a b : Prop) : ¬(a ∧ b) ∨ a := by
  alethe_walker_test
    "( (step t0 (cl (not (and a b)) a) :rule and_pos :args (0)) )"

#print axioms alethe_walker_and_pos_axiom_free

/-- `or_neg` (index 0): `(a ∨ b) ∨ ¬a`. -/
theorem alethe_walker_or_neg_axiom_free (a b : Prop) : (a ∨ b) ∨ ¬a := by
  alethe_walker_test
    "( (step t0 (cl (or a b) (not a)) :rule or_neg :args (0)) )"

#print axioms alethe_walker_or_neg_axiom_free

/-- `implies_neg1`: `(a → b) ∨ a`. -/
theorem alethe_walker_implies_neg1_axiom_free (a b : Prop) : (a → b) ∨ a := by
  alethe_walker_test
    "( (step t0 (cl (=> a b) a) :rule implies_neg1) )"

#print axioms alethe_walker_implies_neg1_axiom_free

/-- `implies_neg2`: `(a → b) ∨ ¬b`. -/
theorem alethe_walker_implies_neg2_axiom_free (a b : Prop) : (a → b) ∨ ¬b := by
  alethe_walker_test
    "( (step t0 (cl (=> a b) (not b)) :rule implies_neg2) )"

#print axioms alethe_walker_implies_neg2_axiom_free

/-- `implies_simplify`: `(a → False) = ¬a`. Constructive (`rfl`). -/
theorem alethe_walker_implies_simplify_axiom_free (a : Prop) : (a → False) = ¬a := by
  alethe_walker_test
    "( (step t0 (cl (= (=> a false) (not a))) :rule implies_simplify) )"

#print axioms alethe_walker_implies_simplify_axiom_free

/- Alethe walker — clause-structure rules (`reordering` /
   `contraction`). Both remap a premise's disjunction onto a
   set-preserving rewrite of its literal list. The `or` rule first
   unpacks an assumed disjunction into a multi-literal clause; then
   the rule under test permutes / dedups it. Constructive
   (`Or.elim` / `Or.inl`/`Or.inr` only) — genuinely axiom-free. -/

/-- `reordering`: from `h : a ∨ b`, derive `b ∨ a`. -/
theorem alethe_walker_reordering_axiom_free (a b : Prop) (h : a ∨ b) : b ∨ a := by
  alethe_walker_test
    "( (assume a0 (or a b)) \
       (step t0 (cl a b) :rule or :premises (a0)) \
       (step t1 (cl b a) :rule reordering :premises (t0)) )"

#print axioms alethe_walker_reordering_axiom_free

/-- `contraction`: from `h : a ∨ a`, derive `a`. -/
theorem alethe_walker_contraction_axiom_free (a : Prop) (h : a ∨ a) : a := by
  alethe_walker_test
    "( (assume a0 (or a a)) \
       (step t0 (cl a a) :rule or :premises (a0)) \
       (step t1 (cl a) :rule contraction :premises (t0)) )"

#print axioms alethe_walker_contraction_axiom_free

/- Alethe walker — `subproof` (anchored deduction lifting).
   A subproof assumes `a` locally, resolves it against the
   top-level `h : ¬a` to the empty clause, and the discharging
   `subproof` step lifts that to `(cl (not a) false)` ≡ `¬a ∨ False`
   (an empty body contributes the `false` literal). A final
   resolution against `false` peels it off to recover `¬a`.
   Exercises: local-assume fvar binding, the empty-body → `false`
   case, and the `em`-based deduction lift. Classical baseline. -/
theorem alethe_walker_subproof_axiom_free (a : Prop) (h : ¬a) : ¬a := by
  alethe_walker_test
    "( (assume a0 (not a)) \
       (anchor :step t0) \
       (assume t0.a0 a) \
       (step t0.t0 (cl) :rule resolution :premises (t0.a0 a0)) \
       (step t0 (cl (not a) false) :rule subproof :discharge (t0.a0)) \
       (step t1 (cl (not false)) :rule false) \
       (step t2 (cl (not a)) :rule resolution :premises (t0 t1)) )"

#print axioms alethe_walker_subproof_axiom_free

/- Alethe walker — `equiv_simplify` (propositional-equality
   tautologies).

   cvc5's `equiv_simplify` emits propositional-equality
   tautologies — reflexivity, double negation, identity-element
   elimination, etc. — as `(cl (= lhs rhs))` clauses. The walker
   pattern-matches on the clause shape and constructs a proof
   term per supported pattern. Three of the four patterns close
   constructively (`[propext, Quot.sound]`); only the
   double-negation pattern needs `Classical.not_not` and lands
   at the classical baseline.

   Unsupported patterns surface as `throwError` (audit H1) — see
   the negative test. New patterns can be added incrementally to
   `elabEquivSimplify`. -/

/-- Reflexivity tautology: `(t = t) = True`. Proof term:
    `propext (Iff.intro (fun _ => True.intro) (fun _ => Eq.refl t))`.
    Constructive — no `Classical`. -/
theorem alethe_walker_equiv_simplify_refl_axiom_free
    (t : Int) : (t = t) = True := by
  alethe_walker_test
    "( (step t0 (cl (= (= t t) true)) :rule equiv_simplify) )"

#print axioms alethe_walker_equiv_simplify_refl_axiom_free

/-- Double negation: `(¬¬a) = a`. Uses `Classical.not_not` —
    the forward direction `¬¬a → a` is the classical step;
    backward is constructive. Footprint: classical baseline. -/
theorem alethe_walker_equiv_simplify_not_not_axiom_free
    (a : Prop) : (¬¬a) = a := by
  alethe_walker_test
    "( (step t0 (cl (= (not (not a)) a)) :rule equiv_simplify) )"

#print axioms alethe_walker_equiv_simplify_not_not_axiom_free

/-- And-idempotence: `(a ∧ a) = a`. Proof:
    `propext (Iff.intro And.left (fun ha => ⟨ha, ha⟩))`.
    Constructive. -/
theorem alethe_walker_equiv_simplify_and_idem_axiom_free
    (a : Prop) : (a ∧ a) = a := by
  alethe_walker_test
    "( (step t0 (cl (= (and a a) a)) :rule equiv_simplify) )"

#print axioms alethe_walker_equiv_simplify_and_idem_axiom_free

/-- Or-idempotence: `(a ∨ a) = a`. Proof:
    `propext (Iff.intro (fun h => h.elim id id) Or.inl)`.
    Constructive. -/
theorem alethe_walker_equiv_simplify_or_idem_axiom_free
    (a : Prop) : (a ∨ a) = a := by
  alethe_walker_test
    "( (step t0 (cl (= (or a a) a)) :rule equiv_simplify) )"

#print axioms alethe_walker_equiv_simplify_or_idem_axiom_free

/-- Eq-true elimination: `(a = True) = a`. Proof:
    `propext (Iff.intro (Eq.mp ∘ Eq.symm) (fun ha ↦ propext …))`.
    Footprint: propext. cvc5 emits this in `uf_lia_mix` /
    `lia_weaken_bound` when normalizing `(< -1 0) = true`. -/
theorem alethe_walker_equiv_simplify_eq_true_axiom_free
    (a : Prop) : (a = True) = a := by
  alethe_walker_test
    "( (step t0 (cl (= (= a true) a)) :rule equiv_simplify) )"

#print axioms alethe_walker_equiv_simplify_eq_true_axiom_free

/-- Not-true collapse: `(¬True) = False`. Proof:
    `propext (Iff.intro (fun h ↦ h True.intro) False.elim)`.
    Footprint: propext. cvc5 emits this while collapsing a
    refuted reflexive equality (corpus `prop_eq_trans`). -/
theorem alethe_walker_equiv_simplify_not_true_axiom_free
    : (¬True) = False := by
  alethe_walker_test
    "( (step t0 (cl (= (not true) false)) :rule equiv_simplify) )"

#print axioms alethe_walker_equiv_simplify_not_true_axiom_free

/-- Trust-tagged leaf with a propositional-equality tautology
    body: cvc5 tags these `TRUST_THEORY_REWRITE` exactly like
    arithmetic rewrites, but omega can't discharge them — the
    walker's `hole` path first tries the `equiv_simplify`
    structural matcher (corpus `prop_eq_trans`'s steps t5/t7).
    Footprint: propext. -/
theorem alethe_walker_hole_prop_tautology_axiom_free
    (a : Prop) : (a = a) = True := by
  alethe_walker_test
    "( (step t0 (cl (= (= a a) true)) :rule hole :args (\"TRUST_THEORY_REWRITE\")) )"

#print axioms alethe_walker_hole_prop_tautology_axiom_free

/-- audit H1: an `equiv_simplify` clause that doesn't match any
    supported pattern must FAIL rather than be admitted. The
    walker throws with a list of supported patterns; the tactic
    errors; the goal is left OPEN. `(= (and a b) (and b a))`
    (and-commutativity) is true but not in the supported set, so
    this pattern is rejected — extending support is a deliberate
    PR-level decision, never a silent broadening. -/
example (a b : Prop) : True := by
  fail_if_success
    (alethe_walker_test
      "( (step t0 (cl (= (and a b) (and b a))) :rule equiv_simplify) )")
  trivial

/- Alethe walker — non-`False` goal via `falseOrByContra`.

   cvc5's alethe-2024 traces are refutation proofs (final step
   is the empty clause `(cl)`, conclusion `False`). For a user
   goal like `n ≤ 10`, the walker now first calls
   `MVarId.falseOrByContra` to expose `¬(n ≤ 10)` as a
   hypothesis the trace's top-level `assume` step matches
   against. This wiring closes the deferred case from the
   original walker scaffold and is the integration path the
   production `proof_broker` invocation goes through. -/

/-- Non-`False` user goal closed by walking a refutation trace.
    The trace's `(assume a1 (not (<= n 10)))` matches the
    hypothesis byContra introduces; the `la_generic` leaf
    omega-discharges `n ≤ 5 ∧ ¬(n ≤ 10) ⊢ False`. -/
theorem alethe_walker_byContra_axiom_free
    (n : Int) (h : n ≤ 5) : n ≤ 10 := by
  alethe_walker_test
    "( (assume a0 (<= n 5)) \
       (assume a1 (not (<= n 10))) \
       (step t0 (cl) :rule la_generic :args ()) )"

#print axioms alethe_walker_byContra_axiom_free

/- Alethe walker — `equiv_pos1` / `equiv_pos2` (3-literal Boolean
   tautologies).

   These rules cvc5's SAT engine emits for case-splits on
   propositional equality during clausal normalization of LIA
   traces. Both are 0-premise tautologies; the proof is a nested
   `Classical.em` case-split first on `(a = b)`, then on `b`
   (`equiv_pos1`) or `a` (`equiv_pos2`), with `Eq.mp`/`Eq.mpr`
   transporting one Prop to the other in the equality-holds
   branch. Discovered as the blocker for real cvc5 LIA traces
   during the walker-into-closer integration (PR #49). -/

/-- `equiv_pos1`: tautology `¬(a = b) ∨ a ∨ ¬b`. Case-split
    cascade: not-eq → left; eq + b → middle (via `Eq.mpr`);
    eq + ¬b → right. -/
theorem alethe_walker_equiv_pos1_axiom_free
    (a b : Prop) : ¬(a = b) ∨ a ∨ ¬b := by
  alethe_walker_test
    "( (step t0 (cl (not (= a b)) a (not b)) :rule equiv_pos1) )"

#print axioms alethe_walker_equiv_pos1_axiom_free

/-- `equiv_pos2`: tautology `¬(a = b) ∨ ¬a ∨ b`. Mirror of
    `equiv_pos1`: not-eq → left; eq + ¬a → middle; eq + a → right
    (via `Eq.mp`). -/
theorem alethe_walker_equiv_pos2_axiom_free
    (a b : Prop) : ¬(a = b) ∨ ¬a ∨ b := by
  alethe_walker_test
    "( (step t0 (cl (not (= a b)) (not a) b) :rule equiv_pos2) )"

#print axioms alethe_walker_equiv_pos2_axiom_free

/- Alethe walker — `cong` over built-in operators.

   Real cvc5 LIA traces use `cong` to lift argument equalities
   through built-in operators (`not`, `+`, `<=`, etc.) — not just
   UF symbols. The Expr-level `elabCong` refactor handles these
   by translating LHS/RHS via `sexpToExpr` (which already knows
   how to translate operator-headed lists) and stripping
   `pids.length` apps to expose the typed operator. -/

/-- `cong` over `not` (unary Prop operator). Trace shape mirrors
    UF cong but with `not` as the function head. -/
theorem alethe_walker_cong_not_axiom_free
    (a b : Prop) (h : a = b) : (¬a) = (¬b) := by
  alethe_walker_test
    "( (assume a0 (= a b)) \
       (step t0 (cl (= (not a) (not b))) :rule cong :premises (a0)) )"

#print axioms alethe_walker_cong_not_axiom_free

/-- `cong` over `+` (binary polymorphic operator over `Int`).
    cvc5 emits this when lifting arg equalities through an
    addition during LIA normalization. -/
theorem alethe_walker_cong_add_axiom_free
    (x y z w : Int) (h1 : x = y) (h2 : z = w) : x + z = y + w := by
  alethe_walker_test
    "( (assume a0 (= x y)) \
       (assume a1 (= z w)) \
       (step t0 (cl (= (+ x z) (+ y w))) :rule cong :premises (a0 a1)) )"

#print axioms alethe_walker_cong_add_axiom_free

/-- `cong` over `<=` (binary comparison, predicate-valued).
    Slightly different from `+`: the conclusion's equality is
    between two `Prop`s, exercising the `mkCongr` chain when the
    operator's result type is `Prop`. -/
theorem alethe_walker_cong_le_axiom_free
    (x y : Int) (h : x = y) : (x ≤ 5) = (y ≤ 5) := by
  alethe_walker_test
    "( (assume a0 (= x y)) \
       (step t_refl (cl (= 5 5)) :rule refl) \
       (step t0 (cl (= (<= x 5) (<= y 5))) :rule cong :premises (a0 t_refl)) )"

#print axioms alethe_walker_cong_le_axiom_free

/- Alethe walker — n-ary `cong` (≥3 operands). cvc5 emits one
   premise per operand of a variadic head; the reifier renders
   n-ary `or`/`and`/`+` as a right-nested binary chain, so cong
   folds `mkCongr` over the chain rather than the flat `appFn!`
   path. Constructive (`mkCongr` only). -/

/-- `cong` over a 3-ary `or`. -/
theorem alethe_walker_cong_nary_or_axiom_free
    (a b c a' : Prop) (h : a = a') : (a ∨ b ∨ c) = (a' ∨ b ∨ c) := by
  alethe_walker_test
    "( (assume a0 (= a a')) \
       (step t0 (cl (= b b)) :rule refl) \
       (step t1 (cl (= c c)) :rule refl) \
       (step t2 (cl (= (or a b c) (or a' b c))) :rule cong :premises (a0 t0 t1)) )"

#print axioms alethe_walker_cong_nary_or_axiom_free

/-- `cong` over a 3-ary `+` (exercises the variadic-arithmetic
    reifier and the nested chain together). The goal is written in
    the right-nested form the reifier produces. -/
theorem alethe_walker_cong_nary_add_axiom_free
    (x y z w u v : Int) (h1 : x = y) (h2 : z = w) (h3 : u = v) :
    (x + (z + u)) = (y + (w + v)) := by
  alethe_walker_test
    "( (assume a0 (= x y)) \
       (assume a1 (= z w)) \
       (assume a2 (= u v)) \
       (step t0 (cl (= (+ x z u) (+ y w v))) :rule cong :premises (a0 a1 a2)) )"

#print axioms alethe_walker_cong_nary_add_axiom_free

/- Alethe walker — snapshot test against a real cvc5 trace.

   The trace below is the verbatim alethe-2024 output cvc5
   minted for `(n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m)
   ⊢ n ≤ 10` (the `lia_axiom_free` shape) — captured by adding
   diagnostic logging to `tryAletheWalker` in this branch,
   then pasted verbatim here. Walking it via `alethe_walker_test`
   exercises the walker independently of cvc5 dispatch: CI
   doesn't need cvc5 to validate this path, and the trace text
   pins the walker against the actual shape cvc5 emits.

   What the trace exercises end-to-end:
   * cvc5's `(! expr :named @id)` named-reference syntax, with
     back-references `@p_X` throughout (parsed and expanded by
     the SDK).
   * `equiv_pos2` (3-literal Boolean tautology, no premises).
   * `hole` with `TRUST_THEORY_REWRITE` annotation — re-derived
     via omega regardless of the cvc5 tag (audit H1).
   * `cong` over built-in operator atoms (`not`, `>=`) — the
     Expr-level refactor handles these uniformly.
   * `trans` chaining equality steps.
   * `refl` as a leaf.
   * Multi-premise `resolution` closing the empty clause.

   If cvc5 ever changes its trace format (different rule names,
   different ordering, new syntactic sugar), this test surfaces
   the drift immediately. -/
theorem alethe_walker_real_cvc5_trace_axiom_free
    (n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m) : n ≤ 10 := by
  alethe_walker_test "( \
    (assume a0 (! (= (+ n m) 10) :named @p_1)) \
    (assume a1 (! (<= 0 m) :named @p_2)) \
    (assume a2 (! (not (! (<= n 10) :named @p_3)) :named @p_4)) \
    (step t0 (cl (not (! (= @p_4 (! (not (! (>= m 0) :named @p_5)) :named @p_7)) :named @p_8)) (not @p_4) @p_7) :rule equiv_pos2) \
    (step t1 (cl (! (= @p_3 (! (not (! (>= n 11) :named @p_9)) :named @p_15)) :named @p_18)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_18 3 7)) \
    (step t2 (cl (= @p_4 (! (not @p_15) :named @p_16))) :rule cong :premises (t1)) \
    (step t3 (cl (! (= @p_16 @p_9) :named @p_17)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_17 1 7)) \
    (step t4 (cl (= @p_4 @p_9)) :rule trans :premises (t2 t3)) \
    (step t5 (cl (not (! (= @p_1 (! (= n (! (+ 10 (* -1 m)) :named @p_10)) :named @p_13)) :named @p_14)) (not @p_1) @p_13) :rule equiv_pos2) \
    (step t6 (cl @p_14) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_14 3 7)) \
    (step t7 (cl @p_13) :rule resolution :premises (t5 t6 a0)) \
    (step t8 (cl (= 11 11)) :rule refl) \
    (step t9 (cl (= @p_9 (! (>= @p_10 11) :named @p_11))) :rule cong :premises (t7 t8)) \
    (step t10 (cl (! (= @p_11 @p_7) :named @p_12)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_12 3 7)) \
    (step t11 (cl (= @p_9 @p_7)) :rule trans :premises (t9 t10)) \
    (step t12 (cl @p_8) :rule trans :premises (t4 t11)) \
    (step t13 (cl @p_7) :rule resolution :premises (t0 t12 a2)) \
    (step t14 (cl (not (! (= @p_2 @p_5) :named @p_6)) (not @p_2) @p_5) :rule equiv_pos2) \
    (step t15 (cl @p_6) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_6 3 7)) \
    (step t16 (cl @p_5) :rule resolution :premises (t14 t15 a1)) \
    (step t17 (cl) :rule resolution :premises (t13 t16)) )"

#print axioms alethe_walker_real_cvc5_trace_axiom_free

/- Alethe walker — quantifier instantiation + binder congruence.

   Verbatim cvc5 1.3.0 traces for corpus `uf_forall_inst` and
   `uf_exists_witness` — the first goals exercising `forall_inst`
   (instantiate a universal at a term) and `bind` (rewrite under a
   binder). Both ride the existing subproof/anchor machinery: the
   `forall_inst` clause is a classical tautology `¬(∀x,F) ∨ F[x:=t]`;
   `bind` lifts a body equality proved under the anchored binder to
   an equality of quantified formulas via `propext`. The body holes
   discharge through omega with the bound `x` / UF `f` as atoms.
   Footprint stays at the classical baseline. -/

/-- `f 3 ≤ 10` from `∀ x, f x ≤ 10` — universal instantiation at 3
    (`forall_inst :args (3)`), with `bind` rewriting `(f x ≤ 10)` to
    `¬(f x ≥ 11)` under the `∀ x` binder. -/
theorem alethe_walker_forall_inst_axiom_free
    (f : Int → Int) (h1 : ∀ x : Int, f x ≤ 10) : f 3 ≤ 10 := by
  alethe_walker_test "( \
    (assume a0 (forall ((x Int)) (<= (f x) 10))) \
    (assume a1 (! (not (! (<= (! (f 3) :named @p_1) 10) :named @p_2)) :named @p_3)) \
    (step t0 (cl (! (=> (forall ((x Int)) (not (>= (f x) 11))) (! (not (! (>= @p_1 11) :named @p_7)) :named @p_9)) :named @p_14) (forall ((x Int)) (not (>= (f x) 11)))) :rule implies_neg1) \
    (anchor :step t1) \
    (assume t1.a0 (forall ((x Int)) (not (>= (f x) 11)))) \
    (step t1.t0 (cl (or (! (not (forall ((x Int)) (not (>= (f x) 11)))) :named @p_13) @p_9)) :rule forall_inst :args (3)) \
    (step t1.t1 (cl @p_13 @p_9) :rule or :premises (t1.t0)) \
    (step t1.t2 (cl (not (! (= (forall ((x Int)) (<= (f x) 10)) (forall ((x Int)) (not (>= (f x) 11)))) :named @p_4)) (not (forall ((x Int)) (<= (f x) 10))) (forall ((x Int)) (not (>= (f x) 11)))) :rule equiv_pos2) \
    (anchor :step t1.t3 :args ((x Int) (:= (x Int) x))) \
    (step t1.t3.t0 (cl (! (= (<= (! (f x) :named @p_5) 10) (not (>= @p_5 11))) :named @p_6)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_6 3 7)) \
    (step t1.t3 (cl @p_4) :rule bind) \
    (step t1.t4 (cl (forall ((x Int)) (not (>= (f x) 11)))) :rule resolution :premises (t1.t2 t1.t3 a0)) \
    (step t1.t5 (cl @p_9) :rule resolution :premises (t1.t1 t1.t4)) \
    (step t1 (cl @p_13 @p_9) :rule subproof :discharge (t1.a0)) \
    (step t2 (cl @p_14 @p_9) :rule resolution :premises (t0 t1)) \
    (step t3 (cl @p_14 (! (not @p_9) :named @p_10)) :rule implies_neg2) \
    (step t4 (cl @p_14 @p_14) :rule resolution :premises (t2 t3)) \
    (step t5 (cl @p_14) :rule contraction :premises (t4)) \
    (step t6 (cl @p_13 @p_9) :rule implies :premises (t5)) \
    (step t7 (cl @p_9 @p_13) :rule reordering :premises (t6)) \
    (step t8 (cl (not (! (= @p_3 @p_7) :named @p_8)) (not @p_3) @p_7) :rule equiv_pos2) \
    (step t9 (cl (! (= @p_2 @p_9) :named @p_12)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_12 3 7)) \
    (step t10 (cl (= @p_3 @p_10)) :rule cong :premises (t9)) \
    (step t11 (cl (! (= @p_10 @p_7) :named @p_11)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_11 1 7)) \
    (step t12 (cl @p_8) :rule trans :premises (t10 t11)) \
    (step t13 (cl @p_7) :rule resolution :premises (t8 t12 a1)) \
    (step t14 (cl (not @p_4) (not (forall ((x Int)) (<= (f x) 10))) (forall ((x Int)) (not (>= (f x) 11)))) :rule equiv_pos2) \
    (anchor :step t15 :args ((x Int) (:= (x Int) x))) \
    (step t15.t0 (cl @p_6) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_6 3 7)) \
    (step t15 (cl @p_4) :rule bind) \
    (step t16 (cl (forall ((x Int)) (not (>= (f x) 11)))) :rule resolution :premises (t14 t15 a0)) \
    (step t17 (cl) :rule resolution :premises (t7 t13 t16)) \
    )"

#print axioms alethe_walker_forall_inst_axiom_free

/-- `∃ x, f x = 0` from a witness `f y = 0` — `forall_inst :args (y)`
    instantiates the negated-goal `∀ x, ¬(f x = 0)` at the witness
    `y`, contradicting `f y = 0`. -/
theorem alethe_walker_exists_witness_axiom_free
    (f : Int → Int) (y : Int) (h1 : f y = 0) : ∃ x : Int, f x = 0 := by
  alethe_walker_test "( \
    (assume a0 (! (= (f y) 0) :named @p_1)) \
    (assume a1 (! (not (exists ((x Int)) (= (f x) 0))) :named @p_2)) \
    (step t0 (cl (! (=> (forall ((x Int)) (not (= (f x) 0))) (! (not @p_1) :named @p_8)) :named @p_9) (forall ((x Int)) (not (= (f x) 0)))) :rule implies_neg1) \
    (anchor :step t1) \
    (assume t1.a0 (forall ((x Int)) (not (= (f x) 0)))) \
    (step t1.t0 (cl (or (! (not (forall ((x Int)) (not (= (f x) 0)))) :named @p_4) @p_8)) :rule forall_inst :args (y)) \
    (step t1.t1 (cl @p_4 @p_8) :rule or :premises (t1.t0)) \
    (step t1.t2 (cl (not (! (= @p_2 (forall ((x Int)) (not (= (f x) 0)))) :named @p_3)) (not @p_2) (forall ((x Int)) (not (= (f x) 0)))) :rule equiv_pos2) \
    (step t1.t3 (cl (! (= (exists ((x Int)) (= (f x) 0)) @p_4) :named @p_7)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_7 13 7)) \
    (step t1.t4 (cl (= @p_2 (! (not @p_4) :named @p_5))) :rule cong :premises (t1.t3)) \
    (step t1.t5 (cl (! (= @p_5 (forall ((x Int)) (not (= (f x) 0)))) :named @p_6)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_6 1 7)) \
    (step t1.t6 (cl @p_3) :rule trans :premises (t1.t4 t1.t5)) \
    (step t1.t7 (cl (forall ((x Int)) (not (= (f x) 0)))) :rule resolution :premises (t1.t2 t1.t6 a1)) \
    (step t1.t8 (cl @p_8) :rule resolution :premises (t1.t1 t1.t7)) \
    (step t1 (cl @p_4 @p_8) :rule subproof :discharge (t1.a0)) \
    (step t2 (cl @p_9 @p_8) :rule resolution :premises (t0 t1)) \
    (step t3 (cl @p_9 (not @p_8)) :rule implies_neg2) \
    (step t4 (cl @p_9 @p_9) :rule resolution :premises (t2 t3)) \
    (step t5 (cl @p_9) :rule contraction :premises (t4)) \
    (step t6 (cl @p_4 @p_8) :rule implies :premises (t5)) \
    (step t7 (cl (not @p_3) (not @p_2) (forall ((x Int)) (not (= (f x) 0)))) :rule equiv_pos2) \
    (step t8 (cl @p_7) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_7 13 7)) \
    (step t9 (cl (= @p_2 @p_5)) :rule cong :premises (t8)) \
    (step t10 (cl @p_6) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_6 1 7)) \
    (step t11 (cl @p_3) :rule trans :premises (t9 t10)) \
    (step t12 (cl (forall ((x Int)) (not (= (f x) 0)))) :rule resolution :premises (t7 t11 a1)) \
    (step t13 (cl) :rule resolution :premises (t6 a0 t12)) \
    )"

#print axioms alethe_walker_exists_witness_axiom_free

/-- Equality chains over `Prop` atoms (corpus `prop_eq_trans`):
    `p = q, q = r ⊢ p = r` via `trans`/`refl`/`cong` where the
    carrier sort is `Bool` (reified `Prop`), not `Int`. The
    `TRUST_THEORY_REWRITE` holes normalize `(r = r) = True` and
    `(¬True) = False` over Prop. Verbatim cvc5 1.3.0 output. -/
theorem alethe_walker_prop_eq_trans_axiom_free
    (p q r : Prop) (h1 : p = q) (h2 : q = r) : p = r := by
  alethe_walker_test "( \
    (assume a0 (! (= p q) :named @p_1)) \
    (assume a1 (! (= q r) :named @p_2)) \
    (assume a2 (! (not (! (= p r) :named @p_3)) :named @p_4)) \
    (step t0 (cl (not (! (= @p_4 false) :named @p_5)) (not @p_4) false) :rule equiv_pos2) \
    (step t1 (cl @p_3) :rule trans :premises (a0 a1)) \
    (step t2 (cl (! (= r r) :named @p_6)) :rule refl) \
    (step t3 (cl (= @p_3 @p_6)) :rule cong :premises (t1 t2)) \
    (step t4 (cl (= @p_4 (! (not @p_6) :named @p_7))) :rule cong :premises (t3)) \
    (step t5 (cl (! (= @p_6 true) :named @p_10)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_10 1 6)) \
    (step t6 (cl (= @p_7 (! (not true) :named @p_8))) :rule cong :premises (t5)) \
    (step t7 (cl (! (= @p_8 false) :named @p_9)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_9 1 7)) \
    (step t8 (cl (= @p_7 false)) :rule trans :premises (t6 t7)) \
    (step t9 (cl @p_5) :rule trans :premises (t4 t8)) \
    (step t10 (cl false) :rule resolution :premises (t0 t9 a2)) \
    (step t11 (cl (not false)) :rule false) \
    (step t12 (cl) :rule resolution :premises (t10 t11)) )"

#print axioms alethe_walker_prop_eq_trans_axiom_free

/-- Alethe walker — `False`-conclusion goal (corpus
    `lia_false_from_bounds`). The goal is already `False`, so the
    walker does NOT `byContra`; cvc5's negated-goal assume
    `(not false)` therefore has no matching hypothesis and is
    discharged as the `¬False` tautology (identity) — the first
    corpus goal to exercise that path. Verbatim cvc5 1.3.0 trace. -/
theorem alethe_walker_false_from_bounds_axiom_free
    (x : Int) (h1 : x ≤ 3) (h2 : 5 ≤ x) : False := by
  alethe_walker_test "( \
    (assume a0 (! (<= x 3) :named @p_1)) \
    (assume a1 (! (<= 5 x) :named @p_2)) \
    (assume a2 (! (not false) :named @p_3)) \
    (step t0 (cl (not (! (= (! (< (! (+ x (! (* -1 x) :named @p_6)) :named @p_7) (! (+ 4 (! (* -1 5) :named @p_4)) :named @p_5)) :named @p_8) false) :named @p_20)) (not @p_8) false) :rule equiv_pos2) \
    (step t1 (cl (! (= @p_8 (! (not (! (>= @p_7 @p_5) :named @p_21)) :named @p_22)) :named @p_31)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_31 3 6)) \
    (step t2 (cl (! (= @p_7 0) :named @p_30)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_30 3 7)) \
    (step t3 (cl (= 4 4)) :rule refl) \
    (step t4 (cl (! (= @p_4 -5) :named @p_29)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_29 3 7)) \
    (step t5 (cl (= @p_5 (! (+ 4 -5) :named @p_27))) :rule cong :premises (t3 t4)) \
    (step t6 (cl (! (= @p_27 -1) :named @p_28)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_28 3 7)) \
    (step t7 (cl (= @p_5 -1)) :rule trans :premises (t5 t6)) \
    (step t8 (cl (= @p_21 (! (>= 0 -1) :named @p_25))) :rule cong :premises (t2 t7)) \
    (step t9 (cl (! (= @p_25 true) :named @p_26)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_26 3 7)) \
    (step t10 (cl (= @p_21 true)) :rule trans :premises (t8 t9)) \
    (step t11 (cl (= @p_22 (! (not true) :named @p_23))) :rule cong :premises (t10)) \
    (step t12 (cl (! (= @p_23 false) :named @p_24)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_24 1 7)) \
    (step t13 (cl (= @p_22 false)) :rule trans :premises (t11 t12)) \
    (step t14 (cl @p_20) :rule trans :premises (t1 t13)) \
    (step t15 (cl (not (! (< x 4) :named @p_15)) (not (! (<= @p_6 @p_4) :named @p_9)) @p_8) :rule la_generic :args (1/1 1/1 1/1)) \
    (step t16 (cl (not (! (= (! (not (>= x 4)) :named @p_16) @p_15) :named @p_18)) (not @p_16) @p_15) :rule equiv_pos2) \
    (step t17 (cl (! (= @p_15 @p_16) :named @p_19)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_19 3 6)) \
    (step t18 (cl @p_18) :rule symm :premises (t17)) \
    (step t19 (cl (not (! (= @p_1 @p_16) :named @p_17)) (not @p_1) @p_16) :rule equiv_pos2) \
    (step t20 (cl @p_17) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_17 3 7)) \
    (step t21 (cl @p_16) :rule resolution :premises (t19 t20 a0)) \
    (step t22 (cl @p_15) :rule resolution :premises (t16 t18 t21)) \
    (step t23 (cl (=> (! (and (! (< -1 0) :named @p_11) (! (>= x 5) :named @p_10)) :named @p_12) @p_9)) :rule la_mult_neg) \
    (step t24 (cl (not @p_12) @p_9) :rule implies :premises (t23)) \
    (step t25 (cl @p_12 (not @p_11) (not @p_10)) :rule and_neg) \
    (step t26 (cl (= (! (= @p_11 true) :named @p_14) @p_11)) :rule equiv_simplify) \
    (step t27 (cl (not @p_14) @p_11) :rule equiv1 :premises (t26)) \
    (step t28 (cl @p_14) :rule rare_rewrite :args (\"evaluate\")) \
    (step t29 (cl @p_11) :rule resolution :premises (t27 t28)) \
    (step t30 (cl (not (! (= @p_2 @p_10) :named @p_13)) (not @p_2) @p_10) :rule equiv_pos2) \
    (step t31 (cl @p_13) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_13 3 7)) \
    (step t32 (cl @p_10) :rule resolution :premises (t30 t31 a1)) \
    (step t33 (cl @p_12) :rule resolution :premises (t25 t29 t32)) \
    (step t34 (cl @p_9) :rule resolution :premises (t24 t33)) \
    (step t35 (cl @p_8) :rule resolution :premises (t15 t22 t34)) \
    (step t36 (cl false) :rule resolution :premises (t0 t14 t35)) \
    (step t37 (cl @p_3) :rule false) \
    (step t38 (cl) :rule resolution :premises (t36 t37)) \
    )"

#print axioms alethe_walker_false_from_bounds_axiom_free








/- Alethe walker — scale point (corpus `lia_pigeonhole3`).

   Verbatim cvc5 1.3.0 refutation that three values in {1,2} cannot be
   pairwise distinct: 636 steps, 118 arithmetic leaves, the widest
   corpus trace (~5x the next). Exercises both scale fixes — the
   resolution-resolvent dedup (set semantics) and the exclusion of
   subproof-local assumes from omega's hypotheses — together with the
   `False`-conclusion assume. Footprint: classical baseline. -/
theorem alethe_walker_pigeonhole3_axiom_free
    (a b c : Int) (la : 1 ≤ a) (ua : a ≤ 2) (lb : 1 ≤ b) (ub : b ≤ 2)
    (lc : 1 ≤ c) (uc : c ≤ 2) (dab : a ≠ b) (dbc : b ≠ c) (dac : a ≠ c) : False := by
  alethe_walker_test "( \
    (assume a0 (! (<= 1 a) :named @p_1)) \
    (assume a1 (! (<= a 2) :named @p_2)) \
    (assume a2 (! (<= 1 b) :named @p_3)) \
    (assume a3 (! (<= b 2) :named @p_4)) \
    (assume a4 (! (<= 1 c) :named @p_5)) \
    (assume a5 (! (<= c 2) :named @p_6)) \
    (assume a6 (! (not (! (= a b) :named @p_7)) :named @p_8)) \
    (assume a7 (! (not (! (= b c) :named @p_9)) :named @p_10)) \
    (assume a8 (! (not (! (= a c) :named @p_11)) :named @p_12)) \
    (assume a9 (! (not false) :named @p_13)) \
    (step t0 (cl (not (! (= (! (or (! (not (! (not (! (>= (! (+ b (! (* -1 c) :named @p_21)) :named @p_35) 0) :named @p_36)) :named @p_39)) :named @p_40) (! (not (! (>= b 1) :named @p_19)) :named @p_228) (! (not (! (>= (! (+ a @p_21) :named @p_22) 1) :named @p_23)) :named @p_164) (! (not (! (not (! (>= a 3) :named @p_14)) :named @p_15)) :named @p_258)) :named @p_290) (! (or @p_36 @p_228 @p_164 @p_14) :named @p_289)) :named @p_305)) (not @p_290) @p_289) :rule equiv_pos2) \
    (step t1 (cl (! (= @p_40 @p_36) :named @p_89)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_89 1 6)) \
    (step t2 (cl (= @p_228 @p_228)) :rule refl) \
    (step t3 (cl (= @p_164 @p_164)) :rule refl) \
    (step t4 (cl (! (= @p_258 @p_14) :named @p_286)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_286 1 6)) \
    (step t5 (cl @p_305) :rule cong :premises (t1 t2 t3 t4)) \
    (step t6 (cl (! (=> (! (and @p_39 @p_19 @p_23 @p_15) :named @p_291) false) :named @p_293) @p_291) :rule implies_neg1) \
    (anchor :step t7) \
    (assume t7.a0 @p_39) \
    (assume t7.a1 @p_19) \
    (assume t7.a2 @p_23) \
    (assume t7.a3 @p_15) \
    (step t7.t0 (cl (not (! (= (! (> a 2) :named @p_294) (! (not @p_2) :named @p_18)) :named @p_304)) (not @p_294) @p_18) :rule equiv_pos2) \
    (step t7.t1 (cl @p_304) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_304 3 6)) \
    (step t7.t2 (cl (not (! (= @p_18 @p_294) :named @p_303)) (not @p_18) @p_294) :rule equiv_pos2) \
    (step t7.t3 (cl (! (= @p_2 @p_15) :named @p_16)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_16 3 7)) \
    (step t7.t4 (cl (= @p_18 @p_258)) :rule cong :premises (t7.t3)) \
    (step t7.t5 (cl (= @p_18 @p_14)) :rule trans :premises (t7.t4 t4)) \
    (step t7.t6 (cl (= @p_294 @p_14)) :rule trans :premises (t7.t1 t7.t5)) \
    (step t7.t7 (cl (= @p_14 @p_294)) :rule symm :premises (t7.t6)) \
    (step t7.t8 (cl @p_303) :rule trans :premises (t7.t5 t7.t7)) \
    (step t7.t9 (cl (! (=> @p_2 false) :named @p_295) @p_2) :rule implies_neg1) \
    (anchor :step t7.t10) \
    (assume t7.t10.a0 @p_2) \
    (step t7.t10.t0 (cl (not (! (= (! (< (! (+ a (! (* -1 @p_22) :named @p_189) (! (* -1 b) :named @p_25) @p_35) :named @p_296) (! (+ 2 (! (* -1 1) :named @p_52) @p_52 0) :named @p_188)) :named @p_297) false) :named @p_298)) (not @p_297) false) :rule equiv_pos2) \
    (step t7.t10.t1 (cl (! (= @p_297 (! (not (! (>= @p_296 @p_188) :named @p_299)) :named @p_300)) :named @p_302)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_302 3 6)) \
    (step t7.t10.t2 (cl (! (= @p_296 (! (+ (! (* 0 c) :named @p_146) @p_25 b (! (* 0 a) :named @p_204)) :named @p_205)) :named @p_301)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_301 3 6)) \
    (step t7.t10.t3 (cl (! (= @p_146 0) :named @p_151)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_151 3 6)) \
    (step t7.t10.t4 (cl (= @p_25 @p_25)) :rule refl) \
    (step t7.t10.t5 (cl (= b b)) :rule refl) \
    (step t7.t10.t6 (cl (! (= @p_204 0) :named @p_208)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_208 3 6)) \
    (step t7.t10.t7 (cl (= @p_205 (! (+ 0 @p_25 b 0) :named @p_206))) :rule cong :premises (t7.t10.t3 t7.t10.t4 t7.t10.t5 t7.t10.t6)) \
    (step t7.t10.t8 (cl (! (= @p_206 0) :named @p_207)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_207 3 7)) \
    (step t7.t10.t9 (cl (= @p_205 0)) :rule trans :premises (t7.t10.t7 t7.t10.t8)) \
    (step t7.t10.t10 (cl (= @p_296 0)) :rule trans :premises (t7.t10.t2 t7.t10.t9)) \
    (step t7.t10.t11 (cl (= 2 2)) :rule refl) \
    (step t7.t10.t12 (cl (! (= @p_52 -1) :named @p_83)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_83 3 7)) \
    (step t7.t10.t13 (cl (= 0 0)) :rule refl) \
    (step t7.t10.t14 (cl (= @p_188 (! (+ 2 -1 -1 0) :named @p_202))) :rule cong :premises (t7.t10.t11 t7.t10.t12 t7.t10.t12 t7.t10.t13)) \
    (step t7.t10.t15 (cl (! (= @p_202 0) :named @p_203)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_203 3 7)) \
    (step t7.t10.t16 (cl (= @p_188 0)) :rule trans :premises (t7.t10.t14 t7.t10.t15)) \
    (step t7.t10.t17 (cl (= @p_299 (! (>= 0 0) :named @p_79))) :rule cong :premises (t7.t10.t10 t7.t10.t16)) \
    (step t7.t10.t18 (cl (! (= @p_79 true) :named @p_80)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_80 3 7)) \
    (step t7.t10.t19 (cl (= @p_299 true)) :rule trans :premises (t7.t10.t17 t7.t10.t18)) \
    (step t7.t10.t20 (cl (= @p_300 (! (not true) :named @p_77))) :rule cong :premises (t7.t10.t19)) \
    (step t7.t10.t21 (cl (! (= @p_77 false) :named @p_78)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_78 1 7)) \
    (step t7.t10.t22 (cl (= @p_300 false)) :rule trans :premises (t7.t10.t20 t7.t10.t21)) \
    (step t7.t10.t23 (cl @p_298) :rule trans :premises (t7.t10.t1 t7.t10.t22)) \
    (step t7.t10.t24 (cl @p_18 (! (not (! (<= @p_189 @p_52) :named @p_194)) :named @p_197) (! (not (! (<= @p_25 @p_52) :named @p_239)) :named @p_245) (! (not (! (< @p_35 0) :named @p_68)) :named @p_72) @p_297) :rule la_generic :args (1/1 1/1 1/1 1/1 1/1)) \
    (step t7.t10.t25 (cl (=> (! (and (! (< -1 0) :named @p_64) @p_23) :named @p_195) @p_194)) :rule la_mult_neg) \
    (step t7.t10.t26 (cl (! (not @p_195) :named @p_196) @p_194) :rule implies :premises (t7.t10.t25)) \
    (step t7.t10.t27 (cl @p_195 (! (not @p_64) :named @p_67) @p_164) :rule and_neg) \
    (step t7.t10.t28 (cl (= (! (= @p_64 true) :named @p_66) @p_64)) :rule equiv_simplify) \
    (step t7.t10.t29 (cl (not @p_66) @p_64) :rule equiv1 :premises (t7.t10.t28)) \
    (step t7.t10.t30 (cl @p_66) :rule rare_rewrite :args (\"evaluate\")) \
    (step t7.t10.t31 (cl @p_64) :rule resolution :premises (t7.t10.t29 t7.t10.t30)) \
    (step t7.t10.t32 (cl @p_195) :rule resolution :premises (t7.t10.t27 t7.t10.t31 t7.a2)) \
    (step t7.t10.t33 (cl @p_194) :rule resolution :premises (t7.t10.t26 t7.t10.t32)) \
    (step t7.t10.t34 (cl (=> (! (and @p_64 @p_19) :named @p_240) @p_239)) :rule la_mult_neg) \
    (step t7.t10.t35 (cl (not @p_240) @p_239) :rule implies :premises (t7.t10.t34)) \
    (step t7.t10.t36 (cl @p_240 @p_67 @p_228) :rule and_neg) \
    (step t7.t10.t37 (cl (not (! (= @p_3 @p_19) :named @p_20)) (not @p_3) @p_19) :rule equiv_pos2) \
    (step t7.t10.t38 (cl @p_20) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_20 3 7)) \
    (step t7.t10.t39 (cl @p_19) :rule resolution :premises (t7.t10.t37 t7.t10.t38 a2)) \
    (step t7.t10.t40 (cl @p_240) :rule resolution :premises (t7.t10.t36 t7.t10.t31 t7.t10.t39)) \
    (step t7.t10.t41 (cl @p_239) :rule resolution :premises (t7.t10.t35 t7.t10.t40)) \
    (step t7.t10.t42 (cl (! (not (! (= @p_39 @p_68) :named @p_69)) :named @p_71) @p_40 @p_68) :rule equiv_pos2) \
    (step t7.t10.t43 (cl (! (= @p_68 @p_39) :named @p_70)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_70 3 6)) \
    (step t7.t10.t44 (cl @p_69) :rule symm :premises (t7.t10.t43)) \
    (step t7.t10.t45 (cl @p_68) :rule resolution :premises (t7.t10.t42 t7.t10.t44 t7.a0)) \
    (step t7.t10.t46 (cl @p_297) :rule resolution :premises (t7.t10.t24 t7.t10.a0 t7.t10.t33 t7.t10.t41 t7.t10.t45)) \
    (step t7.t10.t47 (cl false) :rule resolution :premises (t7.t10.t0 t7.t10.t23 t7.t10.t46)) \
    (step t7.t10 (cl @p_18 false) :rule subproof :discharge (t7.t10.a0)) \
    (step t7.t11 (cl @p_295 false) :rule resolution :premises (t7.t9 t7.t10)) \
    (step t7.t12 (cl @p_295 @p_13) :rule implies_neg2) \
    (step t7.t13 (cl @p_295 @p_295) :rule resolution :premises (t7.t11 t7.t12)) \
    (step t7.t14 (cl @p_295) :rule contraction :premises (t7.t13)) \
    (step t7.t15 (cl (= @p_295 @p_18)) :rule implies_simplify) \
    (step t7.t16 (cl (not @p_295) @p_18) :rule equiv1 :premises (t7.t15)) \
    (step t7.t17 (cl @p_18) :rule resolution :premises (t7.t14 t7.t16)) \
    (step t7.t18 (cl @p_294) :rule resolution :premises (t7.t2 t7.t8 t7.t17)) \
    (step t7.t19 (cl @p_18) :rule resolution :premises (t7.t0 t7.t1 t7.t18)) \
    (step t7.t20 (cl) :rule resolution :premises (a1 t7.t19)) \
    (step t7 (cl @p_40 @p_228 @p_164 @p_258 false) :rule subproof :discharge (t7.a0 t7.a1 t7.a2 t7.a3)) \
    (step t8 (cl (! (not @p_291) :named @p_292) @p_39) :rule and_pos :args (0)) \
    (step t9 (cl @p_292 @p_19) :rule and_pos :args (1)) \
    (step t10 (cl @p_292 @p_23) :rule and_pos :args (2)) \
    (step t11 (cl @p_292 @p_15) :rule and_pos :args (3)) \
    (step t12 (cl false @p_292 @p_292 @p_292 @p_292) :rule resolution :premises (t7 t8 t9 t10 t11)) \
    (step t13 (cl @p_292 @p_292 @p_292 @p_292 false) :rule reordering :premises (t12)) \
    (step t14 (cl @p_292 false) :rule contraction :premises (t13)) \
    (step t15 (cl @p_293 false) :rule resolution :premises (t6 t14)) \
    (step t16 (cl @p_293 @p_13) :rule implies_neg2) \
    (step t17 (cl @p_293 @p_293) :rule resolution :premises (t15 t16)) \
    (step t18 (cl @p_293) :rule contraction :premises (t17)) \
    (step t19 (cl (= @p_293 @p_292)) :rule implies_simplify) \
    (step t20 (cl (not @p_293) @p_292) :rule equiv1 :premises (t19)) \
    (step t21 (cl @p_292) :rule resolution :premises (t18 t20)) \
    (step t22 (cl @p_40 @p_228 @p_164 @p_258) :rule not_and :premises (t21)) \
    (step t23 (cl @p_290 (! (not @p_40) :named @p_45)) :rule or_neg :args (0)) \
    (step t24 (cl @p_290 (! (not @p_228) :named @p_231)) :rule or_neg :args (1)) \
    (step t25 (cl @p_290 (! (not @p_164) :named @p_165)) :rule or_neg :args (2)) \
    (step t26 (cl @p_290 (! (not @p_258) :named @p_260)) :rule or_neg :args (3)) \
    (step t27 (cl @p_290 @p_290 @p_290 @p_290) :rule resolution :premises (t22 t23 t24 t25 t26)) \
    (step t28 (cl @p_290) :rule contraction :premises (t27)) \
    (step t29 (cl @p_289) :rule resolution :premises (t0 t5 t28)) \
    (step t30 (cl @p_36 @p_228 @p_164 @p_14) :rule or :premises (t29)) \
    (step t31 (cl @p_14 @p_36 @p_164 @p_228) :rule reordering :premises (t30)) \
    (step t32 (cl (not (! (= (! (or (! (not (! (not (! (>= @p_35 1) :named @p_92)) :named @p_94)) :named @p_95) @p_39) :named @p_96) (! (or @p_92 @p_39) :named @p_93)) :named @p_107)) (not @p_96) @p_93) :rule equiv_pos2) \
    (step t33 (cl (! (= @p_95 @p_92) :named @p_108)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_108 1 6)) \
    (step t34 (cl (= @p_39 @p_39)) :rule refl) \
    (step t35 (cl @p_107) :rule cong :premises (t33 t34)) \
    (step t36 (cl (not (! (= @p_10 (! (not (! (and @p_94 @p_36) :named @p_97)) :named @p_98)) :named @p_99)) (not @p_10) @p_98) :rule equiv_pos2) \
    (step t37 (cl (! (= @p_9 (! (and (! (<= b c) :named @p_101) (! (>= b c) :named @p_100)) :named @p_102)) :named @p_106)) :rule hole :args (\"THEORY_INFERENCE_ARITH\" \"THEORY_BV\" @p_106)) \
    (step t38 (cl (= @p_10 (! (not @p_102) :named @p_103))) :rule cong :premises (t37)) \
    (step t39 (cl (! (= @p_101 @p_94) :named @p_105)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_105 3 7)) \
    (step t40 (cl (! (= @p_100 @p_36) :named @p_104)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_104 3 7)) \
    (step t41 (cl (= @p_102 @p_97)) :rule cong :premises (t39 t40)) \
    (step t42 (cl (= @p_103 @p_98)) :rule cong :premises (t41)) \
    (step t43 (cl @p_99) :rule trans :premises (t38 t42)) \
    (step t44 (cl @p_98) :rule resolution :premises (t36 t43 a7)) \
    (step t45 (cl @p_95 @p_39) :rule not_and :premises (t44)) \
    (step t46 (cl @p_96 (not @p_95)) :rule or_neg :args (0)) \
    (step t47 (cl @p_96 @p_40) :rule or_neg :args (1)) \
    (step t48 (cl @p_96 @p_96) :rule resolution :premises (t45 t46 t47)) \
    (step t49 (cl @p_96) :rule contraction :premises (t48)) \
    (step t50 (cl @p_93) :rule resolution :premises (t32 t35 t49)) \
    (step t51 (cl @p_92 @p_39) :rule or :premises (t50)) \
    (step t52 (cl (not (! (= (! (or @p_94 (! (not (! (>= c 1) :named @p_179)) :named @p_181) (! (not (! (>= (! (+ a @p_25) :named @p_26) 1) :named @p_27)) :named @p_213) @p_258) :named @p_259) (! (or @p_94 @p_181 @p_213 @p_14) :named @p_257)) :named @p_288)) (not @p_259) @p_257) :rule equiv_pos2) \
    (step t53 (cl (= @p_94 @p_94)) :rule refl) \
    (step t54 (cl (= @p_181 @p_181)) :rule refl) \
    (step t55 (cl (= @p_213 @p_213)) :rule refl) \
    (step t56 (cl @p_288) :rule cong :premises (t53 t54 t55 t4)) \
    (step t57 (cl (! (=> (! (and @p_92 @p_179 @p_27 @p_15) :named @p_261) false) :named @p_263) @p_261) :rule implies_neg1) \
    (anchor :step t58) \
    (assume t58.a0 @p_92) \
    (assume t58.a1 @p_179) \
    (assume t58.a2 @p_27) \
    (assume t58.a3 @p_15) \
    (step t58.t0 (cl (! (not (! (= @p_15 (! (< a 3) :named @p_264)) :named @p_270)) :named @p_272) @p_258 @p_264) :rule equiv_pos2) \
    (step t58.t1 (cl (! (= @p_264 @p_15) :named @p_271)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_271 3 6)) \
    (step t58.t2 (cl @p_270) :rule symm :premises (t58.t1)) \
    (step t58.t3 (cl (! (not @p_16) :named @p_17) @p_18 @p_15) :rule equiv_pos2) \
    (step t58.t4 (cl @p_16) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_16 3 7)) \
    (step t58.t5 (cl @p_15) :rule resolution :premises (t58.t3 t58.t4 a1)) \
    (step t58.t6 (cl @p_264) :rule resolution :premises (t58.t0 t58.t2 t58.t5)) \
    (step t58.t7 (cl (not (! (= @p_14 (! (not @p_264) :named @p_265)) :named @p_287)) @p_15 @p_265) :rule equiv_pos2) \
    (step t58.t8 (cl (= @p_265 @p_258)) :rule cong :premises (t58.t1)) \
    (step t58.t9 (cl (! (= @p_265 @p_14) :named @p_285)) :rule trans :premises (t58.t8 t4)) \
    (step t58.t10 (cl @p_287) :rule symm :premises (t58.t9)) \
    (step t58.t11 (cl (not @p_285) (not @p_265) @p_14) :rule equiv_pos2) \
    (step t58.t12 (cl (! (=> @p_264 false) :named @p_266) @p_264) :rule implies_neg1) \
    (anchor :step t58.t13) \
    (assume t58.t13.a0 @p_264) \
    (step t58.t13.t0 (cl (not (! (= (! (< (! (+ a (! (* -1 @p_26) :named @p_236) @p_21 (! (* -1 @p_35) :named @p_128)) :named @p_268) (! (+ 3 @p_52 @p_52 @p_52) :named @p_267)) :named @p_269) false) :named @p_273)) (not @p_269) false) :rule equiv_pos2) \
    (step t58.t13.t1 (cl (! (= @p_269 (! (not (! (>= @p_268 @p_267) :named @p_274)) :named @p_275)) :named @p_284)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_284 3 6)) \
    (step t58.t13.t2 (cl (= a a)) :rule refl) \
    (step t58.t13.t3 (cl (! (= @p_236 (! (+ (! (* -1 a) :named @p_54) b) :named @p_279)) :named @p_283)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_283 3 7)) \
    (step t58.t13.t4 (cl (= @p_21 @p_21)) :rule refl) \
    (step t58.t13.t5 (cl (! (= @p_128 (! (+ @p_25 c) :named @p_278)) :named @p_282)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_282 3 7)) \
    (step t58.t13.t6 (cl (= @p_268 (! (+ a @p_279 @p_21 @p_278) :named @p_280))) :rule cong :premises (t58.t13.t2 t58.t13.t3 t58.t13.t4 t58.t13.t5)) \
    (step t58.t13.t7 (cl (! (= @p_280 0) :named @p_281)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_281 3 7)) \
    (step t58.t13.t8 (cl (= @p_268 0)) :rule trans :premises (t58.t13.t6 t58.t13.t7)) \
    (step t58.t13.t9 (cl (= 3 3)) :rule refl) \
    (step t58.t13.t10 (cl @p_83) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_83 3 7)) \
    (step t58.t13.t11 (cl (= @p_267 (! (+ 3 -1 -1 -1) :named @p_276))) :rule cong :premises (t58.t13.t9 t58.t13.t10 t58.t13.t10 t58.t13.t10)) \
    (step t58.t13.t12 (cl (! (= @p_276 0) :named @p_277)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_277 3 7)) \
    (step t58.t13.t13 (cl (= @p_267 0)) :rule trans :premises (t58.t13.t11 t58.t13.t12)) \
    (step t58.t13.t14 (cl (= @p_274 @p_79)) :rule cong :premises (t58.t13.t8 t58.t13.t13)) \
    (step t58.t13.t15 (cl @p_80) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_80 3 7)) \
    (step t58.t13.t16 (cl (= @p_274 true)) :rule trans :premises (t58.t13.t14 t58.t13.t15)) \
    (step t58.t13.t17 (cl (= @p_275 @p_77)) :rule cong :premises (t58.t13.t16)) \
    (step t58.t13.t18 (cl @p_78) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_78 1 7)) \
    (step t58.t13.t19 (cl (= @p_275 false)) :rule trans :premises (t58.t13.t17 t58.t13.t18)) \
    (step t58.t13.t20 (cl @p_273) :rule trans :premises (t58.t13.t1 t58.t13.t19)) \
    (step t58.t13.t21 (cl @p_265 (! (not (! (<= @p_236 @p_52) :named @p_241)) :named @p_244) (! (not (! (<= @p_21 @p_52) :named @p_192)) :named @p_198) (! (not (! (<= @p_128 @p_52) :named @p_131)) :named @p_139) @p_269) :rule la_generic :args (1/1 1/1 1/1 1/1 1/1)) \
    (step t58.t13.t22 (cl @p_272 @p_258 @p_264) :rule equiv_pos2) \
    (step t58.t13.t23 (cl @p_17 @p_18 @p_15) :rule equiv_pos2) \
    (step t58.t13.t24 (cl @p_15) :rule resolution :premises (t58.t13.t23 t58.t4 a1)) \
    (step t58.t13.t25 (cl @p_264) :rule resolution :premises (t58.t13.t22 t58.t2 t58.t13.t24)) \
    (step t58.t13.t26 (cl (=> (! (and @p_64 @p_27) :named @p_242) @p_241)) :rule la_mult_neg) \
    (step t58.t13.t27 (cl (! (not @p_242) :named @p_243) @p_241) :rule implies :premises (t58.t13.t26)) \
    (step t58.t13.t28 (cl @p_242 @p_67 @p_213) :rule and_neg) \
    (step t58.t13.t29 (cl (= @p_66 @p_64)) :rule equiv_simplify) \
    (step t58.t13.t30 (cl (not @p_66) @p_64) :rule equiv1 :premises (t58.t13.t29)) \
    (step t58.t13.t31 (cl @p_66) :rule rare_rewrite :args (\"evaluate\")) \
    (step t58.t13.t32 (cl @p_64) :rule resolution :premises (t58.t13.t30 t58.t13.t31)) \
    (step t58.t13.t33 (cl @p_242) :rule resolution :premises (t58.t13.t28 t58.t13.t32 t58.a2)) \
    (step t58.t13.t34 (cl @p_241) :rule resolution :premises (t58.t13.t27 t58.t13.t33)) \
    (step t58.t13.t35 (cl (=> (! (and @p_64 @p_179) :named @p_193) @p_192)) :rule la_mult_neg) \
    (step t58.t13.t36 (cl (not @p_193) @p_192) :rule implies :premises (t58.t13.t35)) \
    (step t58.t13.t37 (cl @p_193 @p_67 @p_181) :rule and_neg) \
    (step t58.t13.t38 (cl (not (! (= @p_5 @p_179) :named @p_180)) (not @p_5) @p_179) :rule equiv_pos2) \
    (step t58.t13.t39 (cl @p_180) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_180 3 7)) \
    (step t58.t13.t40 (cl @p_179) :rule resolution :premises (t58.t13.t38 t58.t13.t39 a4)) \
    (step t58.t13.t41 (cl @p_193) :rule resolution :premises (t58.t13.t37 t58.t13.t32 t58.t13.t40)) \
    (step t58.t13.t42 (cl @p_192) :rule resolution :premises (t58.t13.t36 t58.t13.t41)) \
    (step t58.t13.t43 (cl (=> (! (and @p_64 @p_92) :named @p_132) @p_131)) :rule la_mult_neg) \
    (step t58.t13.t44 (cl (! (not @p_132) :named @p_133) @p_131) :rule implies :premises (t58.t13.t43)) \
    (step t58.t13.t45 (cl @p_132 @p_67 @p_94) :rule and_neg) \
    (step t58.t13.t46 (cl @p_132) :rule resolution :premises (t58.t13.t45 t58.t13.t32 t58.a0)) \
    (step t58.t13.t47 (cl @p_131) :rule resolution :premises (t58.t13.t44 t58.t13.t46)) \
    (step t58.t13.t48 (cl @p_269) :rule resolution :premises (t58.t13.t21 t58.t13.t25 t58.t13.t34 t58.t13.t42 t58.t13.t47)) \
    (step t58.t13.t49 (cl false) :rule resolution :premises (t58.t13.t0 t58.t13.t20 t58.t13.t48)) \
    (step t58.t13 (cl @p_265 false) :rule subproof :discharge (t58.t13.a0)) \
    (step t58.t14 (cl @p_266 false) :rule resolution :premises (t58.t12 t58.t13)) \
    (step t58.t15 (cl @p_266 @p_13) :rule implies_neg2) \
    (step t58.t16 (cl @p_266 @p_266) :rule resolution :premises (t58.t14 t58.t15)) \
    (step t58.t17 (cl @p_266) :rule contraction :premises (t58.t16)) \
    (step t58.t18 (cl (= @p_266 @p_265)) :rule implies_simplify) \
    (step t58.t19 (cl (not @p_266) @p_265) :rule equiv1 :premises (t58.t18)) \
    (step t58.t20 (cl @p_265) :rule resolution :premises (t58.t17 t58.t19)) \
    (step t58.t21 (cl @p_14) :rule resolution :premises (t58.t11 t58.t9 t58.t20)) \
    (step t58.t22 (cl @p_265) :rule resolution :premises (t58.t7 t58.t10 t58.t21)) \
    (step t58.t23 (cl) :rule resolution :premises (t58.t6 t58.t22)) \
    (step t58 (cl @p_94 @p_181 @p_213 @p_258 false) :rule subproof :discharge (t58.a0 t58.a1 t58.a2 t58.a3)) \
    (step t59 (cl (! (not @p_261) :named @p_262) @p_92) :rule and_pos :args (0)) \
    (step t60 (cl @p_262 @p_179) :rule and_pos :args (1)) \
    (step t61 (cl @p_262 @p_27) :rule and_pos :args (2)) \
    (step t62 (cl @p_262 @p_15) :rule and_pos :args (3)) \
    (step t63 (cl false @p_262 @p_262 @p_262 @p_262) :rule resolution :premises (t58 t59 t60 t61 t62)) \
    (step t64 (cl @p_262 @p_262 @p_262 @p_262 false) :rule reordering :premises (t63)) \
    (step t65 (cl @p_262 false) :rule contraction :premises (t64)) \
    (step t66 (cl @p_263 false) :rule resolution :premises (t57 t65)) \
    (step t67 (cl @p_263 @p_13) :rule implies_neg2) \
    (step t68 (cl @p_263 @p_263) :rule resolution :premises (t66 t67)) \
    (step t69 (cl @p_263) :rule contraction :premises (t68)) \
    (step t70 (cl (= @p_263 @p_262)) :rule implies_simplify) \
    (step t71 (cl (not @p_263) @p_262) :rule equiv1 :premises (t70)) \
    (step t72 (cl @p_262) :rule resolution :premises (t69 t71)) \
    (step t73 (cl @p_94 @p_181 @p_213 @p_258) :rule not_and :premises (t72)) \
    (step t74 (cl @p_259 @p_95) :rule or_neg :args (0)) \
    (step t75 (cl @p_259 (! (not @p_181) :named @p_184)) :rule or_neg :args (1)) \
    (step t76 (cl @p_259 (! (not @p_213) :named @p_214)) :rule or_neg :args (2)) \
    (step t77 (cl @p_259 @p_260) :rule or_neg :args (3)) \
    (step t78 (cl @p_259 @p_259 @p_259 @p_259) :rule resolution :premises (t73 t74 t75 t76 t77)) \
    (step t79 (cl @p_259) :rule contraction :premises (t78)) \
    (step t80 (cl @p_257) :rule resolution :premises (t52 t56 t79)) \
    (step t81 (cl @p_94 @p_181 @p_213 @p_14) :rule or :premises (t80)) \
    (step t82 (cl @p_14 @p_213 @p_94 @p_181) :rule reordering :premises (t81)) \
    (step t83 (cl @p_17 @p_18 @p_15) :rule equiv_pos2) \
    (step t84 (cl @p_16) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_16 3 7)) \
    (step t85 (cl @p_15) :rule resolution :premises (t83 t84 a1)) \
    (step t86 (cl (not (! (= (! (or @p_214 (! (not (! (>= @p_26 0) :named @p_28)) :named @p_42)) :named @p_215) (! (or @p_27 @p_42) :named @p_212)) :named @p_226)) (not @p_215) @p_212) :rule equiv_pos2) \
    (step t87 (cl (! (= @p_214 @p_27) :named @p_227)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_227 1 6)) \
    (step t88 (cl (= @p_42 @p_42)) :rule refl) \
    (step t89 (cl @p_226) :rule cong :premises (t87 t88)) \
    (step t90 (cl (not (! (= @p_8 (! (not (! (and @p_213 @p_28) :named @p_216)) :named @p_217)) :named @p_218)) (not @p_8) @p_217) :rule equiv_pos2) \
    (step t91 (cl (! (= @p_7 (! (and (! (<= a b) :named @p_220) (! (>= a b) :named @p_219)) :named @p_221)) :named @p_225)) :rule hole :args (\"THEORY_INFERENCE_ARITH\" \"THEORY_BV\" @p_225)) \
    (step t92 (cl (= @p_8 (! (not @p_221) :named @p_222))) :rule cong :premises (t91)) \
    (step t93 (cl (! (= @p_220 @p_213) :named @p_224)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_224 3 7)) \
    (step t94 (cl (! (= @p_219 @p_28) :named @p_223)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_223 3 7)) \
    (step t95 (cl (= @p_221 @p_216)) :rule cong :premises (t93 t94)) \
    (step t96 (cl (= @p_222 @p_217)) :rule cong :premises (t95)) \
    (step t97 (cl @p_218) :rule trans :premises (t92 t96)) \
    (step t98 (cl @p_217) :rule resolution :premises (t90 t97 a6)) \
    (step t99 (cl @p_214 @p_42) :rule not_and :premises (t98)) \
    (step t100 (cl @p_215 (not @p_214)) :rule or_neg :args (0)) \
    (step t101 (cl @p_215 (! (not @p_42) :named @p_43)) :rule or_neg :args (1)) \
    (step t102 (cl @p_215 @p_215) :rule resolution :premises (t99 t100 t101)) \
    (step t103 (cl @p_215) :rule contraction :premises (t102)) \
    (step t104 (cl @p_212) :rule resolution :premises (t86 t89 t103)) \
    (step t105 (cl @p_27 @p_42) :rule or :premises (t104)) \
    (step t106 (cl (not (! (= (! (or @p_43 @p_181 @p_164 (! (not (! (not (! (>= b 3) :named @p_109)) :named @p_110)) :named @p_114)) :named @p_183) (! (or @p_28 @p_181 @p_164 @p_109) :named @p_182)) :named @p_211)) (not @p_183) @p_182) :rule equiv_pos2) \
    (step t107 (cl (! (= @p_43 @p_28) :named @p_91)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_91 1 6)) \
    (step t108 (cl (! (= @p_114 @p_109) :named @p_155)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_155 1 6)) \
    (step t109 (cl @p_211) :rule cong :premises (t107 t54 t3 t108)) \
    (step t110 (cl (! (=> (! (and @p_42 @p_179 @p_23 @p_110) :named @p_185) false) :named @p_187) @p_185) :rule implies_neg1) \
    (anchor :step t111) \
    (assume t111.a0 @p_42) \
    (assume t111.a1 @p_179) \
    (assume t111.a2 @p_23) \
    (assume t111.a3 @p_110) \
    (step t111.t0 (cl (! (not (! (= (! (> b 2) :named @p_123) (! (not @p_4) :named @p_112)) :named @p_156)) :named @p_159) (! (not @p_123) :named @p_160) @p_112) :rule equiv_pos2) \
    (step t111.t1 (cl @p_156) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_156 3 6)) \
    (step t111.t2 (cl (! (not (! (= @p_112 @p_123) :named @p_154)) :named @p_157) (! (not @p_112) :named @p_158) @p_123) :rule equiv_pos2) \
    (step t111.t3 (cl (! (= @p_4 @p_110) :named @p_111)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_111 3 7)) \
    (step t111.t4 (cl (= @p_112 @p_114)) :rule cong :premises (t111.t3)) \
    (step t111.t5 (cl (= @p_112 @p_109)) :rule trans :premises (t111.t4 t108)) \
    (step t111.t6 (cl (= @p_123 @p_109)) :rule trans :premises (t111.t1 t111.t5)) \
    (step t111.t7 (cl (= @p_109 @p_123)) :rule symm :premises (t111.t6)) \
    (step t111.t8 (cl @p_154) :rule trans :premises (t111.t5 t111.t7)) \
    (step t111.t9 (cl (! (=> @p_4 false) :named @p_124) @p_4) :rule implies_neg1) \
    (anchor :step t111.t10) \
    (assume t111.t10.a0 @p_4) \
    (step t111.t10.t0 (cl (not (! (= (! (< (! (+ b @p_189 @p_21 @p_26) :named @p_190) @p_188) :named @p_191) false) :named @p_199)) (not @p_191) false) :rule equiv_pos2) \
    (step t111.t10.t1 (cl (! (= @p_191 (! (not (! (>= @p_190 @p_188) :named @p_200)) :named @p_201)) :named @p_210)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_210 3 6)) \
    (step t111.t10.t2 (cl (! (= @p_190 @p_205) :named @p_209)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_209 3 6)) \
    (step t111.t10.t3 (cl @p_151) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_151 3 6)) \
    (step t111.t10.t4 (cl (= @p_25 @p_25)) :rule refl) \
    (step t111.t10.t5 (cl (= b b)) :rule refl) \
    (step t111.t10.t6 (cl @p_208) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_208 3 6)) \
    (step t111.t10.t7 (cl (= @p_205 @p_206)) :rule cong :premises (t111.t10.t3 t111.t10.t4 t111.t10.t5 t111.t10.t6)) \
    (step t111.t10.t8 (cl @p_207) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_207 3 7)) \
    (step t111.t10.t9 (cl (= @p_205 0)) :rule trans :premises (t111.t10.t7 t111.t10.t8)) \
    (step t111.t10.t10 (cl (= @p_190 0)) :rule trans :premises (t111.t10.t2 t111.t10.t9)) \
    (step t111.t10.t11 (cl (= 2 2)) :rule refl) \
    (step t111.t10.t12 (cl @p_83) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_83 3 7)) \
    (step t111.t10.t13 (cl (= 0 0)) :rule refl) \
    (step t111.t10.t14 (cl (= @p_188 @p_202)) :rule cong :premises (t111.t10.t11 t111.t10.t12 t111.t10.t12 t111.t10.t13)) \
    (step t111.t10.t15 (cl @p_203) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_203 3 7)) \
    (step t111.t10.t16 (cl (= @p_188 0)) :rule trans :premises (t111.t10.t14 t111.t10.t15)) \
    (step t111.t10.t17 (cl (= @p_200 @p_79)) :rule cong :premises (t111.t10.t10 t111.t10.t16)) \
    (step t111.t10.t18 (cl @p_80) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_80 3 7)) \
    (step t111.t10.t19 (cl (= @p_200 true)) :rule trans :premises (t111.t10.t17 t111.t10.t18)) \
    (step t111.t10.t20 (cl (= @p_201 @p_77)) :rule cong :premises (t111.t10.t19)) \
    (step t111.t10.t21 (cl @p_78) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_78 1 7)) \
    (step t111.t10.t22 (cl (= @p_201 false)) :rule trans :premises (t111.t10.t20 t111.t10.t21)) \
    (step t111.t10.t23 (cl @p_199) :rule trans :premises (t111.t10.t1 t111.t10.t22)) \
    (step t111.t10.t24 (cl @p_112 @p_197 @p_198 (! (not (! (< @p_26 0) :named @p_58)) :named @p_62) @p_191) :rule la_generic :args (1/1 1/1 1/1 1/1 1/1)) \
    (step t111.t10.t25 (cl (=> @p_195 @p_194)) :rule la_mult_neg) \
    (step t111.t10.t26 (cl @p_196 @p_194) :rule implies :premises (t111.t10.t25)) \
    (step t111.t10.t27 (cl @p_195 @p_67 @p_164) :rule and_neg) \
    (step t111.t10.t28 (cl (= @p_66 @p_64)) :rule equiv_simplify) \
    (step t111.t10.t29 (cl (not @p_66) @p_64) :rule equiv1 :premises (t111.t10.t28)) \
    (step t111.t10.t30 (cl @p_66) :rule rare_rewrite :args (\"evaluate\")) \
    (step t111.t10.t31 (cl @p_64) :rule resolution :premises (t111.t10.t29 t111.t10.t30)) \
    (step t111.t10.t32 (cl @p_195) :rule resolution :premises (t111.t10.t27 t111.t10.t31 t111.a2)) \
    (step t111.t10.t33 (cl @p_194) :rule resolution :premises (t111.t10.t26 t111.t10.t32)) \
    (step t111.t10.t34 (cl (=> @p_193 @p_192)) :rule la_mult_neg) \
    (step t111.t10.t35 (cl (not @p_193) @p_192) :rule implies :premises (t111.t10.t34)) \
    (step t111.t10.t36 (cl @p_193 @p_67 @p_181) :rule and_neg) \
    (step t111.t10.t37 (cl (not @p_180) (not @p_5) @p_179) :rule equiv_pos2) \
    (step t111.t10.t38 (cl @p_180) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_180 3 7)) \
    (step t111.t10.t39 (cl @p_179) :rule resolution :premises (t111.t10.t37 t111.t10.t38 a4)) \
    (step t111.t10.t40 (cl @p_193) :rule resolution :premises (t111.t10.t36 t111.t10.t31 t111.t10.t39)) \
    (step t111.t10.t41 (cl @p_192) :rule resolution :premises (t111.t10.t35 t111.t10.t40)) \
    (step t111.t10.t42 (cl (! (not (! (= @p_42 @p_58) :named @p_59)) :named @p_61) @p_43 @p_58) :rule equiv_pos2) \
    (step t111.t10.t43 (cl (! (= @p_58 @p_42) :named @p_60)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_60 3 6)) \
    (step t111.t10.t44 (cl @p_59) :rule symm :premises (t111.t10.t43)) \
    (step t111.t10.t45 (cl @p_58) :rule resolution :premises (t111.t10.t42 t111.t10.t44 t111.a0)) \
    (step t111.t10.t46 (cl @p_191) :rule resolution :premises (t111.t10.t24 t111.t10.a0 t111.t10.t33 t111.t10.t41 t111.t10.t45)) \
    (step t111.t10.t47 (cl false) :rule resolution :premises (t111.t10.t0 t111.t10.t23 t111.t10.t46)) \
    (step t111.t10 (cl @p_112 false) :rule subproof :discharge (t111.t10.a0)) \
    (step t111.t11 (cl @p_124 false) :rule resolution :premises (t111.t9 t111.t10)) \
    (step t111.t12 (cl @p_124 @p_13) :rule implies_neg2) \
    (step t111.t13 (cl @p_124 @p_124) :rule resolution :premises (t111.t11 t111.t12)) \
    (step t111.t14 (cl @p_124) :rule contraction :premises (t111.t13)) \
    (step t111.t15 (cl (! (= @p_124 @p_112) :named @p_126)) :rule implies_simplify) \
    (step t111.t16 (cl (! (not @p_124) :named @p_125) @p_112) :rule equiv1 :premises (t111.t15)) \
    (step t111.t17 (cl @p_112) :rule resolution :premises (t111.t14 t111.t16)) \
    (step t111.t18 (cl @p_123) :rule resolution :premises (t111.t2 t111.t8 t111.t17)) \
    (step t111.t19 (cl @p_112) :rule resolution :premises (t111.t0 t111.t1 t111.t18)) \
    (step t111.t20 (cl) :rule resolution :premises (a3 t111.t19)) \
    (step t111 (cl @p_43 @p_181 @p_164 @p_114 false) :rule subproof :discharge (t111.a0 t111.a1 t111.a2 t111.a3)) \
    (step t112 (cl (! (not @p_185) :named @p_186) @p_42) :rule and_pos :args (0)) \
    (step t113 (cl @p_186 @p_179) :rule and_pos :args (1)) \
    (step t114 (cl @p_186 @p_23) :rule and_pos :args (2)) \
    (step t115 (cl @p_186 @p_110) :rule and_pos :args (3)) \
    (step t116 (cl false @p_186 @p_186 @p_186 @p_186) :rule resolution :premises (t111 t112 t113 t114 t115)) \
    (step t117 (cl @p_186 @p_186 @p_186 @p_186 false) :rule reordering :premises (t116)) \
    (step t118 (cl @p_186 false) :rule contraction :premises (t117)) \
    (step t119 (cl @p_187 false) :rule resolution :premises (t110 t118)) \
    (step t120 (cl @p_187 @p_13) :rule implies_neg2) \
    (step t121 (cl @p_187 @p_187) :rule resolution :premises (t119 t120)) \
    (step t122 (cl @p_187) :rule contraction :premises (t121)) \
    (step t123 (cl (= @p_187 @p_186)) :rule implies_simplify) \
    (step t124 (cl (not @p_187) @p_186) :rule equiv1 :premises (t123)) \
    (step t125 (cl @p_186) :rule resolution :premises (t122 t124)) \
    (step t126 (cl @p_43 @p_181 @p_164 @p_114) :rule not_and :premises (t125)) \
    (step t127 (cl @p_183 (! (not @p_43) :named @p_47)) :rule or_neg :args (0)) \
    (step t128 (cl @p_183 @p_184) :rule or_neg :args (1)) \
    (step t129 (cl @p_183 @p_165) :rule or_neg :args (2)) \
    (step t130 (cl @p_183 (! (not @p_114) :named @p_118)) :rule or_neg :args (3)) \
    (step t131 (cl @p_183 @p_183 @p_183 @p_183) :rule resolution :premises (t126 t127 t128 t129 t130)) \
    (step t132 (cl @p_183) :rule contraction :premises (t131)) \
    (step t133 (cl @p_182) :rule resolution :premises (t106 t109 t132)) \
    (step t134 (cl @p_28 @p_181 @p_164 @p_109) :rule or :premises (t133)) \
    (step t135 (cl @p_109 @p_28 @p_164 @p_181) :rule reordering :premises (t134)) \
    (step t136 (cl (not @p_180) (not @p_5) @p_179) :rule equiv_pos2) \
    (step t137 (cl @p_180) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_180 3 7)) \
    (step t138 (cl @p_179) :rule resolution :premises (t136 t137 a4)) \
    (step t139 (cl (not @p_111) @p_112 @p_110) :rule equiv_pos2) \
    (step t140 (cl @p_111) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_111 3 7)) \
    (step t141 (cl @p_110) :rule resolution :premises (t139 t140 a3)) \
    (step t142 (cl (not (! (= (! (or @p_165 (! (not (! (>= @p_22 0) :named @p_24)) :named @p_115)) :named @p_166) (! (or @p_23 @p_115) :named @p_163)) :named @p_177)) (not @p_166) @p_163) :rule equiv_pos2) \
    (step t143 (cl (! (= @p_165 @p_23) :named @p_178)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_178 1 6)) \
    (step t144 (cl (= @p_115 @p_115)) :rule refl) \
    (step t145 (cl @p_177) :rule cong :premises (t143 t144)) \
    (step t146 (cl (not (! (= @p_12 (! (not (! (and @p_164 @p_24) :named @p_167)) :named @p_168)) :named @p_169)) (not @p_12) @p_168) :rule equiv_pos2) \
    (step t147 (cl (! (= @p_11 (! (and (! (<= a c) :named @p_171) (! (>= a c) :named @p_170)) :named @p_172)) :named @p_176)) :rule hole :args (\"THEORY_INFERENCE_ARITH\" \"THEORY_BV\" @p_176)) \
    (step t148 (cl (= @p_12 (! (not @p_172) :named @p_173))) :rule cong :premises (t147)) \
    (step t149 (cl (! (= @p_171 @p_164) :named @p_175)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_175 3 7)) \
    (step t150 (cl (! (= @p_170 @p_24) :named @p_174)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_174 3 7)) \
    (step t151 (cl (= @p_172 @p_167)) :rule cong :premises (t149 t150)) \
    (step t152 (cl (= @p_173 @p_168)) :rule cong :premises (t151)) \
    (step t153 (cl @p_169) :rule trans :premises (t148 t152)) \
    (step t154 (cl @p_168) :rule resolution :premises (t146 t153 a8)) \
    (step t155 (cl @p_165 @p_115) :rule not_and :premises (t154)) \
    (step t156 (cl @p_166 (not @p_165)) :rule or_neg :args (0)) \
    (step t157 (cl @p_166 (! (not @p_115) :named @p_116)) :rule or_neg :args (1)) \
    (step t158 (cl @p_166 @p_166) :rule resolution :premises (t155 t156 t157)) \
    (step t159 (cl @p_166) :rule contraction :premises (t158)) \
    (step t160 (cl @p_163) :rule resolution :premises (t142 t145 t159)) \
    (step t161 (cl @p_23 @p_115) :rule or :premises (t160)) \
    (step t162 (cl (not (! (= (! (or (! (not (! (>= a 1) :named @p_29)) :named @p_37) @p_94 @p_116 @p_114) :named @p_117) (! (or @p_37 @p_94 @p_24 @p_109) :named @p_113)) :named @p_161)) (not @p_117) @p_113) :rule equiv_pos2) \
    (step t163 (cl (= @p_37 @p_37)) :rule refl) \
    (step t164 (cl (! (= @p_116 @p_24) :named @p_162)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_162 1 6)) \
    (step t165 (cl @p_161) :rule cong :premises (t163 t53 t164 t108)) \
    (step t166 (cl (! (=> (! (and @p_29 @p_92 @p_115 @p_110) :named @p_120) false) :named @p_122) @p_120) :rule implies_neg1) \
    (anchor :step t167) \
    (assume t167.a0 @p_29) \
    (assume t167.a1 @p_92) \
    (assume t167.a2 @p_115) \
    (assume t167.a3 @p_110) \
    (step t167.t0 (cl @p_159 @p_160 @p_112) :rule equiv_pos2) \
    (step t167.t1 (cl @p_156) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_156 3 6)) \
    (step t167.t2 (cl @p_157 @p_158 @p_123) :rule equiv_pos2) \
    (step t167.t3 (cl (= @p_112 @p_114)) :rule cong :premises (t140)) \
    (step t167.t4 (cl (= @p_112 @p_109)) :rule trans :premises (t167.t3 t108)) \
    (step t167.t5 (cl (= @p_123 @p_109)) :rule trans :premises (t167.t1 t167.t4)) \
    (step t167.t6 (cl (= @p_109 @p_123)) :rule symm :premises (t167.t5)) \
    (step t167.t7 (cl @p_154) :rule trans :premises (t167.t4 t167.t6)) \
    (step t167.t8 (cl @p_124 @p_4) :rule implies_neg1) \
    (anchor :step t167.t9) \
    (assume t167.t9.a0 @p_4) \
    (step t167.t9.t0 (cl (not (! (= (! (< (! (+ b @p_22 @p_128 @p_54) :named @p_129) (! (+ 2 0 @p_52 @p_52) :named @p_127)) :named @p_130) false) :named @p_140)) (not @p_130) false) :rule equiv_pos2) \
    (step t167.t9.t1 (cl (! (= @p_130 (! (not (! (>= @p_129 @p_127) :named @p_141)) :named @p_142)) :named @p_153)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_153 3 6)) \
    (step t167.t9.t2 (cl (! (= @p_129 (! (+ @p_54 @p_146 (! (* 0 b) :named @p_145) a) :named @p_147)) :named @p_152)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_152 3 6)) \
    (step t167.t9.t3 (cl (= @p_54 @p_54)) :rule refl) \
    (step t167.t9.t4 (cl @p_151) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_151 3 6)) \
    (step t167.t9.t5 (cl (! (= @p_145 0) :named @p_150)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_150 3 6)) \
    (step t167.t9.t6 (cl (= a a)) :rule refl) \
    (step t167.t9.t7 (cl (= @p_147 (! (+ @p_54 0 0 a) :named @p_148))) :rule cong :premises (t167.t9.t3 t167.t9.t4 t167.t9.t5 t167.t9.t6)) \
    (step t167.t9.t8 (cl (! (= @p_148 0) :named @p_149)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_149 3 7)) \
    (step t167.t9.t9 (cl (= @p_147 0)) :rule trans :premises (t167.t9.t7 t167.t9.t8)) \
    (step t167.t9.t10 (cl (= @p_129 0)) :rule trans :premises (t167.t9.t2 t167.t9.t9)) \
    (step t167.t9.t11 (cl (= 2 2)) :rule refl) \
    (step t167.t9.t12 (cl (= 0 0)) :rule refl) \
    (step t167.t9.t13 (cl @p_83) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_83 3 7)) \
    (step t167.t9.t14 (cl (= @p_127 (! (+ 2 0 -1 -1) :named @p_143))) :rule cong :premises (t167.t9.t11 t167.t9.t12 t167.t9.t13 t167.t9.t13)) \
    (step t167.t9.t15 (cl (! (= @p_143 0) :named @p_144)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_144 3 7)) \
    (step t167.t9.t16 (cl (= @p_127 0)) :rule trans :premises (t167.t9.t14 t167.t9.t15)) \
    (step t167.t9.t17 (cl (= @p_141 @p_79)) :rule cong :premises (t167.t9.t10 t167.t9.t16)) \
    (step t167.t9.t18 (cl @p_80) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_80 3 7)) \
    (step t167.t9.t19 (cl (= @p_141 true)) :rule trans :premises (t167.t9.t17 t167.t9.t18)) \
    (step t167.t9.t20 (cl (= @p_142 @p_77)) :rule cong :premises (t167.t9.t19)) \
    (step t167.t9.t21 (cl @p_78) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_78 1 7)) \
    (step t167.t9.t22 (cl (= @p_142 false)) :rule trans :premises (t167.t9.t20 t167.t9.t21)) \
    (step t167.t9.t23 (cl @p_140) :rule trans :premises (t167.t9.t1 t167.t9.t22)) \
    (step t167.t9.t24 (cl @p_112 (! (not (! (< @p_22 0) :named @p_134)) :named @p_138) @p_139 (! (not (! (<= @p_54 @p_52) :named @p_63)) :named @p_73) @p_130) :rule la_generic :args (1/1 1/1 1/1 1/1 1/1)) \
    (step t167.t9.t25 (cl (! (not (! (= @p_115 @p_134) :named @p_135)) :named @p_137) @p_116 @p_134) :rule equiv_pos2) \
    (step t167.t9.t26 (cl (! (= @p_134 @p_115) :named @p_136)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_136 3 6)) \
    (step t167.t9.t27 (cl @p_135) :rule symm :premises (t167.t9.t26)) \
    (step t167.t9.t28 (cl @p_134) :rule resolution :premises (t167.t9.t25 t167.t9.t27 t167.a2)) \
    (step t167.t9.t29 (cl (=> @p_132 @p_131)) :rule la_mult_neg) \
    (step t167.t9.t30 (cl @p_133 @p_131) :rule implies :premises (t167.t9.t29)) \
    (step t167.t9.t31 (cl @p_132 @p_67 @p_94) :rule and_neg) \
    (step t167.t9.t32 (cl (= @p_66 @p_64)) :rule equiv_simplify) \
    (step t167.t9.t33 (cl (not @p_66) @p_64) :rule equiv1 :premises (t167.t9.t32)) \
    (step t167.t9.t34 (cl @p_66) :rule rare_rewrite :args (\"evaluate\")) \
    (step t167.t9.t35 (cl @p_64) :rule resolution :premises (t167.t9.t33 t167.t9.t34)) \
    (step t167.t9.t36 (cl @p_132) :rule resolution :premises (t167.t9.t31 t167.t9.t35 t167.a1)) \
    (step t167.t9.t37 (cl @p_131) :rule resolution :premises (t167.t9.t30 t167.t9.t36)) \
    (step t167.t9.t38 (cl (=> (! (and @p_64 @p_29) :named @p_65) @p_63)) :rule la_mult_neg) \
    (step t167.t9.t39 (cl (not @p_65) @p_63) :rule implies :premises (t167.t9.t38)) \
    (step t167.t9.t40 (cl @p_65 @p_67 @p_37) :rule and_neg) \
    (step t167.t9.t41 (cl (not (! (= @p_1 @p_29) :named @p_30)) (not @p_1) @p_29) :rule equiv_pos2) \
    (step t167.t9.t42 (cl @p_30) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_30 3 7)) \
    (step t167.t9.t43 (cl @p_29) :rule resolution :premises (t167.t9.t41 t167.t9.t42 a0)) \
    (step t167.t9.t44 (cl @p_65) :rule resolution :premises (t167.t9.t40 t167.t9.t35 t167.t9.t43)) \
    (step t167.t9.t45 (cl @p_63) :rule resolution :premises (t167.t9.t39 t167.t9.t44)) \
    (step t167.t9.t46 (cl @p_130) :rule resolution :premises (t167.t9.t24 t167.t9.a0 t167.t9.t28 t167.t9.t37 t167.t9.t45)) \
    (step t167.t9.t47 (cl false) :rule resolution :premises (t167.t9.t0 t167.t9.t23 t167.t9.t46)) \
    (step t167.t9 (cl @p_112 false) :rule subproof :discharge (t167.t9.a0)) \
    (step t167.t10 (cl @p_124 false) :rule resolution :premises (t167.t8 t167.t9)) \
    (step t167.t11 (cl @p_124 @p_13) :rule implies_neg2) \
    (step t167.t12 (cl @p_124 @p_124) :rule resolution :premises (t167.t10 t167.t11)) \
    (step t167.t13 (cl @p_124) :rule contraction :premises (t167.t12)) \
    (step t167.t14 (cl @p_126) :rule implies_simplify) \
    (step t167.t15 (cl @p_125 @p_112) :rule equiv1 :premises (t167.t14)) \
    (step t167.t16 (cl @p_112) :rule resolution :premises (t167.t13 t167.t15)) \
    (step t167.t17 (cl @p_123) :rule resolution :premises (t167.t2 t167.t7 t167.t16)) \
    (step t167.t18 (cl @p_112) :rule resolution :premises (t167.t0 t167.t1 t167.t17)) \
    (step t167.t19 (cl) :rule resolution :premises (a3 t167.t18)) \
    (step t167 (cl @p_37 @p_94 @p_116 @p_114 false) :rule subproof :discharge (t167.a0 t167.a1 t167.a2 t167.a3)) \
    (step t168 (cl (! (not @p_120) :named @p_121) @p_29) :rule and_pos :args (0)) \
    (step t169 (cl @p_121 @p_92) :rule and_pos :args (1)) \
    (step t170 (cl @p_121 @p_115) :rule and_pos :args (2)) \
    (step t171 (cl @p_121 @p_110) :rule and_pos :args (3)) \
    (step t172 (cl false @p_121 @p_121 @p_121 @p_121) :rule resolution :premises (t167 t168 t169 t170 t171)) \
    (step t173 (cl @p_121 @p_121 @p_121 @p_121 false) :rule reordering :premises (t172)) \
    (step t174 (cl @p_121 false) :rule contraction :premises (t173)) \
    (step t175 (cl @p_122 false) :rule resolution :premises (t166 t174)) \
    (step t176 (cl @p_122 @p_13) :rule implies_neg2) \
    (step t177 (cl @p_122 @p_122) :rule resolution :premises (t175 t176)) \
    (step t178 (cl @p_122) :rule contraction :premises (t177)) \
    (step t179 (cl (= @p_122 @p_121)) :rule implies_simplify) \
    (step t180 (cl (not @p_122) @p_121) :rule equiv1 :premises (t179)) \
    (step t181 (cl @p_121) :rule resolution :premises (t178 t180)) \
    (step t182 (cl @p_37 @p_94 @p_116 @p_114) :rule not_and :premises (t181)) \
    (step t183 (cl @p_117 (! (not @p_37) :named @p_48)) :rule or_neg :args (0)) \
    (step t184 (cl @p_117 @p_95) :rule or_neg :args (1)) \
    (step t185 (cl @p_117 (! (not @p_116) :named @p_119)) :rule or_neg :args (2)) \
    (step t186 (cl @p_117 @p_118) :rule or_neg :args (3)) \
    (step t187 (cl @p_117 @p_117 @p_117 @p_117) :rule resolution :premises (t182 t183 t184 t185 t186)) \
    (step t188 (cl @p_117) :rule contraction :premises (t187)) \
    (step t189 (cl @p_113) :rule resolution :premises (t162 t165 t188)) \
    (step t190 (cl @p_37 @p_94 @p_24 @p_109) :rule or :premises (t189)) \
    (step t191 (cl @p_109 @p_94 @p_24 @p_37) :rule reordering :premises (t190)) \
    (step t192 (cl (not @p_30) (not @p_1) @p_29) :rule equiv_pos2) \
    (step t193 (cl @p_30) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_30 3 7)) \
    (step t194 (cl @p_29) :rule resolution :premises (t192 t193 a0)) \
    (step t195 (cl @p_92 @p_39) :rule or :premises (t50)) \
    (step t196 (cl (not (! (= (! (or @p_37 @p_43 (! (not (! (not (! (>= c 3) :named @p_31)) :named @p_32)) :named @p_41) @p_40) :named @p_44) (! (or @p_37 @p_28 @p_31 @p_36) :named @p_38)) :named @p_88)) (not @p_44) @p_38) :rule equiv_pos2) \
    (step t197 (cl (! (= @p_41 @p_31) :named @p_90)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_90 1 6)) \
    (step t198 (cl @p_88) :rule cong :premises (t163 t107 t197 t1)) \
    (step t199 (cl (! (=> (! (and @p_29 @p_42 @p_32 @p_39) :named @p_49) false) :named @p_51) @p_49) :rule implies_neg1) \
    (anchor :step t200) \
    (assume t200.a0 @p_29) \
    (assume t200.a1 @p_42) \
    (assume t200.a2 @p_32) \
    (assume t200.a3 @p_39) \
    (step t200.t0 (cl (not (! (= (! (< (! (+ @p_35 @p_54 @p_26 c) :named @p_55) (! (+ 0 @p_52 -1 2) :named @p_53)) :named @p_56) false) :named @p_74)) (not @p_56) false) :rule equiv_pos2) \
    (step t200.t1 (cl (! (= @p_56 (! (not (! (>= @p_55 @p_53) :named @p_75)) :named @p_76)) :named @p_87)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_87 3 6)) \
    (step t200.t2 (cl (! (= @p_55 (! (+ @p_54 @p_21 @p_25 c b a) :named @p_84)) :named @p_86)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_86 3 6)) \
    (step t200.t3 (cl (! (= @p_84 0) :named @p_85)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_85 3 7)) \
    (step t200.t4 (cl (= @p_55 0)) :rule trans :premises (t200.t2 t200.t3)) \
    (step t200.t5 (cl (= 0 0)) :rule refl) \
    (step t200.t6 (cl @p_83) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_83 3 7)) \
    (step t200.t7 (cl (= -1 -1)) :rule refl) \
    (step t200.t8 (cl (= 2 2)) :rule refl) \
    (step t200.t9 (cl (= @p_53 (! (+ 0 -1 -1 2) :named @p_81))) :rule cong :premises (t200.t5 t200.t6 t200.t7 t200.t8)) \
    (step t200.t10 (cl (! (= @p_81 0) :named @p_82)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_82 3 7)) \
    (step t200.t11 (cl (= @p_53 0)) :rule trans :premises (t200.t9 t200.t10)) \
    (step t200.t12 (cl (= @p_75 @p_79)) :rule cong :premises (t200.t4 t200.t11)) \
    (step t200.t13 (cl @p_80) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_80 3 7)) \
    (step t200.t14 (cl (= @p_75 true)) :rule trans :premises (t200.t12 t200.t13)) \
    (step t200.t15 (cl (= @p_76 @p_77)) :rule cong :premises (t200.t14)) \
    (step t200.t16 (cl @p_78) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_78 1 7)) \
    (step t200.t17 (cl (= @p_76 false)) :rule trans :premises (t200.t15 t200.t16)) \
    (step t200.t18 (cl @p_74) :rule trans :premises (t200.t1 t200.t17)) \
    (step t200.t19 (cl @p_72 @p_73 (not (! (<= @p_26 -1) :named @p_57)) (! (not @p_6) :named @p_34) @p_56) :rule la_generic :args (1/1 1/1 1/1 1/1 1/1)) \
    (step t200.t20 (cl @p_71 @p_40 @p_68) :rule equiv_pos2) \
    (step t200.t21 (cl @p_70) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_70 3 6)) \
    (step t200.t22 (cl @p_69) :rule symm :premises (t200.t21)) \
    (step t200.t23 (cl @p_68) :rule resolution :premises (t200.t20 t200.t22 t200.a3)) \
    (step t200.t24 (cl (=> @p_65 @p_63)) :rule la_mult_neg) \
    (step t200.t25 (cl (not @p_65) @p_63) :rule implies :premises (t200.t24)) \
    (step t200.t26 (cl @p_65 @p_67 @p_37) :rule and_neg) \
    (step t200.t27 (cl (= @p_66 @p_64)) :rule equiv_simplify) \
    (step t200.t28 (cl (not @p_66) @p_64) :rule equiv1 :premises (t200.t27)) \
    (step t200.t29 (cl @p_66) :rule rare_rewrite :args (\"evaluate\")) \
    (step t200.t30 (cl @p_64) :rule resolution :premises (t200.t28 t200.t29)) \
    (step t200.t31 (cl @p_65) :rule resolution :premises (t200.t26 t200.t30 t194)) \
    (step t200.t32 (cl @p_63) :rule resolution :premises (t200.t25 t200.t31)) \
    (step t200.t33 (cl @p_62 @p_57) :rule la_generic :args (1/1 1/1)) \
    (step t200.t34 (cl @p_61 @p_43 @p_58) :rule equiv_pos2) \
    (step t200.t35 (cl @p_60) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_60 3 6)) \
    (step t200.t36 (cl @p_59) :rule symm :premises (t200.t35)) \
    (step t200.t37 (cl @p_58) :rule resolution :premises (t200.t34 t200.t36 t200.a1)) \
    (step t200.t38 (cl @p_57) :rule resolution :premises (t200.t33 t200.t37)) \
    (step t200.t39 (cl @p_56) :rule resolution :premises (t200.t19 t200.t23 t200.t32 t200.t38 a5)) \
    (step t200.t40 (cl false) :rule resolution :premises (t200.t0 t200.t18 t200.t39)) \
    (step t200 (cl @p_37 @p_43 @p_41 @p_40 false) :rule subproof :discharge (t200.a0 t200.a1 t200.a2 t200.a3)) \
    (step t201 (cl (! (not @p_49) :named @p_50) @p_29) :rule and_pos :args (0)) \
    (step t202 (cl @p_50 @p_42) :rule and_pos :args (1)) \
    (step t203 (cl @p_50 @p_32) :rule and_pos :args (2)) \
    (step t204 (cl @p_50 @p_39) :rule and_pos :args (3)) \
    (step t205 (cl false @p_50 @p_50 @p_50 @p_50) :rule resolution :premises (t200 t201 t202 t203 t204)) \
    (step t206 (cl @p_50 @p_50 @p_50 @p_50 false) :rule reordering :premises (t205)) \
    (step t207 (cl @p_50 false) :rule contraction :premises (t206)) \
    (step t208 (cl @p_51 false) :rule resolution :premises (t199 t207)) \
    (step t209 (cl @p_51 @p_13) :rule implies_neg2) \
    (step t210 (cl @p_51 @p_51) :rule resolution :premises (t208 t209)) \
    (step t211 (cl @p_51) :rule contraction :premises (t210)) \
    (step t212 (cl (= @p_51 @p_50)) :rule implies_simplify) \
    (step t213 (cl (not @p_51) @p_50) :rule equiv1 :premises (t212)) \
    (step t214 (cl @p_50) :rule resolution :premises (t211 t213)) \
    (step t215 (cl @p_37 @p_43 @p_41 @p_40) :rule not_and :premises (t214)) \
    (step t216 (cl @p_44 @p_48) :rule or_neg :args (0)) \
    (step t217 (cl @p_44 @p_47) :rule or_neg :args (1)) \
    (step t218 (cl @p_44 (! (not @p_41) :named @p_46)) :rule or_neg :args (2)) \
    (step t219 (cl @p_44 @p_45) :rule or_neg :args (3)) \
    (step t220 (cl @p_44 @p_44 @p_44 @p_44) :rule resolution :premises (t215 t216 t217 t218 t219)) \
    (step t221 (cl @p_44) :rule contraction :premises (t220)) \
    (step t222 (cl @p_38) :rule resolution :premises (t196 t198 t221)) \
    (step t223 (cl @p_37 @p_28 @p_31 @p_36) :rule or :premises (t222)) \
    (step t224 (cl @p_31 @p_28 @p_36 @p_37) :rule reordering :premises (t223)) \
    (step t225 (cl (not (! (= @p_6 @p_32) :named @p_33)) @p_34 @p_32) :rule equiv_pos2) \
    (step t226 (cl @p_33) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_33 3 7)) \
    (step t227 (cl @p_32) :rule resolution :premises (t225 t226 a5)) \
    (step t228 (cl @p_28) :rule resolution :premises (t135 t138 t141 t161 t191 t141 t194 t195 t224 t227 t194)) \
    (step t229 (cl @p_27) :rule resolution :premises (t105 t228)) \
    (step t230 (cl @p_94) :rule resolution :premises (t82 t85 t229 t138)) \
    (step t231 (cl @p_39) :rule resolution :premises (t51 t230)) \
    (step t232 (cl @p_23 @p_115) :rule or :premises (t160)) \
    (step t233 (cl (not (! (= (! (or @p_213 @p_41 @p_228 @p_116) :named @p_230) (! (or @p_213 @p_31 @p_228 @p_24) :named @p_229)) :named @p_256)) (not @p_230) @p_229) :rule equiv_pos2) \
    (step t234 (cl @p_256) :rule cong :premises (t55 t197 t2 t164)) \
    (step t235 (cl (! (=> (! (and @p_27 @p_32 @p_19 @p_115) :named @p_232) false) :named @p_234) @p_232) :rule implies_neg1) \
    (anchor :step t236) \
    (assume t236.a0 @p_27) \
    (assume t236.a1 @p_32) \
    (assume t236.a2 @p_19) \
    (assume t236.a3 @p_115) \
    (step t236.t0 (cl (not (! (= (! (< (! (+ @p_22 @p_236 c @p_25) :named @p_237) (! (+ 0 @p_52 2 @p_52) :named @p_235)) :named @p_238) false) :named @p_246)) (not @p_238) false) :rule equiv_pos2) \
    (step t236.t1 (cl (! (= @p_238 (! (not (! (>= @p_237 @p_235) :named @p_247)) :named @p_248)) :named @p_255)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_255 3 6)) \
    (step t236.t2 (cl (! (= @p_237 (! (+ @p_21 @p_145 c @p_204) :named @p_251)) :named @p_254)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_254 3 6)) \
    (step t236.t3 (cl (= @p_21 @p_21)) :rule refl) \
    (step t236.t4 (cl @p_150) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_150 3 6)) \
    (step t236.t5 (cl (= c c)) :rule refl) \
    (step t236.t6 (cl @p_208) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_208 3 6)) \
    (step t236.t7 (cl (= @p_251 (! (+ @p_21 0 c 0) :named @p_252))) :rule cong :premises (t236.t3 t236.t4 t236.t5 t236.t6)) \
    (step t236.t8 (cl (! (= @p_252 0) :named @p_253)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_253 3 7)) \
    (step t236.t9 (cl (= @p_251 0)) :rule trans :premises (t236.t7 t236.t8)) \
    (step t236.t10 (cl (= @p_237 0)) :rule trans :premises (t236.t2 t236.t9)) \
    (step t236.t11 (cl (= 0 0)) :rule refl) \
    (step t236.t12 (cl @p_83) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_83 3 7)) \
    (step t236.t13 (cl (= 2 2)) :rule refl) \
    (step t236.t14 (cl (= @p_235 (! (+ 0 -1 2 -1) :named @p_249))) :rule cong :premises (t236.t11 t236.t12 t236.t13 t236.t12)) \
    (step t236.t15 (cl (! (= @p_249 0) :named @p_250)) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_250 3 7)) \
    (step t236.t16 (cl (= @p_235 0)) :rule trans :premises (t236.t14 t236.t15)) \
    (step t236.t17 (cl (= @p_247 @p_79)) :rule cong :premises (t236.t10 t236.t16)) \
    (step t236.t18 (cl @p_80) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_80 3 7)) \
    (step t236.t19 (cl (= @p_247 true)) :rule trans :premises (t236.t17 t236.t18)) \
    (step t236.t20 (cl (= @p_248 @p_77)) :rule cong :premises (t236.t19)) \
    (step t236.t21 (cl @p_78) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_78 1 7)) \
    (step t236.t22 (cl (= @p_248 false)) :rule trans :premises (t236.t20 t236.t21)) \
    (step t236.t23 (cl @p_246) :rule trans :premises (t236.t1 t236.t22)) \
    (step t236.t24 (cl @p_138 @p_244 @p_34 @p_245 @p_238) :rule la_generic :args (1/1 1/1 1/1 1/1 1/1)) \
    (step t236.t25 (cl @p_137 @p_116 @p_134) :rule equiv_pos2) \
    (step t236.t26 (cl @p_136) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_136 3 6)) \
    (step t236.t27 (cl @p_135) :rule symm :premises (t236.t26)) \
    (step t236.t28 (cl @p_134) :rule resolution :premises (t236.t25 t236.t27 t236.a3)) \
    (step t236.t29 (cl (=> @p_242 @p_241)) :rule la_mult_neg) \
    (step t236.t30 (cl @p_243 @p_241) :rule implies :premises (t236.t29)) \
    (step t236.t31 (cl @p_242 @p_67 @p_213) :rule and_neg) \
    (step t236.t32 (cl (= @p_66 @p_64)) :rule equiv_simplify) \
    (step t236.t33 (cl (not @p_66) @p_64) :rule equiv1 :premises (t236.t32)) \
    (step t236.t34 (cl @p_66) :rule rare_rewrite :args (\"evaluate\")) \
    (step t236.t35 (cl @p_64) :rule resolution :premises (t236.t33 t236.t34)) \
    (step t236.t36 (cl @p_242) :rule resolution :premises (t236.t31 t236.t35 t236.a0)) \
    (step t236.t37 (cl @p_241) :rule resolution :premises (t236.t30 t236.t36)) \
    (step t236.t38 (cl (=> @p_240 @p_239)) :rule la_mult_neg) \
    (step t236.t39 (cl (not @p_240) @p_239) :rule implies :premises (t236.t38)) \
    (step t236.t40 (cl @p_240 @p_67 @p_228) :rule and_neg) \
    (step t236.t41 (cl (not @p_20) (not @p_3) @p_19) :rule equiv_pos2) \
    (step t236.t42 (cl @p_20) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_20 3 7)) \
    (step t236.t43 (cl @p_19) :rule resolution :premises (t236.t41 t236.t42 a2)) \
    (step t236.t44 (cl @p_240) :rule resolution :premises (t236.t40 t236.t35 t236.t43)) \
    (step t236.t45 (cl @p_239) :rule resolution :premises (t236.t39 t236.t44)) \
    (step t236.t46 (cl @p_238) :rule resolution :premises (t236.t24 t236.t28 t236.t37 a5 t236.t45)) \
    (step t236.t47 (cl false) :rule resolution :premises (t236.t0 t236.t23 t236.t46)) \
    (step t236 (cl @p_213 @p_41 @p_228 @p_116 false) :rule subproof :discharge (t236.a0 t236.a1 t236.a2 t236.a3)) \
    (step t237 (cl (! (not @p_232) :named @p_233) @p_27) :rule and_pos :args (0)) \
    (step t238 (cl @p_233 @p_32) :rule and_pos :args (1)) \
    (step t239 (cl @p_233 @p_19) :rule and_pos :args (2)) \
    (step t240 (cl @p_233 @p_115) :rule and_pos :args (3)) \
    (step t241 (cl false @p_233 @p_233 @p_233 @p_233) :rule resolution :premises (t236 t237 t238 t239 t240)) \
    (step t242 (cl @p_233 @p_233 @p_233 @p_233 false) :rule reordering :premises (t241)) \
    (step t243 (cl @p_233 false) :rule contraction :premises (t242)) \
    (step t244 (cl @p_234 false) :rule resolution :premises (t235 t243)) \
    (step t245 (cl @p_234 @p_13) :rule implies_neg2) \
    (step t246 (cl @p_234 @p_234) :rule resolution :premises (t244 t245)) \
    (step t247 (cl @p_234) :rule contraction :premises (t246)) \
    (step t248 (cl (= @p_234 @p_233)) :rule implies_simplify) \
    (step t249 (cl (not @p_234) @p_233) :rule equiv1 :premises (t248)) \
    (step t250 (cl @p_233) :rule resolution :premises (t247 t249)) \
    (step t251 (cl @p_213 @p_41 @p_228 @p_116) :rule not_and :premises (t250)) \
    (step t252 (cl @p_230 @p_214) :rule or_neg :args (0)) \
    (step t253 (cl @p_230 @p_46) :rule or_neg :args (1)) \
    (step t254 (cl @p_230 @p_231) :rule or_neg :args (2)) \
    (step t255 (cl @p_230 @p_119) :rule or_neg :args (3)) \
    (step t256 (cl @p_230 @p_230 @p_230 @p_230) :rule resolution :premises (t251 t252 t253 t254 t255)) \
    (step t257 (cl @p_230) :rule contraction :premises (t256)) \
    (step t258 (cl @p_229) :rule resolution :premises (t233 t234 t257)) \
    (step t259 (cl @p_213 @p_31 @p_228 @p_24) :rule or :premises (t258)) \
    (step t260 (cl @p_31 @p_213 @p_24 @p_228) :rule reordering :premises (t259)) \
    (step t261 (cl (not @p_20) (not @p_3) @p_19) :rule equiv_pos2) \
    (step t262 (cl @p_20) :rule hole :args (\"TRUST_THEORY_REWRITE\" @p_20 3 7)) \
    (step t263 (cl @p_19) :rule resolution :premises (t261 t262 a2)) \
    (step t264 (cl @p_24) :rule resolution :premises (t260 t227 t229 t263)) \
    (step t265 (cl @p_23) :rule resolution :premises (t232 t264)) \
    (step t266 (cl) :rule resolution :premises (t31 t231 t265 t263 t85)) \
    )"
#print axioms alethe_walker_pigeonhole3_axiom_free

/- ============================================================
   Identity-trace guard (R2)
   ============================================================

   The dispatch pipeline (prop-simp + registry def-unfold) now runs
   inside `Dispatch.run` on every dispatch. A hypothesis of shape
   `True ∧ P` is a prop-simp redex (And_True_left), so dispatching
   these goals produces a NON-identity trace: the cert addresses the
   rewritten IR, not the reified goal. The guard must (a) keep plain
   `proof_broker` closing via the decision-procedure fallback on the
   original goal, and (b) make the cert-consuming closers
   (`proof_broker_walker`, `proof_broker_term`) fail with the named
   guard error instead of consuming the cert against the wrong
   goal. -/

/-- (a) Non-identity trace falls back and still closes: the walker
    is guard-skipped, cert-gated `omega` proves the original goal.
    The footprint stays axiom-free — omega is the proof emitter. -/
theorem pb_guard_nonidentity_falls_back_axiom_free
    (x : Int) (h : True ∧ x ≤ 5) : x ≤ 5 := by
  proof_broker
#print axioms pb_guard_nonidentity_falls_back_axiom_free

/-- (b) Walker-strict on a rewritten dispatch fails closed with the
    guard error; the goal stays open and is then closed honestly. -/
example (x : Int) (h : True ∧ x ≤ 5) : x ≤ 5 := by
  fail_if_success proof_broker_walker
  omega

/-- (b') Term mode on a rewritten dispatch fails closed with the
    guard error; the goal stays open and is then closed honestly. -/
example (x : Int) (h : True ∧ x ≤ 5) : x ≤ 5 := by
  fail_if_success proof_broker_term
  omega

/- ============================================================
   R3-M1: ℕ→ℤ specialization + lift

   The reifier hands the broker the ℤ image of a ℕ goal (cast
   shells, `_pb_nonneg_*` hypotheses, primitive-kind metadata with
   real embedding witnesses); the cert-consuming closers rebuild
   the ℕ proof from the ℤ certificate through the `natCast*` shims.
   Positive tests pin each lift leg's footprint; negative tests pin
   the fail-fast scope rules — ℕ subtraction (the truncation attack
   surface), division, nested ℕ quantifiers, ℕ×UF mixing.
   ============================================================ -/

/-- Plain `proof_broker` on ℕ: reify ℤ image → dispatch → cert
    gates omega on the original ℕ goal. -/
theorem pb_nat_plain (x y : Nat) (h1 : x + 1 ≤ y) (h2 : y ≤ 5) :
    x ≤ 4 := by
  proof_broker
#print axioms pb_nat_plain

/-- Term mode on ℕ: the Tier-1 Farkas witness is consumed against
    the ℤ images of the hypotheses (cast by term construction via
    `natCastLe`/`natCastNonneg`), the goal enters through the
    axiom-free `natLeViaLt` wrapper — no decision procedure touches
    the original goal. -/
theorem pb_nat_term (x y : Nat) (h1 : x + 1 ≤ y) (h2 : y ≤ 5) :
    x ≤ 4 := by
  proof_broker_term
#print axioms pb_nat_term

/-- Walker-strict on ℕ: the live cvc5 alethe trace is walked into a
    kernel term through the cast layer ("cert IS the proof" at ℕ). -/
theorem pb_nat_walker (x y : Nat) (h1 : x + 1 ≤ y) (h2 : y ≤ 5) :
    x ≤ 4 := by
  proof_broker_walker
#print axioms pb_nat_walker

/-- 2^24-scale literals: the reifier constant-folds the closed pow;
    the walker matches the folded literal by kernel defeq. -/
theorem pb_nat_walker_pow (x : Nat) (h : x < 2^24) : x ≤ 16777215 := by
  proof_broker_walker
#print axioms pb_nat_walker_pow

/-- A leading `∀ (n : ℕ)` goal binder is introduced before
    reification; the introduced form dispatches and walks. -/
theorem pb_nat_walker_forall : ∀ n : Nat, n + 1 ≥ 1 := by
  proof_broker_walker
#print axioms pb_nat_walker_forall

/-- The D1 shape (verinf `lift_cell` core): a nonlinear ℕ product
    `zmax * zhigh` is atomized to an `Opaque` payload atom, its
    bound rides along as a hypothesis, and the goal closes through
    the walker with the atom mapped back to `↑(zmax * zhigh)`. -/
theorem pb_nat_walker_d1 (x z zmax zhigh : Nat)
    (hx : x < 2^24) (hz : z < 2 * zmax)
    (_hprod : zmax * zhigh ≤ zmax) :
    x + z < 2^24 + 2 * zmax := by
  proof_broker_walker
#print axioms pb_nat_walker_d1

/-- Term mode consumes the atomized product: the atom is the middle
    variable of a bound chain, so the Farkas witness names both its
    bound and its nonneg fact. (Term mode needs a Tier-1 cert, and
    cvc5 emits `la_generic` only for real multi-hypothesis
    combinations — shape chosen accordingly, like every other
    `pb_term_*` test.) -/
theorem pb_nat_term_d1 (x zmax zhigh : Nat)
    (hx : x + 1 ≤ zmax * zhigh) (hp : zmax * zhigh ≤ 5) :
    x ≤ 4 := by
  proof_broker_term
#print axioms pb_nat_term_d1

/-- ℕ equality goal: split via `Nat.le_antisymm`, each direction a
    fresh dispatch + lift. Both directions are multi-hypothesis
    combinations (so each mints a Tier-1 Farkas witness). -/
theorem pb_nat_term_eq (x y w : Nat)
    (h1 : x + 1 ≤ y) (h2 : y ≤ 5)
    (h3 : 6 ≤ x + 2 * w) (h4 : w ≤ 1) : x = 4 := by
  proof_broker_term
#print axioms pb_nat_term_eq

/-- ATTACK SURFACE (fail fast): ℕ subtraction is truncated — the
    reifier refuses it with a named error rather than cast naively.
    The whole tactic aborts BEFORE dispatch, so even plain
    `proof_broker`'s omega fallback never sees the goal. -/
example (a b : Nat) (h : a - b ≤ 3) : a - b ≤ 4 := by
  fail_if_success proof_broker
  omega

/-- Fail fast: ℕ division is outside the specialization. -/
example (a : Nat) (h : a / 2 ≤ 3) : a / 2 ≤ 4 := by
  fail_if_success proof_broker
  omega

/-- Fail fast: a ℕ quantifier INSIDE the GOAL has no ℤ image yet.
    The goal is never dropped, so this aborts before dispatch. -/
example (x : Nat) : True → ∀ n : Nat, x ≤ x + n := by
  fail_if_success proof_broker
  intro _ n
  omega

/-- R4.2 counterpart: the same shape in HYPOTHESIS position is
    DROPPED, not misread — `buildIR` records it in `skippedLocals`
    and reifies the rest. The goal here is unprovable without `h`,
    so the tactic still fails (no certificate); what it must never
    do is close the goal by reading `h` wrongly. -/
example (x : Nat) (h : ∀ n : Nat, x + n ≤ 3) : x ≤ 3 := by
  fail_if_success proof_broker
  have := h 0
  omega

/-- Fail fast: ℕ arithmetic cannot mix with UF carriers in M1. -/
example (x : Nat) (f : Int → Int) (hf : f 0 = 0) (h : x ≤ 3) :
    x ≤ 4 := by
  fail_if_success proof_broker
  omega

/-- Fail fast even under atomization (C3a ROUND 1 finding 5): a
    nonlinear product HIDING ℕ subtraction is refused with the named
    error, not silently swallowed as an Opaque atom. -/
example (a b c : Nat) (h : (a - b) * c ≤ 3) : (a - b) * c ≤ 4 := by
  fail_if_success proof_broker
  omega

/-- ROUND 2 finding 6 (probe-derived): the atom scan matches the
    directly-spelled core name, not just the `-` notation head. -/
example (a b c : Nat) (h : Nat.sub a b * c ≤ 3) :
    Nat.sub a b * c ≤ 4 := by
  fail_if_success proof_broker
  omega

/-- ROUND 2 finding 6 (probe-derived): `Nat.pred` is truncated
    subtraction by one — refused inside atoms like `Nat.sub`. -/
example (a c : Nat) (h : Nat.pred a * c ≤ 3) :
    Nat.pred a * c ≤ 4 := by
  fail_if_success proof_broker
  omega

/- The R3-M1 specialization gate, pinned fail-closed INDEPENDENT of
   live dispatch (C3a ROUND 1 finding 2): no live path mints a foreign
   specialization or a spec-less ℕ cert, so these drive the real
   `checkCertSpecializations` on synthetic certs. Deleting the "cannot
   invert" branch flips the foreign/mixed tests; deleting the "records
   no Nat → Int" branch flips the nat-none test. -/

/-- Positive control: the exact invertible record passes. -/
example : True := by spec_gate_test nat nat_spec

/-- Positive control: non-ℕ extraction with no records passes. -/
example : True := by spec_gate_test int none

/-- ℕ mode with NO recorded specialization → fail closed. -/
example : True := by
  fail_if_success spec_gate_test nat none
  trivial

/-- A specialization this bridge cannot invert → fail closed. -/
example : True := by
  fail_if_success spec_gate_test int foreign_spec
  trivial

/-- A foreign record riding NEXT TO a valid Nat → Int record still
    fails closed (the gate rejects per-record, not first-match). -/
example : True := by
  fail_if_success spec_gate_test nat mixed_spec
  trivial

/- R3-M2: the gate's `poly` mode (the term-mode path on an α
   extraction). The alpha → Int record is the invertible set there —
   and ONLY there: the walker-path modes above keep refusing it
   (`spec_gate_test int foreign_spec` stays a negative). -/

/-- Positive control: the alpha → Int record passes in poly mode. -/
example : True := by spec_gate_test poly foreign_spec

/-- α mode with NO recorded specialization → fail closed. -/
example : True := by
  fail_if_success spec_gate_test poly none
  trivial

/-- A Nat → Int record on an α extraction → fail closed (the α
    replay does not invert the ℕ cast layer). -/
example : True := by
  fail_if_success spec_gate_test poly nat_spec
  trivial

/-- A record foreign in EVERY mode (beta → Real) → fail closed. -/
example : True := by
  fail_if_success spec_gate_test poly beta_spec
  trivial

/- ============================================================
   R3-M3: definitional metadata + def-unfold inversion.

   A numeral-body constant reifies as an opaque leaf plus a
   `defined_function` metadata entry; the dispatch pipeline's
   definition-unfolding pass (the registry's always-unfold
   `numeral_definition` concept + the reifier's directive) replaces
   it by the numeral, the trace records the unfold, and the
   term-mode lift inverts it by `Eq.mpr` over the kernel-defeq
   unfolding equation before consuming the cert. The closures below
   are load-bearing evidence the pass genuinely fired: with `P`
   opaque, `Zmax < P` is not even provable, so no cert exists.
   ============================================================ -/

/-- The R4-D2 constant: 2^64 − 2^32 + 1 as a plain decimal def. -/
def P : Nat := 18446744069414584321

/-- THE M3 gate (the D2 shape): closes `by proof_broker_term` with
    the def-unfold pass in the trace and inverted in the term. -/
theorem pb_nat_def_unfold (Zmax : Nat) (h : Zmax ≤ 2^16) : Zmax < P := by
  proof_broker_term
#print axioms pb_nat_def_unfold

/-- Plain mode: the LIA arm applies the same inversion before its
    cert-gated omega (omega cannot see through a non-reducible
    def). -/
theorem pb_nat_def_unfold_plain (Zmax : Nat) (h : Zmax ≤ 2^16) :
    Zmax < P := by
  proof_broker
#print axioms pb_nat_def_unfold_plain

def Qdef : Nat := 65536

/-- A numeral def in HYPOTHESIS position is unfolded and inverted
    (defeq type swap on the hypothesis) too. -/
theorem pb_nat_def_unfold_hyp (Zmax : Nat) (h : Zmax ≤ Qdef) :
    Zmax < P := by
  proof_broker_term
#print axioms pb_nat_def_unfold_hyp

/-- Walker-strict stays IDENTITY-only (M3 lifts the guard for the
    term-mode path, not the walker): named fail-closed error. -/
example (Zmax : Nat) (h : Zmax ≤ 2^16) : Zmax < P := by
  fail_if_success proof_broker_walker
  show Zmax < 18446744069414584321
  omega

def Qbad : Nat := 6 * 7

/-- Fail fast: a constant whose body is NOT a numeral is outside
    the M3 scope — named reifier error, nothing dispatches. -/
example (x : Nat) (h : x ≤ 3) : x < Qbad := by
  fail_if_success proof_broker_term
  fail_if_success proof_broker
  show x < 42
  omega

/- The M3 trace guard, pinned branch-by-branch on synthetic traces
   (`trace_guard_test` drives the real `termTraceError?`; no live
   path produces a foreign unfold or a non-invertible applied
   pass... except prop-simp, whose live firing is covered by the R2
   guard tests above). -/

/-- Positive control: identity trace passes. -/
example : True := by trace_guard_test identity

/-- Positive control: an applied unfold of a symbol this extraction
    emitted passes (the M3 admission). -/
example : True := by trace_guard_test def_unfold_ours

/-- Deterministic two-direction pin for the def-unfold
    type-position gate (C4 ROUND 3 Med 1); see `type_pos_gate_test`. -/
def PBGateC : Nat := 41
example : True := by type_pos_gate_test PBGateC

/-- Deterministic RUNTIME pin for the per-call reify accumulators
    (C4 ROUND 4 finding 1; all four fields since ROUND 5): red on
    every run under any re-sharing inside `ReifyAcc.fresh`. The
    call-site/module-state half of the discipline is pinned by
    `check_lean_reify_isolation` in `tools/check.py` (ROUND 6
    Med 1). -/
example : True := by reify_acc_isolation_test

/-- CALL-SITE isolation pin (C4 ROUND 8 Med 1): the accumulators two
    real `buildIRWithAcc` runs actually used must be distinct state
    — red whenever `buildIRWithAcc` returns the accumulator it
    accumulated into (every single-accumulator mutation), because it
    observes aliasing rather than source text; the decoy direction
    is a documented residual (delta §5.7). The goal carries a
    nonlinear ℕ product so run 1 mints an atom to watch. -/
example (x y : Nat) (h : x * y ≤ 5) : x * y ≤ 6 := by
  reify_callsite_isolation_test

/-- An applied unfold of a FOREIGN symbol → fail closed. -/
example : True := by
  fail_if_success trace_guard_test def_unfold_foreign
  trivial

/-- An applied unfold naming NO symbols (absent/malformed/empty
    `inversion_data`) → fail closed, not a vacuous pass over zero
    inversions. -/
example : True := by
  fail_if_success trace_guard_test def_unfold_empty
  trivial

/-- Endpoint hashes disagree but the entry list is EMPTY → fail
    closed (no entry admits the rewrite; admission must mean an
    inversion ran). -/
example : True := by
  fail_if_success trace_guard_test endpoints_no_entries
  trivial

/-- Endpoint hashes disagree but every entry is identity-shaped
    (`no_op`, equal per-entry hashes) → fail closed, same rule. -/
example : True := by
  fail_if_success trace_guard_test endpoints_all_noop
  trivial

/-- An applied pass with no inversion (prop-simp) → fail closed. -/
example : True := by
  fail_if_success trace_guard_test prop_simp_applied
  trivial

/-- A Failed definition_unfolding entry → fail closed (only APPLIED
    unfolds are admitted). -/
example : True := by
  fail_if_success trace_guard_test failed_pass
  trivial

/-- A missing trace → fail closed. -/
example : True := by
  fail_if_success trace_guard_test no_trace
  trivial


/- ============================================================
   R4.2 — the verinf bracket-spike obligation shapes

   These are the fragment features the demo project needs, pinned
   here so a regression shows up in this repo's own CI and not only
   in `proof-broker-demo`. Each mirrors a numbered obligation of
   `lean/BracketSpike/BracketSpike/Bracket.lean` on verinf's
   `lean-bracket-spike` branch; the Mathlib-flavored shapes
   (`ZMod.val`, `Fin n`) live in `Test/TacticMathlib.lean`.
   ============================================================ -/

/-- The demo's Goldilocks modulus, as a numeral-body definition —
    the R3-M3 `defined_function` shape. -/
private def pbP : Nat := 18446744069414584321

/-- D2 / `Bracket.lean:56`. Closed power against a definition. -/
theorem pb_r4_d2_pow_lt_def : (2:Nat)^16 < pbP := by proof_broker
#print axioms pb_r4_d2_pow_lt_def

/-- D2 / `Bracket.lean:62`. R4.2: `2^16 * 2^16` has no literal
    factor, so before closed-numeral folding it atomized into an
    unbounded `Opaque` atom and NO adapter could mint a cert. -/
theorem pb_r4_d2_pow_mul_lt_def : (2:Nat)^16 * 2^16 < pbP := by proof_broker
#print axioms pb_r4_d2_pow_mul_lt_def

/-- D2 / `Bracket.lean:66`. -/
theorem pb_r4_d2_sum_le_def : (2:Nat)^24 + 2 * 2^16 ≤ pbP := by proof_broker
#print axioms pb_r4_d2_sum_le_def

/-- D2 / `Bracket.lean:34` (the `NeZero` instance body). -/
theorem pb_r4_d2_ne_zero : pbP ≠ 0 := by proof_broker
#print axioms pb_r4_d2_ne_zero

/-- D1 / `Bracket.lean:70`. `2 * Zmax` stays linear, `pbP` unfolds,
    and the bound on `Zmax` is what closes it. -/
theorem pb_r4_d1_hle (Zmax : Nat) (hZ : Zmax ≤ 2^16) :
    (2:Nat)^24 + 2 * Zmax ≤ pbP := by proof_broker_term
#print axioms pb_r4_d1_hle

/-- D1 / `Bracket.lean:78`. Two products: `Zmax * zhigh` is the
    genuine nonlinear atom, `Zmax * 2^16` is LINEAR and must not be
    atomized — the ROADMAP's named attack surface ("an `Opaque` atom
    that is not actually opaque"). -/
theorem pb_r4_d1_hlt (xv zv Zmax zhv : Nat) (hx : xv < 2^24)
    (hz : zv < 2 * Zmax) (hprod_le : Zmax * zhv ≤ Zmax * 2^16) :
    xv + zv + Zmax * zhv < 2^24 + 2 * Zmax + Zmax * 2^16 := by
  proof_broker_term
#print axioms pb_r4_d1_hlt

/-- R4.2 scope pin: a closed power outside the folding bounds is a
    NAMED error, never a silent `Opaque` atom. -/
example (h : (2:Nat)^300 < 2^301) : (2:Nat)^300 < 2^301 := by
  fail_if_success proof_broker
  exact h

/-- The over-bounds power nested in a BASE position: the `HPow`
    guard's first conjunct fails (the base is closed-but-declined),
    so control used to fall through to silent atomization — now the
    same named bounds refusal (`natClosedShape`). -/
example (h : ((2:Nat)^5000)^2 ≤ ((2:Nat)^5000)^2) :
    ((2:Nat)^5000)^2 ≤ ((2:Nat)^5000)^2 := by
  fail_if_success proof_broker
  exact h

/-- A closed PRODUCT of two over-bounds powers: exponent 300 > 256
    means neither factor folds, so the `HMul` arm saw two non-closed
    operands and used to atomize the product silently — falsifying
    its own "both operands closed is already folded" comment. Named
    refusal now. -/
example (h : (2:Nat)^300 * (2:Nat)^300 ≤ (2:Nat)^300 * (2:Nat)^300) :
    (2:Nat)^300 * (2:Nat)^300 ≤ (2:Nat)^300 * (2:Nat)^300 := by
  fail_if_success proof_broker
  exact h

/-- R4.2: an applied ℕ-valued function (`ZMod.val` in the demo,
    `List.length` here — a constant application, not a UF free var)
    is an opaque atom carrying only `0 ≤ ↑atom`, and the same
    application in hypothesis and goal is ONE atom. -/
theorem pb_r4_nat_app_atom (l k : List Nat) (Zmax : Nat)
    (hx : l.length < 2^24) (hz : k.length < 2 * Zmax) :
    l.length + k.length < 2^24 + 2 * Zmax := by proof_broker_term
#print axioms pb_r4_nat_app_atom

/-- R4.2 fail-closed: ℕ subtraction hidden inside an atomized
    APPLICATION is refused, exactly as inside an atomized product. -/
private def pbSucc (k : Nat) : Nat := k + 1
example (n m : Nat) (h : (pbSucc (n - m)).succ ≤ 3) :
    (pbSucc (n - m)).succ ≤ 4 := by
  fail_if_success proof_broker
  omega

/-- R4.2: an unapplied ℕ constant with a non-numeral body is still a
    scope error — atomizing it would hide the R3-M3 definition
    pass failing. -/
private def pbQ : Nat := Nat.succ 41
example : pbQ ≤ 42 := by
  fail_if_success proof_broker
  decide

/-- D3 / `Bracket.lean:175`. A nonlinear Int product is an `Opaque`
    Int atom: emitted verbatim, cvc5 rejected the whole script with
    "A non-linear fact was asserted to arithmetic in a linear
    logic" and no certificate was minted. -/
theorem pb_r4_d3_int_nonlinear_atom (Zmax v z zhigh : Int)
    (hrec : v = z + Zmax * zhigh) (hz0 : 0 ≤ z)
    (hmul : Zmax ≤ Zmax * zhigh) : Zmax ≤ v := by proof_broker
#print axioms pb_r4_d3_int_nonlinear_atom

/-- R4.2: a nonlinear product of two atomized applications is ONE
    Int atom, and the identical application in hypothesis and goal
    maps to the same atom. INT subtraction inside an atom is fine —
    nothing is truncated. `f`'s domain is not a declarable type, so
    its applications atomize rather than becoming UF symbols. -/
theorem pb_r4_d3_app_product_atom (f : List Nat → Int) (u v : List Nat)
    (a b : Int) (h : f u * f v ≤ a - b) : f u * f v ≤ a - b + 1 := by
  proof_broker
#print axioms pb_r4_d3_app_product_atom

/-- R4.2 fail-closed: ℕ subtraction inside an atomized INT term is
    refused. `f`'s domain is not a type the IR can declare, so the
    application atomizes instead of becoming a UF symbol — and the
    Int-atom scan (`natOpInsideIntAtom?`, the ℕ-scan's type-aware
    sibling) still catches the `n - m`. -/
example (n m : Nat) (f : List Nat → Int)
    (h : f (List.replicate (n - m) 0) ≤ 3) :
    f (List.replicate (n - m) 0) ≤ 4 := by
  fail_if_success proof_broker
  omega

/-- D3 / `threshold_unique`. R4.2: `c'` is not an SMT-LIB simple
    symbol, so before the pre-reification alpha-rename EVERY adapter
    failed with `bad_identifier: c'`. -/
theorem pb_r4_d3_primed_names {f : Int → Int}
    (hf : ∀ a b, a ≤ b → f b ≤ f a) {c c' T : Int}
    (h1 : f c ≤ T) (h2 : T < f (c - 1)) (h1' : f c' ≤ T)
    (h2' : T < f (c' - 1)) (hle : c ≤ c' - 1)
    (hmono : f (c' - 1) ≤ f c) : False := by proof_broker
#print axioms pb_r4_d3_primed_names

/-- R4.2: a hypothesis outside the reifiable fragment is DROPPED,
    the rest of the context is reified, and the goal closes on what
    is left. Here `hbig` is a nested-ℕ-quantifier proposition and
    `hx` alone settles the goal. -/
theorem pb_r4_hyp_dropped (x : Int) (hbig : ∀ n : Nat, x ≤ x + n)
    (hx : x ≤ 3) : x ≤ 4 := by proof_broker
#print axioms pb_r4_hyp_dropped

end ProofBroker.Test
