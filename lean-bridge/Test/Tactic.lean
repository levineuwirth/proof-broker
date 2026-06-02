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
   baseline, no new trust delta. `equiv_simplify` is deferred:
   its propositional-equality tautologies need propext + Iff
   reflexivity rather than omega-discharge. -/

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

/- Alethe walker — snapshot test against a real cvc5 trace.

   The trace below is the verbatim alethe-2024 output cvc5
   minted for `(n m : Int) (h1 : n + m = 10) (h3 : 0 ≤ m)
   ⊢ n ≤ 10` (the `lia_axiom_free` shape) — captured by adding
   diagnostic logging to `tryAletheWalkerLIA` in this branch,
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

end ProofBroker.Test
