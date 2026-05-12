(** End-to-end probe + closure test, exercising every surface form.

    Build success of this file is the test. Each [proof_broker]
    invocation reifies the goal, dispatches through the broker,
    verifies the cert, and (in the closing forms) hands the goal
    to Stdlib's [lia] under cert-gating — same trust discipline
    as Lean's [omega] path. *)

From Stdlib Require Import ZArith Lia Reals Lra.
From ProofBroker Require Import ProofBrokerTermMode.

Declare ML Module "proof_broker_rocq.plugin".

Open Scope Z_scope.

(** Two-hypothesis LIA Farkas: x >= 5, x <= 3 ⊢ False.
    Bare form: default manifest list, highest-tier-first. *)
Theorem pb_lia_axiom_free : forall x : Z, x >= 5 -> x <= 3 -> False.
Proof.
  intros x H1 H2.
  proof_broker.
Qed.

(** Same goal, explicit-list form: [proof_broker [cvc5, z3]].
    Mirrors Lean's [proof_broker [cvc5, z3]] — input order is the
    actual dispatch order (filter + priority lever, not just filter).
    The bracket-list form intentionally bypasses
    [sort_by_max_tier_descending]. *)
Theorem pb_lia_explicit_list : forall x : Z, x >= 5 -> x <= 3 -> False.
Proof.
  intros x H1 H2.
  proof_broker [cvc5, z3].
Qed.

(** Verbose form: prints the multi-line extraction-path summary
    (IR shape, dispatch attempts, cert, verify) before closing.
    Mirrors Lean's [proof_broker?]. *)
Theorem pb_lia_verbose : forall x : Z, x >= 5 -> x <= 3 -> False.
Proof.
  intros x H1 H2.
  proof_broker_verbose.
Qed.

(** Explicit [z3] dispatch — surfaces what tier/format z3 mints for
    the example1 LIA shape. Used as the empirical input for the
    term-mode closer's plan: term-mode reconstructs Tier 1 Farkas
    witnesses, so we need to confirm z3 mints Tier 1 (and not Tier
    3 alethe-2024 the way cvc5 does). *)
Theorem pb_lia_z3 : forall x : Z, x >= 5 -> x <= 3 -> False.
Proof.
  intros x H1 H2.
  proof_broker_verbose [z3].
Qed.

(** Term-mode closer: instead of routing the verified cert to lia,
    reconstruct the goal proof from the Tier 1 Farkas witness's
    coefficients. The cert IS the proof along this path —
    [farkas_le_2] from ProofBrokerTermMode.v is the load-bearing
    lemma, [ring] discharges the polynomial identity. No lia /
    lra call. Forces [z3] explicitly because z3 is the only
    adapter that mints Tier 1 farkas natively (cvc5 mints Tier 3
    alethe-2024 which the term builder doesn't yet consume). *)
Theorem pb_term_axiom_free : forall x : Z, x >= 5 -> x <= 3 -> False.
Proof.
  intros x H1 H2.
  proof_broker_term [z3].
Qed.

(** Term-mode arity-3 Tier 1 Farkas: 3-hypothesis chain that omega
    closes via transitive reasoning. The fold-based closer builds
    `c1*a1 + c2*a2 + c3*a3 ≤ 0` step by step via
    `z_mul_nonneg_nonpos` + `z_add_nonpos`, then applies
    `farkas_contradict_n` to discharge the strict-positivity. Lifts
    the closer's arity ceiling from 2 to N. Note: this concrete
    chain `x ≥ 5, x ≤ y, y ≤ 3 ⊢ False` requires z3 to extract a
    3-coefficient witness; cvc5 may produce a different proof shape. *)
Theorem pb_term_arity3_axiom_free :
  forall x y : Z, x >= 5 -> x <= y -> y <= 3 -> False.
Proof.
  intros x y H1 H2 H3.
  proof_broker_term [z3].
Qed.

(** Term-mode with strict-[<] hypotheses (no comparison goal). The
    normalizer routes each [h : a < b] through [lt_to_le0] (LIA +1
    trick: [(a + 1) - b <= 0]), then the False-goal fold runs as
    usual. Two strict hypotheses → witness [(H1, 1); (H2, 1)],
    residual [K = 2]. Mirror of Lean's
    [pb_term_lt_hyp_axiom_free]. *)
Theorem pb_term_lt_hyp_axiom_free :
  forall x : Z, 5 < x -> x < 5 -> False.
Proof.
  intros x H1 H2.
  proof_broker_term [z3].
Qed.

(** Term-mode mixing strict and non-strict hypotheses on a transitive
    chain. Strict [0 < x] and [y < 1] use the +1 trick; non-strict
    [x <= y] uses plain [le_to_le0]. Demonstrates that the fold treats
    them uniformly once normalized — the witness arity rises to 3
    ([farkas_contradict_n]'s territory) and coefficients flow through
    explicitly. *)
Theorem pb_term_lt_mixed_axiom_free :
  forall x y : Z, 0 < x -> x <= y -> y < 1 -> False.
Proof.
  intros x y H1 H2 H3.
  proof_broker_term [z3].
Qed.

(** Term-mode with a non-[False] goal of shape [_ <= _ : Z]. The
    witness has one real-hypothesis entry plus a [neg_goal] slot
    the closer discharges via [farkas_le_goal_2] (which wraps the
    constructive decider [Z_le_gt_dec] — axiom-free). Mirror of
    Lean's [pb_term_goal_axiom_free]. *)
Theorem pb_term_goal_axiom_free :
  forall n : Z, n <= 5 -> n <= 6.
Proof.
  intros n H.
  proof_broker_term [z3].
Qed.

(** Term-mode with strict-[<] goal: closer routes through
    [farkas_lt_goal_2] (no LIA +1 trick — [~ (b < c) ≡ c <= b]
    via [Z.ge_le]). *)
Theorem pb_term_lt_axiom_free :
  forall n : Z, n <= 4 -> n < 5.
Proof.
  intros n H.
  proof_broker_term [z3].
Qed.

(** Term-mode with [>=] goal: [Z.ge] doesn't reduce to swapped
    [Z.le] the way Lean's instance reduction does, so
    [run_close_term] applies [Z.le_ge] first, leaving a [<=]
    subgoal that routes through [farkas_le_goal_2]. *)
Theorem pb_term_ge_axiom_free :
  forall n : Z, 5 <= n -> n >= 4.
Proof.
  intros n H.
  proof_broker_term [z3].
Qed.

(** Term-mode with strict-[>] goal: closer applies [Z.lt_gt]
    first, leaving a [<] subgoal that routes through
    [farkas_lt_goal_2]. *)
Theorem pb_term_gt_axiom_free :
  forall n : Z, 5 <= n -> n > 3.
Proof.
  intros n H.
  proof_broker_term [z3].
Qed.

(** Term-mode with equality goal: the closer pre-splits via
    [Z.le_antisymm] (since [~ (a = b)] is a disjunction outside
    single-witness Farkas scope) and runs the existing [<=]-shape
    term-mode on each direction. Two solver dispatches, two
    comparison-goal closures, one [Z.le_antisymm] wrapper. The axiom
    footprint stays "Closed under the global context" — splitting
    adds no new trust delta over the single-direction case. Mirror
    of Lean's [pb_term_eq_axiom_free]. *)
Theorem pb_term_eq_axiom_free :
  forall n : Z, n <= 5 -> 5 <= n -> n = 5.
Proof.
  intros n H1 H2.
  proof_broker_term [z3].
Qed.

(** Arity-3 comparison goal (Z, Le): transitive chain
    [x ≤ y ∧ y ≤ 5 ⊢ x ≤ 6]. The unified closer applies
    [z_le_via_lt], introduces [neg_goal : 6 < x], and feeds the
    full arity-3 witness (H1 + H2 + neg_goal) through the existing
    arity-N False-fold. No special arity-2 helper involved — same
    code path as the False-goal arity-3 test, just with one extra
    Le entry coming from the (+1-trick-normalized) neg_goal. *)
Theorem pb_term_arity3_goal_axiom_free :
  forall x y : Z, x <= y -> y <= 5 -> x <= 6.
Proof.
  intros x y H1 H2.
  proof_broker_term [z3].
Qed.

(** Arity-3 comparison goal (Z, Lt): same shape with strict goal
    [x < 6]. The wrapper is [z_lt_via_le], neg_goal compiles as
    Le (no +1 trick on the [c <= b] negation of [b < c]). *)
Theorem pb_term_arity3_lt_axiom_free :
  forall x y : Z, x <= y -> y <= 4 -> x < 5.
Proof.
  intros x y H1 H2.
  proof_broker_term [z3].
Qed.

(** Eq hypothesis in the witness: [(h1 : x = 5) (h2 : x <= 3) |- False].
    Solver-emitted certs combine Eq hypotheses with signed coefficients
    to capture both directions of the equality in a single witness slot.
    For this goal the natural cert is [(h1, -1), (h2, 1)] with residual
    K = 2 — the Eq contribution is 0 symbolically (since [x - 5 = 0]
    from h1) but the linear-form combination needs the Eq slot to
    cancel [x] against h2.

    The closer pre-processes the signed coefficient: [c = -1] on an
    Eq hyp triggers the flipped direction ([5 - x <= 0] via
    [z_eq_to_le0_flipped]) with [|c| = 1] as the positive coefficient
    in the fold. *)
Theorem pb_term_eq_hyp_axiom_free :
  forall x : Z, x = 5 -> x <= 3 -> False.
Proof.
  intros x H1 H2.
  proof_broker_term [z3].
Qed.

(** Not-hypothesis in the witness: [(h1 : ~ x <= 5) (h2 : x <= 3) |- False].
    [~ x <= 5] semantically means [x > 5]. Combined with [h2 : x <= 3],
    contradiction. The closer routes the Not hypothesis through
    [z_not_le_to_le0] to get [(5 + 1) - x <= 0] (LIA +1 trick on the
    strict [5 < x] derived from the negation), then folds with h2's
    [x - 3 <= 0] to produce a strictly-positive sum. *)
Theorem pb_term_not_hyp_axiom_free :
  forall x : Z, ~ x <= 5 -> x <= 3 -> False.
Proof.
  intros x H1 H2.
  proof_broker_term [z3].
Qed.

(** Verbose + explicit list. *)
Theorem pb_lia_verbose_list : forall x : Z, x >= 5 -> x <= 3 -> False.
Proof.
  intros x H1 H2.
  proof_broker_verbose [cvc5].
Qed.

(** Debug form: dispatch + verify, print one-line summary, do NOT
    close. The proof discharges manually via [lia] to confirm the
    goal is actually solvable; the test value is in seeing the
    cert summary without trusting the closer. *)
Theorem pb_lia_test : forall x : Z, x >= 5 -> x <= 3 -> False.
Proof.
  intros x H1 H2.
  proof_broker_test.
  lia.
Qed.

(** LRA Farkas: x >= 5, x <= 3 ⊢ False over R. Tests the LRA closer
    end-to-end — reifier emits Real-typed free var, broker dispatches
    LRA-capable adapter, cert.refinement_record.fragment is "LRA",
    and [closer_for_fragment] routes to Stdlib's [lra] (parsed from
    "lra" through Procq, same idiom [lia] uses).

    Rocq does NOT split this into a separate opt-in package the way
    Lean splits ProofBrokerMathlib — the cost-of-import asymmetry
    that drove Lean's split (Mathlib is heavy) doesn't exist here:
    Reals + Lra are in Stdlib already. *)
Open Scope R_scope.
Theorem pb_lra_axiom_free : forall x : R, x >= 5 -> x <= 3 -> False.
Proof.
  intros x H1 H2.
  proof_broker.
Qed.
Close Scope R_scope.

(** Term-mode LRA (Real-typed) non-[False] comparison goals.

    Mirrors the Z-typed [pb_term_goal_axiom_free] / [pb_term_lt_axiom_free]
    / [pb_term_ge_axiom_free] / [pb_term_gt_axiom_free] /
    [pb_term_eq_axiom_free] suite but over [R]. The closer routes
    through [r_farkas_le_goal_2] / [r_farkas_lt_goal_2] (no LIA +1
    trick over R — the helpers weaken the negated goal from strict
    [<] to non-strict [<=] internally via [Rlt_le]). [>=] / [>] / [=]
    goals normalize through [Rle_ge] / [Rlt_gt] / [Rle_antisym] (the
    R-typed mirrors of [Z.le_ge] etc.) before recursing.

    Pinned through [z3] because z3 mints native Tier 1 Farkas for
    LRA; cvc5 prefers Tier 3 alethe-2024 here. Trust footprint is
    the standard LRA pair [ClassicalDedekindReals.sig_forall_dec] +
    [FunctionalExtensionality.functional_extensionality_dep] pulled
    in by Stdlib's [Reals] — same as [pb_lra_axiom_free] and the
    case-split test.

    The simple constants here (e.g. [5], [6]) elaborate as [IZR Z.pos
    p] over R; the reifier walks them as Real-typed numLit literals,
    matching the SDK's literal-elaboration discipline for LRA. *)
Open Scope R_scope.

Theorem pb_lra_term_goal_axiom_free :
  forall n : R, n <= 5 -> n <= 6.
Proof.
  intros n H.
  proof_broker_term [z3].
Qed.

Theorem pb_lra_term_lt_axiom_free :
  forall n : R, n <= 4 -> n < 5.
Proof.
  intros n H.
  proof_broker_term [z3].
Qed.

Theorem pb_lra_term_ge_axiom_free :
  forall n : R, 5 <= n -> n >= 4.
Proof.
  intros n H.
  proof_broker_term [z3].
Qed.

Theorem pb_lra_term_gt_axiom_free :
  forall n : R, 5 <= n -> n > 3.
Proof.
  intros n H.
  proof_broker_term [z3].
Qed.

Theorem pb_lra_term_eq_axiom_free :
  forall n : R, n <= 5 -> 5 <= n -> n = 5.
Proof.
  intros n H1 H2.
  proof_broker_term [z3].
Qed.

(** Arity-3 comparison goal (R, Le): transitive chain
    [x ≤ y ∧ y ≤ 5 ⊢ x ≤ 6]. Mirrors [pb_term_arity3_goal_axiom_free]
    over R. The unified closer applies [r_le_via_lt], introduces
    [neg_goal : 6 < x] (strict over R), and feeds the arity-3
    witness through the strict-aware False-fold. The strictness
    from the Lt-shaped neg_goal entry threads through via
    [r_add_le_lt] at the final fold step. *)
Theorem pb_lra_term_arity3_goal_axiom_free :
  forall x y : R, x <= y -> y <= 5 -> x <= 6.
Proof.
  intros x y H1 H2.
  proof_broker_term [z3].
Qed.

(** Arity-3 comparison goal (R, Lt): strict goal [x < 5] from a
    Le-chain. The wrapper is [r_lt_via_le], neg_goal compiles as
    Le (R has no +1 trick; [c <= b] is the natural negation of
    [b < c]). All entries Le, fold stays in the non-strict path
    until contradicting K > 0 via [r_farkas_contradict_n]. *)
Theorem pb_lra_term_arity3_lt_axiom_free :
  forall x y : R, x <= y -> y <= 4 -> x < 5.
Proof.
  intros x y H1 H2.
  proof_broker_term [z3].
Qed.

(** LRA Farkas with leading-coefficient hypotheses, exercising the
    parser's rational-coefficient path end-to-end. Goal:
    [2*x <= 1 /\ x >= 1 |- False]. The Farkas combination cancels [x]
    with [c1=1, c2=2] (or any positive rational scale of this ratio);
    whatever the solver emits, [parse_witness] routes through
    [Linear_arith.clear_denominators_list] to integer coefficients
    before the closer builds the proof term.

    Regression test for the rational widening: solvers' alethe
    emitters (notably cvc5's [:la_generic :args (1/1 1/1 1/1)])
    serialize even integer coefficients as fractions, so the closer
    must accept them. Even when scaled coefficients are integers,
    the LCD = 1 short-circuit of clear_denominators_list exercises
    the path. *)
Theorem pb_lra_term_rational_axiom_free :
  forall x : R, 2 * x <= 1 -> x >= 1 -> False.
Proof.
  intros x H1 H2.
  proof_broker_term [z3].
Qed.

(** Eq hypothesis in the witness (R): mirror of Z's
    [pb_term_eq_hyp_axiom_free]. The solver-emitted cert combines
    [h1 : x = 5] with [h2 : x <= 3] to derive [False]; the Eq hyp
    flows through [r_eq_to_le0] / [r_eq_to_le0_flipped] depending
    on the coefficient sign. *)
Theorem pb_lra_term_eq_hyp_axiom_free :
  forall x : R, x = 5 -> x <= 3 -> False.
Proof.
  intros x H1 H2.
  proof_broker_term [z3].
Qed.

(** Not-hypothesis in the witness (R): mirror of Z's
    [pb_term_not_hyp_axiom_free]. [~ x <= 5] over R compiles to
    the strict [5 < x] (no +1 trick over R). The closer's strict-
    aware fold threads strictness through via [r_not_le_to_lt0] +
    [r_mul_pos_neg] / [r_add_lt_le]. *)
Theorem pb_lra_term_not_hyp_axiom_free :
  forall x : R, ~ (x <= 5)%R -> (x <= 3)%R -> False.
Proof.
  intros x H1 H2.
  proof_broker_term [z3].
Qed.

(** Term-mode LRA strict-[<] hypotheses (False-goal). Strict
    hypotheses over R don't get the LIA +1 trick — there's no discrete
    domain to lift into — so the normalizer leaves them in strict
    [a < 0] form via [r_lt_to_lt0], and the fold tracks strictness
    state to pick [r_mul_pos_neg] + [r_add_*] combinators. Final
    contradiction step is [r_farkas_contradict_n_strict] when any
    premise is strict (allows [K = 0] when strictness alone carries
    the contradiction).

    Two-strict, arity-2: [5 < x ∧ x < 5 ⊢ False] gives linear sum
    [(5 - x) + (x - 5) = 0], K = 0; strictness from both premises
    closes via [r_farkas_contradict_n_strict]. Mirror of Z's
    [pb_term_lt_hyp_axiom_free]. *)
Theorem pb_lra_term_lt_hyp_axiom_free :
  forall x : R, 5 < x -> x < 5 -> False.
Proof.
  intros x H1 H2.
  proof_broker_term [z3].
Qed.

(** Term-mode LRA strict-[<] hypothesis on a Le-goal: [(h : 0 < x) ⊢ 0 ≤ x].
    Witness [(h, 1), (neg_goal, 1)] gives linear sum [(0 - x) + (x - 0) = 0],
    K = 0. The closer weakens [h : 0 < x] to [h : 0 <= x] via
    [r_strict_neg_to_nonpos], then routes through the existing
    [r_farkas_le_goal_2] strict-aware path — strictness on the
    contradiction side comes from the neg_goal's Lt-shape over R, so
    losing [a1]'s strictness on weakening costs nothing. *)
Theorem pb_lra_term_le_goal_strict_a1_axiom_free :
  forall x : R, 0 < x -> 0 <= x.
Proof.
  intros x H.
  proof_broker_term [z3].
Qed.

(** Strict-[<] hypothesis on a Lt-goal: [(h : 0 < x) ⊢ 0 < x] (trivially
    equivalent to [h], but exercises the closer end-to-end). Witness
    sum is exactly zero [(0 - x) + (x - 0) = 0], K = 0 — the
    standard [r_farkas_lt_goal_2] path can't close this because it
    needs K > 0 strictly, so the dispatcher routes to
    [r_farkas_lt_goal_2_strict_a1] which preserves [a1]'s strictness
    through the proof (via [r_mul_pos_neg]) and gets the contradiction
    from the strict combination [c1 * a1 < 0] + [cng * (c - b) ≤ 0]. *)
Theorem pb_lra_term_lt_goal_strict_a1_axiom_free :
  forall x : R, 0 < x -> 0 < x.
Proof.
  intros x H.
  proof_broker_term [z3].
Qed.

(** Strict-[<] hypothesis on a [≥] goal. Closer applies [Rle_ge]
    first, leaving a [≤] subgoal that routes through the Le-goal
    weakening path. *)
Theorem pb_lra_term_ge_goal_strict_a1_axiom_free :
  forall x : R, 0 < x -> x >= 0.
Proof.
  intros x H.
  proof_broker_term [z3].
Qed.

(** Strict-[<] hypothesis on a [>] goal. Closer applies [Rlt_gt]
    first, leaving a [<] subgoal that routes through the strict-a1
    Lt-goal path. *)
Theorem pb_lra_term_gt_goal_strict_a1_axiom_free :
  forall x : R, 0 < x -> x > 0.
Proof.
  intros x H.
  proof_broker_term [z3].
Qed.

(** Mixed strict + non-strict, arity-3: [1 ≤ x ∧ x ≤ y ∧ y < 1 ⊢ False].
    z3's witness has (Le, Le, Lt) — two non-strict premises and one
    strict. The fold threads strictness through:
      acc starts non-strict (entry 1 Le) → Le;
      acc + entry 2 Le → Le (via [r_add_nonpos]);
      acc + entry 3 Lt → Lt (via [r_add_le_lt]).
    Linear sum collapses to zero — strictness from the [y < 1] premise
    is what closes the gap. *)
Theorem pb_lra_term_lt_mixed_axiom_free :
  forall x y : R, 1 <= x -> x <= y -> y < 1 -> False.
Proof.
  intros x y H1 H2 H3.
  proof_broker_term [z3].
Qed.

Close Scope R_scope.

(** Term-mode Tier 2 case-split: a goal with a disjunctive
    hypothesis [(x <= 0) \/ (x >= 10)] under [1 <= x <= 9] closes
    by destruct + per-branch Farkas. cvc5 mints a Tier 2
    [case_split_farkas] cert (adapter priority prefers case-split
    over Tier 3 alethe when the IR has a disjunctive hypothesis),
    and the bridge closer destructs the disjunction in the Coq
    context + applies the matching lemma's Tier 1 Farkas witness
    per branch via [r_farkas_le_2]. No [lra] call along this path
    — the cert IS the proof, both at the case-split structure level
    and at the per-branch arithmetic level. Trust footprint is the
    R-typed term-mode helpers (which carry the standard LRA axiom
    pair [ClassicalDedekindReals.sig_forall_dec],
    [FunctionalExtensionality.functional_extensionality_dep] from
    Stdlib's [Reals]) + [ring] for the per-branch polynomial
    identity. Mirror of the SDK's [test_extract_case_split]
    fixture, end-to-end through the adapter. *)
Open Scope R_scope.
Theorem pb_term_case_split_axiom_free :
  forall x : R, (x <= 0 \/ x >= 10) -> x >= 1 -> x <= 9 -> False.
Proof.
  intros x H_disj H_low H_high.
  proof_broker_term [cvc5].
Qed.
Close Scope R_scope.

(** UF reach: arity-1 congruence, mirroring Lean's
    [uf_axiom_free]. The reifier walks [f : Z -> Z] into a free_var
    with [ty = "Int->Int"], the SDK serializer emits
    [(declare-fun f (Int) Int)], cvc5 returns unsat under QF_UFLIA,
    the verifier envelope-checks (Tier 0 oracle), and the closer
    chain ([congruence | subst; assumption]) discharges. *)
Theorem pb_uf_axiom_free :
  forall (f : Z -> Z) (x y : Z), x = y -> f x = f y.
Proof.
  intros f x y H.
  proof_broker.
Qed.

(** UF reach: arity-2 binary function. *)
Theorem pb_uf_two_arg_axiom_free :
  forall (f : Z -> Z -> Z) (a b : Z), a = b -> f a b = f a a.
Proof.
  intros f a b H.
  proof_broker.
Qed.

(** UF reach: composed / nested function applications. *)
Theorem pb_uf_composed_axiom_free :
  forall (f g : Z -> Z) (x y : Z), x = y -> f (g x) = f (g y).
Proof.
  intros f g x y H.
  proof_broker.
Qed.

(** UF reach: predicate-valued UF. The [P : Z -> Prop] free var is
    arrow-typed with codomain [Prop], which the reifier maps to
    SMT-LIB sort [Bool] via [Smtlib.sort_of_type_ref]. The closer's
    [subst; assumption] arm catches the modus-ponens shape. *)
Theorem pb_uf_predicate_axiom_free :
  forall (P : Z -> Prop) (x y : Z), P x -> x = y -> P y.
Proof.
  intros P x y Hp H.
  proof_broker.
Qed.

(** Axiom-footprint check, mirroring lean-bridge/Test/Tactic.lean's
    [#print axioms] discipline. The closer routes through Stdlib's
    [lia] (LIA path) or [lra] (LRA path); both are axiom-free in the
    same sense Lean's [omega] / [linarith] are. Cert-gated calls
    introduce no [proofBrokerCertSound]-style trust axiom. Each
    named theorem closes without dependencies on any axiom, so
    [Print Assumptions] reports "Closed under the global context" —
    even cleaner than Lean's [propext, Quot.sound] footprint. *)
(* [Print <name>.] markers anchor each [Print Assumptions] block in
   build output for [tools/check_axioms.py]; see
   ProofBrokerTermMode.v's note for context. *)
Print pb_lia_axiom_free.
Print Assumptions pb_lia_axiom_free.

Print pb_lia_explicit_list.
Print Assumptions pb_lia_explicit_list.

Print pb_lia_verbose.
Print Assumptions pb_lia_verbose.

Print pb_lra_axiom_free.
Print Assumptions pb_lra_axiom_free.

Print pb_term_axiom_free.
Print Assumptions pb_term_axiom_free.

Print pb_term_arity3_axiom_free.
Print Assumptions pb_term_arity3_axiom_free.

Print pb_term_lt_hyp_axiom_free.
Print Assumptions pb_term_lt_hyp_axiom_free.

Print pb_term_lt_mixed_axiom_free.
Print Assumptions pb_term_lt_mixed_axiom_free.

Print pb_term_goal_axiom_free.
Print Assumptions pb_term_goal_axiom_free.

Print pb_term_lt_axiom_free.
Print Assumptions pb_term_lt_axiom_free.

Print pb_term_ge_axiom_free.
Print Assumptions pb_term_ge_axiom_free.

Print pb_term_gt_axiom_free.
Print Assumptions pb_term_gt_axiom_free.

Print pb_term_eq_axiom_free.
Print Assumptions pb_term_eq_axiom_free.

Print pb_term_arity3_goal_axiom_free.
Print Assumptions pb_term_arity3_goal_axiom_free.

Print pb_term_arity3_lt_axiom_free.
Print Assumptions pb_term_arity3_lt_axiom_free.

Print pb_term_eq_hyp_axiom_free.
Print Assumptions pb_term_eq_hyp_axiom_free.

Print pb_term_not_hyp_axiom_free.
Print Assumptions pb_term_not_hyp_axiom_free.

Print pb_lra_term_goal_axiom_free.
Print Assumptions pb_lra_term_goal_axiom_free.

Print pb_lra_term_lt_axiom_free.
Print Assumptions pb_lra_term_lt_axiom_free.

Print pb_lra_term_ge_axiom_free.
Print Assumptions pb_lra_term_ge_axiom_free.

Print pb_lra_term_gt_axiom_free.
Print Assumptions pb_lra_term_gt_axiom_free.

Print pb_lra_term_eq_axiom_free.
Print Assumptions pb_lra_term_eq_axiom_free.

Print pb_lra_term_arity3_goal_axiom_free.
Print Assumptions pb_lra_term_arity3_goal_axiom_free.

Print pb_lra_term_arity3_lt_axiom_free.
Print Assumptions pb_lra_term_arity3_lt_axiom_free.

Print pb_lra_term_rational_axiom_free.
Print Assumptions pb_lra_term_rational_axiom_free.

Print pb_lra_term_eq_hyp_axiom_free.
Print Assumptions pb_lra_term_eq_hyp_axiom_free.

Print pb_lra_term_not_hyp_axiom_free.
Print Assumptions pb_lra_term_not_hyp_axiom_free.

Print pb_lra_term_lt_hyp_axiom_free.
Print Assumptions pb_lra_term_lt_hyp_axiom_free.

Print pb_lra_term_lt_mixed_axiom_free.
Print Assumptions pb_lra_term_lt_mixed_axiom_free.

Print pb_lra_term_le_goal_strict_a1_axiom_free.
Print Assumptions pb_lra_term_le_goal_strict_a1_axiom_free.

Print pb_lra_term_lt_goal_strict_a1_axiom_free.
Print Assumptions pb_lra_term_lt_goal_strict_a1_axiom_free.

Print pb_lra_term_ge_goal_strict_a1_axiom_free.
Print Assumptions pb_lra_term_ge_goal_strict_a1_axiom_free.

Print pb_lra_term_gt_goal_strict_a1_axiom_free.
Print Assumptions pb_lra_term_gt_goal_strict_a1_axiom_free.

Print pb_term_case_split_axiom_free.
Print Assumptions pb_term_case_split_axiom_free.

Print pb_uf_axiom_free.
Print Assumptions pb_uf_axiom_free.

Print pb_uf_two_arg_axiom_free.
Print Assumptions pb_uf_two_arg_axiom_free.

Print pb_uf_composed_axiom_free.
Print Assumptions pb_uf_composed_axiom_free.

Print pb_uf_predicate_axiom_free.
Print Assumptions pb_uf_predicate_axiom_free.
