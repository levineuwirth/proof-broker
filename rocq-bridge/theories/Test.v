(** End-to-end probe + closure test, exercising every surface form.

    Build success of this file is the test. Each [proof_broker]
    invocation reifies the goal, dispatches through the broker,
    verifies the cert, and (in the closing forms) hands the goal
    to Stdlib's [lia] under cert-gating — same trust discipline
    as Lean's [omega] path. *)

From Stdlib Require Import ZArith Lia Reals Lra.
(* [classic] for the R-7 boolean-cleanup walker tests (implies /
   equiv1 / equiv2 / not_and / and_neg build their proofs by
   excluded-middle case analysis); [propositional_extensionality]
   for the R-8 equiv_simplify tests (propositional-equality
   tautologies built via propext). *)
From Stdlib Require Import Classical_Prop PropExtensionality.
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
    witness has one real-hypothesis entry plus a [neg_goal] slot the
    closer discharges via the [z_le_via_lt] wrapper (constructive
    decider [Z_le_gt_dec], axiom-free), then folds into the arity-N
    False-path. Mirror of Lean's [pb_term_goal_axiom_free]. *)
Theorem pb_term_goal_axiom_free :
  forall n : Z, n <= 5 -> n <= 6.
Proof.
  intros n H.
  proof_broker_term [z3].
Qed.

(** Term-mode with strict-[<] goal: closer routes through the
    [z_lt_via_le] wrapper into the arity-N fold (no LIA +1 trick —
    [~ (b < c) ≡ c <= b] via [Z.ge_le]). *)
Theorem pb_term_lt_axiom_free :
  forall n : Z, n <= 4 -> n < 5.
Proof.
  intros n H.
  proof_broker_term [z3].
Qed.

(** Term-mode with [>=] goal: [Z.ge] doesn't reduce to swapped
    [Z.le] the way Lean's instance reduction does, so
    [run_close_term] applies [Z.le_ge] first, leaving a [<=]
    subgoal that routes through the [z_le_via_lt] wrapper. *)
Theorem pb_term_ge_axiom_free :
  forall n : Z, 5 <= n -> n >= 4.
Proof.
  intros n H.
  proof_broker_term [z3].
Qed.

(** Term-mode with strict-[>] goal: closer applies [Z.lt_gt]
    first, leaving a [<] subgoal that routes through the
    [z_lt_via_le] wrapper. *)
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
    through the [r_le_via_lt] / [r_lt_via_le] wrappers into the
    arity-N strict-aware fold (no LIA +1 trick over R — strictness on
    neg_goal flows in naturally via [Rnot_le_lt] / [Rnot_lt_le]).
    [>=] / [>] / [=] goals normalize through [Rle_ge] / [Rlt_gt] /
    [Rle_antisym] (the R-typed mirrors of [Z.le_ge] etc.) before
    recursing.

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
    K = 0. The unified strict-aware fold consumes the Lt-normalized
    [h] directly ([r_lt_to_lt0 → a - b < 0]) and combines it with the
    neg_goal's Lt-shape over R; no weakening required. *)
Theorem pb_lra_term_le_goal_strict_a1_axiom_free :
  forall x : R, 0 < x -> 0 <= x.
Proof.
  intros x H.
  proof_broker_term [z3].
Qed.

(** Strict-[<] hypothesis on a Lt-goal: [(h : 0 < x) ⊢ 0 < x] (trivially
    equivalent to [h], but exercises the closer end-to-end). Witness
    sum is exactly zero [(0 - x) + (x - 0) = 0], K = 0 — the
    strict-aware fold preserves [a1]'s strictness through the proof
    (via [r_mul_pos_neg]) and gets the contradiction from the strict
    combination [c1 * a1 < 0] + [cng * (c - b) ≤ 0], closed by
    [r_farkas_contradict_n_strict] (which permits K = 0 when strictness
    on the sum carries the contradiction). *)
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

(* ============================================================
   LLM-as-backend home-side replay closer
   (roadmap §Phase 3 deliverable 3, Rocq parity M2).

   [llm_replay_test "<script>"] simulates a successful LLM
   adapter response (an LLM produced this Ltac string) and runs
   the *same* [Llm_replay.replay_script] closer the live broker
   path takes for a Tier-3 [Tier3_replay_deferred] cert. This
   exercises the audit-H1 contract — kernel replay + axiom-
   footprint subset check — with no network and no model.
   Mirror of the llm_replay_test block in
   lean-bridge/Test/Tactic.lean. *)

(* Positive: a clean Ltac script the home kernel independently
   accepts ([intros; reflexivity], axiom-free) closes the goal
   via the LLM-replay path. The proof term comes from Rocq, not
   the LLM — audit H1. *)
Theorem pb_llm_replay_axiom_free : forall x : Z, x = x.
Proof.
  llm_replay_test "intros x; reflexivity".
Qed.

Print pb_llm_replay_axiom_free.
Print Assumptions pb_llm_replay_axiom_free.

(* Negative: a script that runs without error but does not close
   the goal ([idtac]) is a tactic failure — never a silent
   pass. [assert_fails] confirms the inner tactic errored;
   [exact I] then closes legitimately. *)
Example pb_llm_replay_rejects_non_closing : True.
Proof.
  assert_fails (llm_replay_test "idtac").
  exact I.
Qed.

(* Negative: a script that does not parse as Rocq Ltac is a
   tactic failure, not an admitted theorem. *)
Example pb_llm_replay_rejects_unparsable : True.
Proof.
  assert_fails (llm_replay_test "@@@ not lean @@@").
  exact I.
Qed.

(* ============================================================
   LLM-assisted Tier-3 reconstruction fallback
   (roadmap §Phase 3 deliverable 4, Rocq parity M3).

   [llm_reconstruct_test "<traceFmt>" "<script>"] simulates a
   successful [Llm_reconstruct.translate] call (the LLM was
   asked to translate an un-replayable Tier-3 trace and
   returned the script) and routes the candidate through the
   SAME audit-H1 gate the production fallback uses. The
   translation step itself is a pure I/O wrapper around an
   untrusted oracle — no soundness contribution — so swapping
   the live SDK call for a literal script is faithful to what's
   being tested: that a candidate script makes it through
   [replay_reconstructed_script] → [Llm_replay.replay_script],
   with the audit-H1 gate firing identically. Mirror of the
   llm_reconstruct_test block in lean-bridge/Test/Tactic.lean. *)

(* Positive: a translated script the kernel independently
   accepts (axiom-free [intros; reflexivity]) closes the goal
   via the reconstruction fallback's replay closer. The build
   log carries the "closed via LLM Tier-3 reconstruction …"
   audit line. *)
Theorem pb_llm_reconstruct_axiom_free : forall x : Z, x = x.
Proof.
  llm_reconstruct_test "alethe-2024" "intros x; reflexivity".
Qed.

Print pb_llm_reconstruct_axiom_free.
Print Assumptions pb_llm_reconstruct_axiom_free.

(* Negative: a translation that runs without error but does not
   close the goal is a tactic failure, never a silent pass. *)
Example pb_llm_reconstruct_rejects_non_closing : True.
Proof.
  assert_fails (llm_reconstruct_test "alethe-2024" "idtac").
  exact I.
Qed.

(* Negative: a translation that does not parse as Rocq Ltac is
   a tactic failure, not an admitted theorem. *)
Example pb_llm_reconstruct_rejects_unparsable : True.
Proof.
  assert_fails (llm_reconstruct_test "tstp-fof" "@@@ not lean @@@").
  exact I.
Qed.

(** Alethe walker — R-2 clausal layer.

    Mirror of lean-bridge/Test/Tactic.lean's
    [alethe_walker_clausal_axiom_free]. The trace seeds the two
    [assume] steps against the local hypotheses [hA] and [hNA],
    then the [resolution] step cancels the complementary
    [(A, not A)] pair to derive the empty clause = False.
    Walker proof: [hNA hA : False].

    Audit-footprint-clean: no axioms (the walker built a pure
    kernel term, no decision procedure involved at all). *)
Theorem alethe_walker_clausal_axiom_free :
  forall (A : Prop), A -> ~ A -> False.
Proof.
  intros A hA hNA.
  alethe_walker_test
    "( (assume a0 A) (assume a1 (not A)) (step t0 (cl) :rule resolution :premises (a0 a1)) )".
Qed.

Print alethe_walker_clausal_axiom_free.
Print Assumptions alethe_walker_clausal_axiom_free.

(** Alethe walker — R-3 arithmetic layer ([la_generic] /
    [la_mult_neg]).

    Mirror of lean-bridge/Test/Tactic.lean's
    [alethe_walker_la_generic_lit] / [_disj]. cvc5 emits
    [la_generic] for LIA-tautology leaves; the walker creates a
    fresh evar of the clause's type, and the outer tactic runs
    [lia] on it via [tclINDEPENDENT]. Axiom-footprint match
    Coq's [lia] (Coq Stdlib's LIA decision procedure, axiom-free
    over Z). *)

(** Single-literal LIA tautology: [0 <= 5] proved by [lia] via
    the walker's evar-discharge. *)
Theorem alethe_walker_la_generic_lit : (0 <= 5)%Z.
Proof.
  alethe_walker_test
    "( (step t0 (cl (<= 0 5)) :rule la_generic :args ()) )".
Qed.

Print alethe_walker_la_generic_lit.
Print Assumptions alethe_walker_la_generic_lit.

(** Multi-literal disjunction tautology: [~ (x >= 3) \/ (x >= 1)].
    The walker translates the [(cl ...)] clause to a
    right-associated Or; the resulting evar's type is the
    disjunction, which [lia] handles by case analysis on its
    negation. *)
Theorem alethe_walker_la_generic_disj :
  forall x : Z, ~ (x >= 3) \/ (x >= 1).
Proof.
  intro x.
  alethe_walker_test
    "( (step t0 (cl (not (>= x 3)) (>= x 1)) :rule la_generic :args (1/1 1/1)) )".
Qed.

Print alethe_walker_la_generic_disj.
Print Assumptions alethe_walker_la_generic_disj.

(** Alethe walker — R-4 multi-literal resolution.

    Mirror of lean-bridge/Test/Tactic.lean's
    [alethe_walker_resolution_axiom_free]. A 3-clause
    propositional refutation:
    - hAB : A \/ B
    - hAC : ~A \/ C
    - hnB : ~B
    - hnC : ~C
    The walker performs four resolution steps:
    - t2: resolve (cl A B) and (cl (not A) C) on pivot A/~A
      → resolvent (cl B C). Exercises the full Or.elim cascade
      via [cases_clause] + [inject_lit], the n-ary case the
      R-2 simple resolution couldn't handle.
    - t3: resolve (cl B C) and (not B) → (cl C).
    - t4: resolve (cl C) and (not C) → (cl) = False.
    Axiom-footprint clean: pure kernel-term reconstruction. *)
Theorem alethe_walker_resolution_axiom_free :
  forall (A B C : Prop),
    A \/ B -> ~ A \/ C -> ~ B -> ~ C -> False.
Proof.
  intros A B C hAB hAC hnB hnC.
  alethe_walker_test "(
    (assume a0 (or A B))
    (assume a1 (or (not A) C))
    (assume a2 (not B))
    (assume a3 (not C))
    (step t0 (cl A B) :rule or :premises (a0))
    (step t1 (cl (not A) C) :rule or :premises (a1))
    (step t2 (cl B C) :rule resolution :premises (t0 t1))
    (step t3 (cl C) :rule resolution :premises (t2 a2))
    (step t4 (cl) :rule resolution :premises (t3 a3)) )".
Qed.

Print alethe_walker_resolution_axiom_free.
Print Assumptions alethe_walker_resolution_axiom_free.

(** Alethe walker — R-5 equality cluster (refl / symm / trans / cong).

    Mirror of lean-bridge/Test/Tactic.lean's equality-cluster tests
    (Lean #45). Three checks, all over uninterpreted sorts/functions
    so they exercise the generic-UF application fallback in
    [sexp_to_constr] and the polymorphic-[eq] retyping (no longer
    hardcoded to Z). All axiom-footprint clean: pure [eq_refl] /
    [eq_sym] / [eq_trans] / [f_equal] reconstruction, no Classical. *)

(* Unary congruence: f x = f y from x = y. Exercises [elab_cong]'s
   single-argument [f_equal] link (n = 1, no eq_trans chaining). *)
Theorem alethe_walker_cong_unary_axiom_free :
  forall (U : Type) (f : U -> U) (x y : U), x = y -> f x = f y.
Proof.
  intros U f x y hxy.
  alethe_walker_test "(
    (assume a0 (= x y))
    (step t0 (cl (= (f x) (f y))) :rule cong :premises (a0)) )".
Qed.

Print alethe_walker_cong_unary_axiom_free.
Print Assumptions alethe_walker_cong_unary_axiom_free.

(* Binary congruence: g a c = g b d from a = b and c = d. Exercises
   the per-argument rewrite chain with [eq_trans] linking the two
   single-argument [f_equal] steps (n = 2). *)
Theorem alethe_walker_cong_binary_axiom_free :
  forall (U : Type) (g : U -> U -> U) (a b c d : U),
    a = b -> c = d -> g a c = g b d.
Proof.
  intros U g a b c d hab hcd.
  alethe_walker_test "(
    (assume a0 (= a b))
    (assume a1 (= c d))
    (step t0 (cl (= (g a c) (g b d))) :rule cong :premises (a0 a1)) )".
Qed.

Print alethe_walker_cong_binary_axiom_free.
Print Assumptions alethe_walker_cong_binary_axiom_free.

(* End-to-end UF refutation: x = y and f x <> f y are contradictory.
   [cong] derives f x = f y, then resolution against the negated
   literal closes the empty clause. Chains the equality cluster into
   the R-4 resolution machinery. *)
Theorem alethe_walker_uf_refutation_axiom_free :
  forall (U : Type) (f : U -> U) (x y : U),
    x = y -> f x <> f y -> False.
Proof.
  intros U f x y hxy hne.
  alethe_walker_test "(
    (assume a0 (= x y))
    (assume a1 (not (= (f x) (f y))))
    (step t0 (cl (= (f x) (f y))) :rule cong :premises (a0))
    (step t1 (cl) :rule resolution :premises (t0 a1)) )".
Qed.

Print alethe_walker_uf_refutation_axiom_free.
Print Assumptions alethe_walker_uf_refutation_axiom_free.

(** Alethe walker — R-6 trust-tagged leaves (hole / rare_rewrite).

    Mirror of lean-bridge/Test/Tactic.lean's trust-tagged-leaf tests
    (Lean #46). cvc5 emits [hole] (TRUST_THEORY_REWRITE-annotated)
    and [rare_rewrite] (RARE rewrite system) as "admit the
    conclusion" steps. Audit H1 forbids trusting the tag: the walker
    re-derives the clause via the same [lia]-discharge as [la_generic],
    so the proof goes through the kernel independently of cvc5's
    annotation. Axiom-footprint matches Coq's [lia] (axiom-free over
    Z). The negative test pins the contract: a tag is never license. *)

(* [hole]: a LIA-tautology leaf, lia-discharged via the walker's evar. *)
Theorem alethe_walker_hole_axiom_free : (0 <= 5)%Z.
Proof.
  alethe_walker_test "( (step t0 (cl (<= 0 5)) :rule hole) )".
Qed.

Print alethe_walker_hole_axiom_free.
Print Assumptions alethe_walker_hole_axiom_free.

(* [rare_rewrite]: same lia-discharge policy, multi-literal clause. *)
Theorem alethe_walker_rare_rewrite_axiom_free :
  forall x : Z, ~ (x >= 3) \/ (x >= 1).
Proof.
  intro x.
  alethe_walker_test
    "( (step t0 (cl (not (>= x 3)) (>= x 1)) :rule rare_rewrite) )".
Qed.

Print alethe_walker_rare_rewrite_axiom_free.
Print Assumptions alethe_walker_rare_rewrite_axiom_free.

(* End-to-end: a [hole] clause feeding into resolution. The walker
   discharges the trust-tagged leaf via lia (the clause is the
   LIA-tautological implication n >= 6 -> n >= 5 in clausal form),
   then the clausal layer composes it against the hypotheses to
   close False. Confirms [hole] slots into the R-4 resolution
   machinery exactly as [la_generic] does. *)
Theorem alethe_walker_hole_refutation_axiom_free :
  forall (n : Z), n >= 6 -> ~ (n >= 5) -> False.
Proof.
  intros n h1 h2.
  alethe_walker_test
    "( (assume a0 (>= n 6))
       (assume a1 (not (>= n 5)))
       (step t0 (cl (not (>= n 6)) (>= n 5)) :rule hole)
       (step t1 (cl (not (>= n 6))) :rule resolution :premises (t0 a1))
       (step t2 (cl) :rule resolution :premises (t1 a0)) )".
Qed.

Print alethe_walker_hole_refutation_axiom_free.
Print Assumptions alethe_walker_hole_refutation_axiom_free.

(* audit H1 (negative): a [hole] whose clause is NOT a lia-tautology
   must FAIL rather than be admitted on the trust tag. The clause
   [(>= n 100)] matches the goal type (so it clears the is_conv
   check) but is false for general n; the walker's evar survives to
   the [lia] discharge, which fails, so the whole tactic fails and
   the goal is left OPEN. This is the contract that makes [hole]
   H1-safe: cvc5's annotation is advisory, never license. The
   [Fail] vernacular asserts the tactic errors; [Abort] discards the
   (correctly) unproved goal, so it contributes no axioms. *)
Theorem alethe_walker_hole_unsound_must_fail : forall n : Z, n >= 100.
Proof.
  intro n.
  Fail alethe_walker_test "( (step t0 (cl (>= n 100)) :rule hole) )".
Abort.

(** Alethe walker — R-7 boolean cleanup (implies / equiv1 / equiv2 /
    not_and / and_neg).

    Mirror of lean-bridge/Test/Tactic.lean's boolean-cleanup tests
    (Lean #47). cvc5 emits these during SAT-side normalization to
    flatten implications, propositional equivalences, and
    conjunctions into clausal form. The walker builds the proofs by
    [classic] (excluded-middle) case analysis, so these are the
    FIRST walker proofs to leave the intuitionistic fragment: the
    axiom footprint grows from empty to [{classic}] — the standard
    classical baseline, no new trust delta. *)

(* [implies]: a -> b yields ~a \/ b. *)
Theorem alethe_walker_implies_axiom_free :
  forall (a b : Prop), (a -> b) -> (~ a \/ b).
Proof.
  intros a b hab.
  alethe_walker_test "(
    (assume a0 (=> a b))
    (step t0 (cl (not a) b) :rule implies :premises (a0)) )".
Qed.

Print alethe_walker_implies_axiom_free.
Print Assumptions alethe_walker_implies_axiom_free.

(* [equiv1]: a = b yields ~a \/ b (forward direction, eq_mp transport). *)
Theorem alethe_walker_equiv1_axiom_free :
  forall (a b : Prop), a = b -> (~ a \/ b).
Proof.
  intros a b hab.
  alethe_walker_test "(
    (assume a0 (= a b))
    (step t0 (cl (not a) b) :rule equiv1 :premises (a0)) )".
Qed.

Print alethe_walker_equiv1_axiom_free.
Print Assumptions alethe_walker_equiv1_axiom_free.

(* [equiv2]: a = b yields a \/ ~b (backward direction, eq_mpr transport). *)
Theorem alethe_walker_equiv2_axiom_free :
  forall (a b : Prop), a = b -> (a \/ ~ b).
Proof.
  intros a b hab.
  alethe_walker_test "(
    (assume a0 (= a b))
    (step t0 (cl a (not b)) :rule equiv2 :premises (a0)) )".
Qed.

Print alethe_walker_equiv2_axiom_free.
Print Assumptions alethe_walker_equiv2_axiom_free.

(* [not_and] binary: ~(a /\ b) yields ~a \/ ~b (De Morgan). *)
Theorem alethe_walker_not_and_binary_axiom_free :
  forall (a b : Prop), ~ (a /\ b) -> (~ a \/ ~ b).
Proof.
  intros a b h.
  alethe_walker_test "(
    (assume a0 (not (and a b)))
    (step t0 (cl (not a) (not b)) :rule not_and :premises (a0)) )".
Qed.

Print alethe_walker_not_and_binary_axiom_free.
Print Assumptions alethe_walker_not_and_binary_axiom_free.

(* [not_and] ternary: exercises the [build_not_and] recursion. *)
Theorem alethe_walker_not_and_ternary_axiom_free :
  forall (a b c : Prop), ~ (a /\ b /\ c) -> (~ a \/ ~ b \/ ~ c).
Proof.
  intros a b c h.
  alethe_walker_test "(
    (assume a0 (not (and a b c)))
    (step t0 (cl (not a) (not b) (not c)) :rule not_and :premises (a0)) )".
Qed.

Print alethe_walker_not_and_ternary_axiom_free.
Print Assumptions alethe_walker_not_and_ternary_axiom_free.

(* [and_neg] binary: the tautology (a /\ b) \/ ~a \/ ~b, no premises. *)
Theorem alethe_walker_and_neg_binary_axiom_free :
  forall (a b : Prop), (a /\ b) \/ ~ a \/ ~ b.
Proof.
  intros a b.
  alethe_walker_test "(
    (step t0 (cl (and a b) (not a) (not b)) :rule and_neg) )".
Qed.

Print alethe_walker_and_neg_binary_axiom_free.
Print Assumptions alethe_walker_and_neg_binary_axiom_free.

(* [and_neg] ternary: exercises the [build_and_neg] recursion. *)
Theorem alethe_walker_and_neg_ternary_axiom_free :
  forall (a b c : Prop), (a /\ b /\ c) \/ ~ a \/ ~ b \/ ~ c.
Proof.
  intros a b c.
  alethe_walker_test "(
    (step t0 (cl (and a b c) (not a) (not b) (not c)) :rule and_neg) )".
Qed.

Print alethe_walker_and_neg_ternary_axiom_free.
Print Assumptions alethe_walker_and_neg_ternary_axiom_free.

(* End-to-end: [implies] composed with resolution. From a -> b, a,
   and ~b derive False — the implies-flattened clause feeds the R-4
   resolution machinery. *)
Theorem alethe_walker_implies_refutation_axiom_free :
  forall (a b : Prop), (a -> b) -> a -> ~ b -> False.
Proof.
  intros a b hab ha hnb.
  alethe_walker_test "(
    (assume a0 (=> a b))
    (assume a1 a)
    (assume a2 (not b))
    (step t0 (cl (not a) b) :rule implies :premises (a0))
    (step t1 (cl b) :rule resolution :premises (t0 a1))
    (step t2 (cl) :rule resolution :premises (t1 a2)) )".
Qed.

Print alethe_walker_implies_refutation_axiom_free.
Print Assumptions alethe_walker_implies_refutation_axiom_free.

(** Alethe walker — R-8 equiv_simplify (propositional-equality
    tautology simplification).

    Mirror of lean-bridge/Test/Tactic.lean's equiv_simplify tests
    (Lean #48). cvc5 emits these as leaves [(cl (= lhs rhs))] where
    [lhs <-> rhs] is a propositional tautology. The walker is a
    structural pattern matcher building per-pattern
    [propositional_extensionality (conj fwd bwd)] terms. Footprint
    adds [propositional_extensionality] (propext); the double-
    negation pattern additionally pulls [classic] (via NNPP). *)

(* Pattern (= (= t t) true): reflexivity tautology. Constructive
   directions; footprint {propositional_extensionality}. *)
Theorem alethe_walker_equiv_simplify_refl_axiom_free :
  forall (U : Type) (t : U), (t = t) = True.
Proof.
  intros U t.
  alethe_walker_test "(
    (step t0 (cl (= (= t t) true)) :rule equiv_simplify) )".
Qed.

Print alethe_walker_equiv_simplify_refl_axiom_free.
Print Assumptions alethe_walker_equiv_simplify_refl_axiom_free.

(* Pattern (= (not (not a)) a): double negation. The forward
   direction is classical (NNPP); footprint
   {classic, propositional_extensionality}. *)
Theorem alethe_walker_equiv_simplify_dneg_axiom_free :
  forall (a : Prop), (~ ~ a) = a.
Proof.
  intro a.
  alethe_walker_test "(
    (step t0 (cl (= (not (not a)) a)) :rule equiv_simplify) )".
Qed.

Print alethe_walker_equiv_simplify_dneg_axiom_free.
Print Assumptions alethe_walker_equiv_simplify_dneg_axiom_free.

(* Pattern (= (and a a) a): And idempotence. Constructive;
   footprint {propositional_extensionality}. *)
Theorem alethe_walker_equiv_simplify_and_idem_axiom_free :
  forall (a : Prop), (a /\ a) = a.
Proof.
  intro a.
  alethe_walker_test "(
    (step t0 (cl (= (and a a) a)) :rule equiv_simplify) )".
Qed.

Print alethe_walker_equiv_simplify_and_idem_axiom_free.
Print Assumptions alethe_walker_equiv_simplify_and_idem_axiom_free.

(* Pattern (= (or a a) a): Or idempotence. Constructive;
   footprint {propositional_extensionality}. *)
Theorem alethe_walker_equiv_simplify_or_idem_axiom_free :
  forall (a : Prop), (a \/ a) = a.
Proof.
  intro a.
  alethe_walker_test "(
    (step t0 (cl (= (or a a) a)) :rule equiv_simplify) )".
Qed.

Print alethe_walker_equiv_simplify_or_idem_axiom_free.
Print Assumptions alethe_walker_equiv_simplify_or_idem_axiom_free.

(* Pattern (= (not true) false): not-true collapse. Constructive;
   footprint {propositional_extensionality}. cvc5 emits this while
   collapsing a refuted reflexive equality (corpus prop_eq_trans). *)
Theorem alethe_walker_equiv_simplify_not_true_axiom_free :
  (~ True) = False.
Proof.
  alethe_walker_test "(
    (step t0 (cl (= (not true) false)) :rule equiv_simplify) )".
Qed.

Print alethe_walker_equiv_simplify_not_true_axiom_free.
Print Assumptions alethe_walker_equiv_simplify_not_true_axiom_free.

(* Trust-tagged leaf with a propositional-equality tautology body:
   cvc5 tags these TRUST_THEORY_REWRITE exactly like arithmetic
   rewrites, but lia can't discharge them — the walker's hole path
   first tries the equiv_simplify structural matcher (corpus
   prop_eq_trans's steps t5/t7). Footprint
   {propositional_extensionality}. *)
Theorem alethe_walker_hole_prop_tautology_axiom_free :
  forall (a : Prop), ((a = a) = True).
Proof.
  intro a.
  alethe_walker_test "(
    (step t0 (cl (= (= a a) true)) :rule hole :args (""TRUST_THEORY_REWRITE"")) )".
Qed.

Print alethe_walker_hole_prop_tautology_axiom_free.
Print Assumptions alethe_walker_hole_prop_tautology_axiom_free.

(* Negative: an equiv_simplify clause whose shape is not one of the
   recognized patterns must FAIL (handing control to the
   closer chain's fallback) rather than fabricate a proof. Here the
   sides are genuinely distinct props, so no tautology builder
   applies. Aborted, registers no axioms. *)
Theorem alethe_walker_equiv_simplify_unsupported_must_fail :
  forall (a b : Prop), (a /\ b) = a.
Proof.
  intros a b.
  Fail alethe_walker_test "(
    (step t0 (cl (= (and a b) a)) :rule equiv_simplify) )".
Abort.

(** Alethe walker — R-9 byContra wrapping (shared closer path).

    Mirror of lean-bridge/Test/Tactic.lean's
    [alethe_walker_byContra_axiom_free] (Lean #49). This exercises
    the same [walk_proof_into_goal] helper the production closer
    chain ([Pb_rocq_main.try_alethe_walker_lia]) now uses: a
    refutation trace (empty final clause) against a NON-[False]
    user goal. The walker first reduces [n >= 5] to [False] by
    classical contradiction ([apply NNPP; intro]), exposing
    [~ (n >= 5)] as a hypothesis the trace's [assume a1] matches;
    the la_generic leaf (n < 6 \/ n >= 5) + two resolutions then
    close [False]. Footprint [{classic}] — from the NNPP
    contradiction; the la_generic leaf is discharged by axiom-free
    [lia]. *)
Theorem alethe_walker_bycontra_axiom_free :
  forall (n : Z), n >= 6 -> n >= 5.
Proof.
  intros n h1.
  alethe_walker_test "(
    (assume a0 (>= n 6))
    (assume a1 (not (>= n 5)))
    (step t0 (cl (not (>= n 6)) (>= n 5)) :rule la_generic :args ())
    (step t1 (cl (not (>= n 6))) :rule resolution :premises (t0 a1))
    (step t2 (cl) :rule resolution :premises (t1 a0)) )".
Qed.

Print alethe_walker_bycontra_axiom_free.
Print Assumptions alethe_walker_bycontra_axiom_free.

(** Alethe walker — R-10 equiv_pos1 / equiv_pos2 (3-literal
    Boolean tautologies).

    Mirror of lean-bridge/Test/Tactic.lean's equiv_pos tests
    (Lean #50). The two positive-polarity halves of propositional-
    equivalence reasoning, deferred from the R-7 boolean cluster as
    they are nested case-splits. No premises; built by nested
    [classic] case analysis with the eq_mp/eq_mpr transports.
    Footprint [{classic}] — the transports go through axiom-free
    [eq_ind], so no propext is pulled. *)

(* equiv_pos1: ~(a=b) \/ a \/ ~b. *)
Theorem alethe_walker_equiv_pos1_axiom_free :
  forall (a b : Prop), ~ (a = b) \/ a \/ ~ b.
Proof.
  intros a b.
  alethe_walker_test "(
    (step t0 (cl (not (= a b)) a (not b)) :rule equiv_pos1) )".
Qed.

Print alethe_walker_equiv_pos1_axiom_free.
Print Assumptions alethe_walker_equiv_pos1_axiom_free.

(* equiv_pos2: ~(a=b) \/ ~a \/ b. *)
Theorem alethe_walker_equiv_pos2_axiom_free :
  forall (a b : Prop), ~ (a = b) \/ ~ a \/ b.
Proof.
  intros a b.
  alethe_walker_test "(
    (step t0 (cl (not (= a b)) (not a) b) :rule equiv_pos2) )".
Qed.

Print alethe_walker_equiv_pos2_axiom_free.
Print Assumptions alethe_walker_equiv_pos2_axiom_free.

(** Alethe walker — R-11 cong over built-in operators.

    Mirror of lean-bridge/Test/Tactic.lean's cong-over-operator
    tests (Lean #51). Real cvc5 LIA traces use [cong] to lift
    argument equalities through built-in operators ([not], [+],
    [<=], …), not just UF symbols — this is the congruence shape
    that lets a real alethe-2024 trace walk end-to-end rather than
    fall through to [lia]. No elaborator change was needed: the
    Constr-level [elab_cong] (built that way since R-5, as Coq has
    no [mkCongr]) already translates operator-headed lists via
    [sexp_to_constr] and peels the spine via [decompose_app] —
    operator heads ([Zadd]/[Zle]/[not]) decompose exactly like UF
    heads. All axiom-free: [cong] is [f_equal]/[eq_trans]/[eq_refl]. *)

(* cong over [not] (unary Prop operator): (~a) = (~b) from a = b. *)
Theorem alethe_walker_cong_not_axiom_free :
  forall (a b : Prop), a = b -> (~ a) = (~ b).
Proof.
  intros a b h.
  alethe_walker_test "(
    (assume a0 (= a b))
    (step t0 (cl (= (not a) (not b))) :rule cong :premises (a0)) )".
Qed.

Print alethe_walker_cong_not_axiom_free.
Print Assumptions alethe_walker_cong_not_axiom_free.

(* cong over [+] (binary operator over Z): x + z = y + w from
   x = y and z = w. The shape cvc5 emits lifting arg equalities
   through an addition during LIA normalization. *)
Theorem alethe_walker_cong_add_axiom_free :
  forall (x y z w : Z), x = y -> z = w -> x + z = y + w.
Proof.
  intros x y z w h1 h2.
  alethe_walker_test "(
    (assume a0 (= x y))
    (assume a1 (= z w))
    (step t0 (cl (= (+ x z) (+ y w))) :rule cong :premises (a0 a1)) )".
Qed.

Print alethe_walker_cong_add_axiom_free.
Print Assumptions alethe_walker_cong_add_axiom_free.

(* cong over [<=] (binary comparison, predicate-valued): the
   conclusion's equality is between two Props, exercising the
   per-argument chain when the operator's result type is Prop.
   The constant 5 position is carried by a [refl] premise. *)
Theorem alethe_walker_cong_le_axiom_free :
  forall (x y : Z), x = y -> (x <= 5)%Z = (y <= 5)%Z.
Proof.
  intros x y h.
  alethe_walker_test "(
    (assume a0 (= x y))
    (step t_refl (cl (= 5 5)) :rule refl)
    (step t0 (cl (= (<= x 5) (<= y 5))) :rule cong :premises (a0 t_refl)) )".
Qed.

Print alethe_walker_cong_le_axiom_free.
Print Assumptions alethe_walker_cong_le_axiom_free.
