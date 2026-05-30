(** Alethe walker — snapshot test against a real cvc5 trace.

    Mirror of lean-bridge/Test/Tactic.lean's
    [alethe_walker_real_cvc5_trace_axiom_free] (Lean #52). The trace
    below is the VERBATIM alethe-2024 output cvc5 minted for the goal
    [(n m : Z) (h1 : n + m = 10) (h3 : 0 <= m) |- n <= 10] — the same
    goal and trace string Lean PR #52 pinned, reused here per the
    port plan. Walking it via [alethe_walker_test] validates the Rocq
    walker against cvc5's actual output independently of live cvc5:
    CI needs no solver, and the trace text pins the walker against
    the real shape cvc5 emits. If cvc5 changes its format (rule
    names, ordering, sugar) this test surfaces the drift immediately.

    LIVES IN ITS OWN FILE: [Print]-ing the fully-walked proof term is
    large enough that, inside [Test.v]'s single coqc action, dune's
    action-output truncation (head+tail kept, middle dropped) would
    drop sibling theorems' [Print Assumptions] blocks out of the
    build log and break the trust-footprint gate. As its own
    compilation unit the large output is isolated; the [name =]
    marker (head) and the [Axioms:] block (tail) both survive
    truncation, so the gate still associates this theorem's footprint.

    What it exercises end-to-end, composing the whole arc:
    * cvc5's [(! expr :named @id)] syntax with [@p_X] back-references
      (parsed + expanded by the shared SDK);
    * byContra wrapping (R-9): the goal [n <= 10] is non-False, so the
      walker reduces it to [False] via [NNPP], exposing [~ (n <= 10)]
      for the trace's [assume a2] to match;
    * [equiv_pos2] (R-10, 3-literal tautology, no premises);
    * [hole] with TRUST_THEORY_REWRITE — re-derived independently of
      the tag (audit H1). Every hole here concludes a *propositional
      equality* of arithmetic facts, discharged via
      [propositional_extensionality] + [lia] (the [discharge_leaf]
      upgrade), not plain [lia];
    * [cong] over built-in operators [not] and [>=] (R-11);
    * [trans] chaining equalities, [refl] as a leaf;
    * multi-premise [resolution] closing the empty clause.

    Footprint [{classic, propositional_extensionality}] — classic
    from equiv_pos2 + the NNPP byContra; propext from the
    Prop-equality hole discharge. (Lean's mirror lands at
    [propext, Classical.choice, Quot.sound], the same classical+
    propositional baseline in Lean's axiom vocabulary.) *)

From Stdlib Require Import ZArith Lia.
(* [classic] / [NNPP] for the byContra wrapping; [classic] also via
   equiv_pos2. [propositional_extensionality] for the Prop-equality
   hole discharge. *)
From Stdlib Require Import Classical_Prop PropExtensionality.
From ProofBroker Require Import ProofBrokerTermMode.

Declare ML Module "proof_broker_rocq.plugin".

Open Scope Z_scope.

Theorem alethe_walker_real_cvc5_trace_axiom_free :
  forall (n m : Z), n + m = 10 -> 0 <= m -> n <= 10.
Proof.
  intros n m h1 h3.
  alethe_walker_test "(
    (assume a0 (! (= (+ n m) 10) :named @p_1))
    (assume a1 (! (<= 0 m) :named @p_2))
    (assume a2 (! (not (! (<= n 10) :named @p_3)) :named @p_4))
    (step t0 (cl (not (! (= @p_4 (! (not (! (>= m 0) :named @p_5)) :named @p_7)) :named @p_8)) (not @p_4) @p_7) :rule equiv_pos2)
    (step t1 (cl (! (= @p_3 (! (not (! (>= n 11) :named @p_9)) :named @p_15)) :named @p_18)) :rule hole :args (""TRUST_THEORY_REWRITE"" @p_18 3 7))
    (step t2 (cl (= @p_4 (! (not @p_15) :named @p_16))) :rule cong :premises (t1))
    (step t3 (cl (! (= @p_16 @p_9) :named @p_17)) :rule hole :args (""TRUST_THEORY_REWRITE"" @p_17 1 7))
    (step t4 (cl (= @p_4 @p_9)) :rule trans :premises (t2 t3))
    (step t5 (cl (not (! (= @p_1 (! (= n (! (+ 10 (* -1 m)) :named @p_10)) :named @p_13)) :named @p_14)) (not @p_1) @p_13) :rule equiv_pos2)
    (step t6 (cl @p_14) :rule hole :args (""TRUST_THEORY_REWRITE"" @p_14 3 7))
    (step t7 (cl @p_13) :rule resolution :premises (t5 t6 a0))
    (step t8 (cl (= 11 11)) :rule refl)
    (step t9 (cl (= @p_9 (! (>= @p_10 11) :named @p_11))) :rule cong :premises (t7 t8))
    (step t10 (cl (! (= @p_11 @p_7) :named @p_12)) :rule hole :args (""TRUST_THEORY_REWRITE"" @p_12 3 7))
    (step t11 (cl (= @p_9 @p_7)) :rule trans :premises (t9 t10))
    (step t12 (cl @p_8) :rule trans :premises (t4 t11))
    (step t13 (cl @p_7) :rule resolution :premises (t0 t12 a2))
    (step t14 (cl (not (! (= @p_2 @p_5) :named @p_6)) (not @p_2) @p_5) :rule equiv_pos2)
    (step t15 (cl @p_6) :rule hole :args (""TRUST_THEORY_REWRITE"" @p_6 3 7))
    (step t16 (cl @p_5) :rule resolution :premises (t14 t15 a1))
    (step t17 (cl) :rule resolution :premises (t13 t16)) )".
Qed.

Print alethe_walker_real_cvc5_trace_axiom_free.
Print Assumptions alethe_walker_real_cvc5_trace_axiom_free.
