(** Trust-footprint tests for the quantifier rules (R-15):
    [forall_inst], [bind], and the existential-duality trust
    rewrite. Verbatim cvc5 1.3.0 traces for corpus [uf_forall_inst]
    and [uf_exists_witness] — the same proofs [CorpusReplay.v]
    compiles for the dynamic-replay gate, but here paired with
    [Print]/[Print Assumptions] so the trust-footprint gate
    ([tools/check_axioms.py]) pins each to the classical baseline.

    Isolated in its own file (not folded into [Test.v]): the full
    quantifier traces print large proof terms, and dune truncates
    per-action output head+tail — keeping them in a separate coqc
    action prevents their [Print] output from evicting sibling
    tests' [Print Assumptions] from the gate's view. *)

From Stdlib Require Import ZArith Lia.
(* [classic] (via NNPP) for forall_inst's excluded-middle split and
   the duality's by-contradiction; [propositional_extensionality]
   for bind's congruence-under-binder and the duality's iff. *)
From Stdlib Require Import Classical_Prop PropExtensionality.
From ProofBroker Require Import ProofBrokerTermMode.

Declare ML Module "proof_broker_rocq.plugin".

Open Scope Z_scope.

(* [forall_inst] (instantiate at 3) + [bind] (rewrite [f x <= 10] to
   [~ (f x >= 11)] under the [forall x] binder). Footprint: classical
   baseline ([classic] + [propositional_extensionality]). *)
Theorem alethe_walker_forall_inst_bind_axiom_free :
  forall (f : Z -> Z), (forall x : Z, f x <= 10) -> f 3 <= 10.
Proof. intros f h1. alethe_walker_test "(
(assume a0 (forall ((x Int)) (<= (f x) 10)))
(assume a1 (! (not (! (<= (! (f 3) :named @p_1) 10) :named @p_2)) :named @p_3))
(step t0 (cl (! (=> (forall ((x Int)) (not (>= (f x) 11))) (! (not (! (>= @p_1 11) :named @p_7)) :named @p_9)) :named @p_14) (forall ((x Int)) (not (>= (f x) 11)))) :rule implies_neg1)
(anchor :step t1)
(assume t1.a0 (forall ((x Int)) (not (>= (f x) 11))))
(step t1.t0 (cl (or (! (not (forall ((x Int)) (not (>= (f x) 11)))) :named @p_13) @p_9)) :rule forall_inst :args (3))
(step t1.t1 (cl @p_13 @p_9) :rule or :premises (t1.t0))
(step t1.t2 (cl (not (! (= (forall ((x Int)) (<= (f x) 10)) (forall ((x Int)) (not (>= (f x) 11)))) :named @p_4)) (not (forall ((x Int)) (<= (f x) 10))) (forall ((x Int)) (not (>= (f x) 11)))) :rule equiv_pos2)
(anchor :step t1.t3 :args ((x Int) (:= (x Int) x)))
(step t1.t3.t0 (cl (! (= (<= (! (f x) :named @p_5) 10) (not (>= @p_5 11))) :named @p_6)) :rule hole :args (""TRUST_THEORY_REWRITE"" @p_6 3 7))
(step t1.t3 (cl @p_4) :rule bind)
(step t1.t4 (cl (forall ((x Int)) (not (>= (f x) 11)))) :rule resolution :premises (t1.t2 t1.t3 a0))
(step t1.t5 (cl @p_9) :rule resolution :premises (t1.t1 t1.t4))
(step t1 (cl @p_13 @p_9) :rule subproof :discharge (t1.a0))
(step t2 (cl @p_14 @p_9) :rule resolution :premises (t0 t1))
(step t3 (cl @p_14 (! (not @p_9) :named @p_10)) :rule implies_neg2)
(step t4 (cl @p_14 @p_14) :rule resolution :premises (t2 t3))
(step t5 (cl @p_14) :rule contraction :premises (t4))
(step t6 (cl @p_13 @p_9) :rule implies :premises (t5))
(step t7 (cl @p_9 @p_13) :rule reordering :premises (t6))
(step t8 (cl (not (! (= @p_3 @p_7) :named @p_8)) (not @p_3) @p_7) :rule equiv_pos2)
(step t9 (cl (! (= @p_2 @p_9) :named @p_12)) :rule hole :args (""TRUST_THEORY_REWRITE"" @p_12 3 7))
(step t10 (cl (= @p_3 @p_10)) :rule cong :premises (t9))
(step t11 (cl (! (= @p_10 @p_7) :named @p_11)) :rule hole :args (""TRUST_THEORY_REWRITE"" @p_11 1 7))
(step t12 (cl @p_8) :rule trans :premises (t10 t11))
(step t13 (cl @p_7) :rule resolution :premises (t8 t12 a1))
(step t14 (cl (not @p_4) (not (forall ((x Int)) (<= (f x) 10))) (forall ((x Int)) (not (>= (f x) 11)))) :rule equiv_pos2)
(anchor :step t15 :args ((x Int) (:= (x Int) x)))
(step t15.t0 (cl @p_6) :rule hole :args (""TRUST_THEORY_REWRITE"" @p_6 3 7))
(step t15 (cl @p_4) :rule bind)
(step t16 (cl (forall ((x Int)) (not (>= (f x) 11)))) :rule resolution :premises (t14 t15 a0))
(step t17 (cl) :rule resolution :premises (t7 t13 t16))
)". Qed.

Print alethe_walker_forall_inst_bind_axiom_free.
Print Assumptions alethe_walker_forall_inst_bind_axiom_free.

(* [forall_inst] (instantiate the negated goal at witness [y]) + the
   existential-duality trust rewrite [(exists x, f x = 0) =
   ~(forall x, ~ (f x = 0))]. Footprint: classical baseline. *)
Theorem alethe_walker_exists_duality_axiom_free :
  forall (f : Z -> Z) (y : Z), f y = 0 -> exists x : Z, f x = 0.
Proof. intros f y h1. alethe_walker_test "(
(assume a0 (! (= (f y) 0) :named @p_1))
(assume a1 (! (not (exists ((x Int)) (= (f x) 0))) :named @p_2))
(step t0 (cl (! (=> (forall ((x Int)) (not (= (f x) 0))) (! (not @p_1) :named @p_8)) :named @p_9) (forall ((x Int)) (not (= (f x) 0)))) :rule implies_neg1)
(anchor :step t1)
(assume t1.a0 (forall ((x Int)) (not (= (f x) 0))))
(step t1.t0 (cl (or (! (not (forall ((x Int)) (not (= (f x) 0)))) :named @p_4) @p_8)) :rule forall_inst :args (y))
(step t1.t1 (cl @p_4 @p_8) :rule or :premises (t1.t0))
(step t1.t2 (cl (not (! (= @p_2 (forall ((x Int)) (not (= (f x) 0)))) :named @p_3)) (not @p_2) (forall ((x Int)) (not (= (f x) 0)))) :rule equiv_pos2)
(step t1.t3 (cl (! (= (exists ((x Int)) (= (f x) 0)) @p_4) :named @p_7)) :rule hole :args (""TRUST_THEORY_REWRITE"" @p_7 13 7))
(step t1.t4 (cl (= @p_2 (! (not @p_4) :named @p_5))) :rule cong :premises (t1.t3))
(step t1.t5 (cl (! (= @p_5 (forall ((x Int)) (not (= (f x) 0)))) :named @p_6)) :rule hole :args (""TRUST_THEORY_REWRITE"" @p_6 1 7))
(step t1.t6 (cl @p_3) :rule trans :premises (t1.t4 t1.t5))
(step t1.t7 (cl (forall ((x Int)) (not (= (f x) 0)))) :rule resolution :premises (t1.t2 t1.t6 a1))
(step t1.t8 (cl @p_8) :rule resolution :premises (t1.t1 t1.t7))
(step t1 (cl @p_4 @p_8) :rule subproof :discharge (t1.a0))
(step t2 (cl @p_9 @p_8) :rule resolution :premises (t0 t1))
(step t3 (cl @p_9 (not @p_8)) :rule implies_neg2)
(step t4 (cl @p_9 @p_9) :rule resolution :premises (t2 t3))
(step t5 (cl @p_9) :rule contraction :premises (t4))
(step t6 (cl @p_4 @p_8) :rule implies :premises (t5))
(step t7 (cl (not @p_3) (not @p_2) (forall ((x Int)) (not (= (f x) 0)))) :rule equiv_pos2)
(step t8 (cl @p_7) :rule hole :args (""TRUST_THEORY_REWRITE"" @p_7 13 7))
(step t9 (cl (= @p_2 @p_5)) :rule cong :premises (t8))
(step t10 (cl @p_6) :rule hole :args (""TRUST_THEORY_REWRITE"" @p_6 1 7))
(step t11 (cl @p_3) :rule trans :premises (t9 t10))
(step t12 (cl (forall ((x Int)) (not (= (f x) 0)))) :rule resolution :premises (t7 t11 a1))
(step t13 (cl) :rule resolution :premises (t6 a0 t12))
)". Qed.

Print alethe_walker_exists_duality_axiom_free.
Print Assumptions alethe_walker_exists_duality_axiom_free.
