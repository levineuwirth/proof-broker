(** UF-reach closure tests for [proof_broker] (moved out of Test.v).

    Since R1.3 the UF arm is walker-FIRST: a cvc5 Tier-3
    alethe-2024 cert is walked into a kernel term ("cert IS the
    proof") before the [congruence | subst; assumption] re-proving
    chain, so these four closures now print large walker proof
    terms (classical [Or.elim] cascades) instead of tiny
    congruence terms. They live in their OWN file because dune
    truncates per-action output head+tail: inside Test.v the four
    [Print] dumps pushed the shared action over the cap and
    evicted a NEIGHBOR's [Print] marker from the trust-footprint
    gate (the TestSnapshot.v lesson). Footprint
    per theorem: [classic] (+ [propositional_extensionality] where
    the trace carries Prop-equality holes) — the walker baseline,
    allowlisted in tools/axiom_allowlist.json. *)

From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Classical_Prop PropExtensionality.
From ProofBroker Require Import ProofBrokerTermMode.

Declare ML Module "proof_broker_rocq.plugin".

Open Scope Z_scope.

(** UF reach: arity-1 congruence, mirroring Lean's
    [uf_axiom_free]. The reifier walks [f : Z -> Z] into a free_var
    with [ty = "Int->Int"], the SDK serializer emits
    [(declare-fun f (Int) Int)], cvc5 returns unsat under QF_UFLIA,
    and the walker reconstructs the trace into a kernel term (the
    closer chain [congruence | subst; assumption] is the
    fallback). *)
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
    SMT-LIB sort [Bool] via [Smtlib.sort_of_type_ref]. *)
Theorem pb_uf_predicate_axiom_free :
  forall (P : Z -> Prop) (x y : Z), P x -> x = y -> P y.
Proof.
  intros P x y Hp H.
  proof_broker.
Qed.

Print pb_uf_axiom_free.
Print Assumptions pb_uf_axiom_free.

Print pb_uf_two_arg_axiom_free.
Print Assumptions pb_uf_two_arg_axiom_free.

Print pb_uf_composed_axiom_free.
Print Assumptions pb_uf_composed_axiom_free.

Print pb_uf_predicate_axiom_free.
Print Assumptions pb_uf_predicate_axiom_free.
