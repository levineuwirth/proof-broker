(** R3-M1 ℕ→ℤ lift tests, continued — split from TestNatLift.v so
    the [Print]/[Print Assumptions] pairs survive dune's per-action
    output truncation (RUNBOOK trap; walker proof terms print
    large). *)

From Stdlib Require Import ZArith Arith Lia.
From Stdlib Require Import Classical_Prop PropExtensionality.
From ProofBroker Require Import ProofBrokerTermMode.

Declare ML Module "proof_broker_rocq.plugin".

(* A leading [forall (n : nat)] goal binder is introduced before
   reification; the introduced form dispatches and walks. *)
Theorem pb_nat_walker_forall_axiom_free :
  forall n : nat, (n + 1 >= 1)%nat.
Proof. proof_broker_walker. Qed.

Print pb_nat_walker_forall_axiom_free.
Print Assumptions pb_nat_walker_forall_axiom_free.

(* The D1 shape (verinf lift_cell core): a nonlinear ℕ product
   [zmax * zhigh] is atomized to an Opaque payload atom, its bound
   rides along, and the goal closes through the walker with the
   atom mapped back to [Z.of_nat (zmax * zhigh)]. *)
Theorem pb_nat_walker_d1_axiom_free :
  forall x z zmax zhigh : nat,
    (x < 2^24)%nat -> (z < 2 * zmax)%nat ->
    (zmax * zhigh <= zmax)%nat ->
    (x + z < 2^24 + 2 * zmax)%nat.
Proof. intros x z zmax zhigh hx hz hprod. proof_broker_walker. Qed.

Print pb_nat_walker_d1_axiom_free.
Print Assumptions pb_nat_walker_d1_axiom_free.

(* Term mode consumes the atomized product: the atom is the middle
   variable of a bound chain, so the Farkas witness names both its
   bound and its nonneg fact. Footprint empty. *)
Theorem pb_nat_term_d1_axiom_free :
  forall x zmax zhigh : nat,
    (x + 1 <= zmax * zhigh)%nat -> (zmax * zhigh <= 5)%nat ->
    (x <= 4)%nat.
Proof. intros x zmax zhigh hx hp. proof_broker_term. Qed.

Print pb_nat_term_d1_axiom_free.
Print Assumptions pb_nat_term_d1_axiom_free.

(* nat equality goal: split via Nat.le_antisymm, each direction a
   fresh dispatch + lift; both directions are multi-hypothesis
   combinations (each mints a Tier-1 Farkas witness). Footprint
   empty. *)
Theorem pb_nat_term_eq_axiom_free :
  forall x y w : nat,
    (x + 1 <= y)%nat -> (y <= 5)%nat ->
    (6 <= x + 2 * w)%nat -> (w <= 1)%nat ->
    x = 4%nat.
Proof. intros x y w h1 h2 h3 h4. proof_broker_term. Qed.

Print pb_nat_term_eq_axiom_free.
Print Assumptions pb_nat_term_eq_axiom_free.

