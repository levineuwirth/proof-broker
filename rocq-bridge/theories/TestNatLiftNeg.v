(** R3-M1 ℕ→ℤ lift tests, negative tests — split from TestNatLift.v so
    the [Print]/[Print Assumptions] pairs survive dune's per-action
    output truncation (RUNBOOK trap; walker proof terms print
    large). *)

From Stdlib Require Import ZArith Arith Lia.
From Stdlib Require Import Classical_Prop PropExtensionality.
From ProofBroker Require Import ProofBrokerTermMode.

Declare ML Module "proof_broker_rocq.plugin".

(* ATTACK SURFACE (fail fast): ℕ subtraction is truncated — the
   reifier refuses it with a named error rather than cast naively.
   The whole tactic aborts BEFORE dispatch, so even plain
   [proof_broker]'s [lia] fallback never sees the goal. *)
Theorem pb_nat_sub_fails_closed :
  forall a b : nat, (a - b <= 3)%nat -> (a - b <= 4)%nat.
Proof.
  intros a b h.
  Fail proof_broker.
  lia.
Qed.

Print pb_nat_sub_fails_closed.
Print Assumptions pb_nat_sub_fails_closed.

(* Fail fast: ℕ division is outside the specialization. *)
Theorem pb_nat_div_fails_closed :
  forall a : nat, (a / 2 <= 3)%nat -> (a / 2 <= 4)%nat.
Proof.
  intros a h.
  Fail proof_broker.
  lia.
Qed.

Print pb_nat_div_fails_closed.
Print Assumptions pb_nat_div_fails_closed.

(* Fail fast: a ℕ quantifier INSIDE the formula (hypothesis
   position) has no ℤ image yet. *)
Theorem pb_nat_nested_forall_fails_closed :
  forall x : nat, (forall n : nat, x <= x + n)%nat -> (x <= x + 1)%nat.
Proof.
  intros x h.
  Fail proof_broker.
  lia.
Qed.

Print pb_nat_nested_forall_fails_closed.
Print Assumptions pb_nat_nested_forall_fails_closed.

(* Fail fast: ℕ arithmetic cannot mix with UF carriers in M1. *)
Theorem pb_nat_uf_mix_fails_closed :
  forall (x : nat) (f : Z -> Z),
    (f 0 = 0)%Z -> (x <= 3)%nat -> (x <= 4)%nat.
Proof.
  intros x f hf h.
  Fail proof_broker.
  lia.
Qed.

Print pb_nat_uf_mix_fails_closed.
Print Assumptions pb_nat_uf_mix_fails_closed.
