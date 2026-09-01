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

(* The R3-M1 specialization gate, pinned fail-closed INDEPENDENT of
   live dispatch (C3a ROUND 1 finding 2): no live path mints a foreign
   specialization or a spec-less ℕ cert, so these drive the real
   [check_cert_specializations] on synthetic certs via the test-only
   [pb_spec_gate_test]. Deleting the "cannot invert" branch flips the
   foreign/mixed tests; deleting the "records no Nat -> Int" branch
   flips the nat-none test. *)

Theorem pb_spec_gate_nat_spec_passes : True.
Proof. pb_spec_gate_test nat nat_spec. Qed.

Print pb_spec_gate_nat_spec_passes.
Print Assumptions pb_spec_gate_nat_spec_passes.

Theorem pb_spec_gate_int_none_passes : True.
Proof. pb_spec_gate_test int none. Qed.

Print pb_spec_gate_int_none_passes.
Print Assumptions pb_spec_gate_int_none_passes.

Theorem pb_spec_gate_missing_fails_closed : True.
Proof. Fail pb_spec_gate_test nat none. exact I. Qed.

Print pb_spec_gate_missing_fails_closed.
Print Assumptions pb_spec_gate_missing_fails_closed.

Theorem pb_spec_gate_foreign_fails_closed : True.
Proof. Fail pb_spec_gate_test int foreign_spec. exact I. Qed.

Print pb_spec_gate_foreign_fails_closed.
Print Assumptions pb_spec_gate_foreign_fails_closed.

Theorem pb_spec_gate_mixed_fails_closed : True.
Proof. Fail pb_spec_gate_test nat mixed_spec. exact I. Qed.

Print pb_spec_gate_mixed_fails_closed.
Print Assumptions pb_spec_gate_mixed_fails_closed.

(* Fail fast even under atomization (C3a ROUND 1 finding 5): a
   nonlinear product HIDING ℕ subtraction is refused with the named
   error, not silently swallowed as an Opaque atom. *)
Theorem pb_nat_sub_in_atom_fails_closed :
  forall a b c : nat, ((a - b) * c <= 3)%nat -> ((a - b) * c <= 4)%nat.
Proof.
  intros a b c h.
  Fail proof_broker.
  lia.
Qed.

Print pb_nat_sub_in_atom_fails_closed.
Print Assumptions pb_nat_sub_in_atom_fails_closed.
