(** End-to-end probe + closure test.

    Build success of this file is the test. [proof_broker] reifies
    the goal, dispatches through cvc4/cvc5/z3, verifies the cert,
    and closes via [lia] under cert-gating — same trust discipline
    as Lean's [omega] path. [proof_broker_test] is the non-closing
    debug form that just prints the cert summary. *)

From Stdlib Require Import ZArith Lia.

Declare ML Module "proof_broker_rocq.plugin".

Open Scope Z_scope.

(** Two-hypothesis LIA Farkas: x >= 5, x <= 3 ⊢ False. *)
Theorem pb_lia_axiom_free : forall x : Z, x >= 5 -> x <= 3 -> False.
Proof.
  intros x H1 H2.
  proof_broker.
Qed.

(** Axiom-footprint check, mirroring lean-bridge/Test/AxiomCheck.lean.
    The closer routes through Stdlib's [lia], which is axiom-free
    in the same sense Lean's [omega] is — the cert-gated call
    introduces no [proofBrokerCertSound]-style trust axiom. *)
Print Assumptions pb_lia_axiom_free.

(** Same goal, debug form: prints the cert summary, leaves the goal
    open, and the test discharges manually. Useful when you want
    to see what the broker minted without trusting the closer. *)
Goal forall x : Z, x >= 5 -> x <= 3 -> False.
Proof.
  intros x H1 H2.
  proof_broker_test.
  lia.
Qed.
