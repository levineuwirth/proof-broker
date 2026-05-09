(** End-to-end probe + closure test, exercising every surface form.

    Build success of this file is the test. Each [proof_broker]
    invocation reifies the goal, dispatches through the broker,
    verifies the cert, and (in the closing forms) hands the goal
    to Stdlib's [lia] under cert-gating — same trust discipline
    as Lean's [omega] path. *)

From Stdlib Require Import ZArith Lia.

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

(** Axiom-footprint check, mirroring lean-bridge/Test/Tactic.lean's
    [#print axioms] discipline. The closer routes through Stdlib's
    [lia], which is axiom-free in the same sense Lean's [omega] is —
    cert-gated calls introduce no [proofBrokerCertSound]-style trust
    axiom. Each named theorem above closes without dependencies on
    any axiom, so [Print Assumptions] reports "Closed under the
    global context" — even cleaner than Lean's [propext, Quot.sound]
    footprint. *)
Print Assumptions pb_lia_axiom_free.
Print Assumptions pb_lia_explicit_list.
Print Assumptions pb_lia_verbose.
