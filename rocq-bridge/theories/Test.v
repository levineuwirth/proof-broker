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
