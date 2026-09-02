(** R3-M1: ℕ→ℤ specialization + lift tests (mirror of lean-bridge's
    pb_nat_* suite in Test/Tactic.lean).

    The reifier hands the broker the ℤ image of a nat goal (cast
    shells, [_pb_nonneg_*] hypotheses, primitive-kind metadata with
    real embedding witnesses); the cert-consuming closers rebuild
    the nat proof from the ℤ certificate through the constructive
    [nat_cast_*] shims. The M1 Rocq gate is the FOOTPRINT: the
    term-mode nat theorems below must print "Closed under the
    global context" — the whole lift (push-cast, transfer, wrapper,
    Farkas fold, [ring]) is axiom-free. Walker theorems stay within
    the walker's classical ceiling ([by_contradiction] → NNPP →
    [classic]).

    Negative tests pin the fail-fast scope rules: ℕ subtraction
    (the truncation attack surface), ℕ division, nested ℕ
    quantifiers, ℕ×UF mixing.

    Own file so the [Print]/[Print Assumptions] pairs survive dune's
    per-action output truncation (RUNBOOK trap). *)

From Stdlib Require Import ZArith Arith Lia.
From Stdlib Require Import Classical_Prop PropExtensionality.
From ProofBroker Require Import ProofBrokerTermMode.

Declare ML Module "proof_broker_rocq.plugin".

(* Plain [proof_broker] on nat: reify ℤ image → dispatch → the
   walker's cast layer, else cert-gated [lia] on the original
   goal. *)
Theorem pb_nat_plain_axiom_free :
  forall x y : nat, (x + 1 <= y)%nat -> (y <= 5)%nat -> (x <= 4)%nat.
Proof. intros x y h1 h2. proof_broker. Qed.

Print pb_nat_plain_axiom_free.
Print Assumptions pb_nat_plain_axiom_free.

(* Term mode on nat: the Tier-1 Farkas witness is consumed against
   the ℤ images of the hypotheses (cast by term construction), the
   goal enters through the constructive [nat_le_via_lt] wrapper —
   no decision procedure touches the original goal, and the
   footprint is EMPTY (the M1 Rocq gate). *)
Theorem pb_nat_term_axiom_free :
  forall x y : nat, (x + 1 <= y)%nat -> (y <= 5)%nat -> (x <= 4)%nat.
Proof. intros x y h1 h2. proof_broker_term. Qed.

Print pb_nat_term_axiom_free.
Print Assumptions pb_nat_term_axiom_free.

(* Walker-strict on nat: the live cvc5 alethe trace is walked into
   a kernel term through the cast layer ("cert IS the proof" at ℕ). *)
Theorem pb_nat_walker_axiom_free :
  forall x y : nat, (x + 1 <= y)%nat -> (y <= 5)%nat -> (x <= 4)%nat.
Proof. intros x y h1 h2. proof_broker_walker. Qed.

Print pb_nat_walker_axiom_free.
Print Assumptions pb_nat_walker_axiom_free.

(* 2^24-scale literals: the reifier constant-folds the closed pow;
   the push-cast discharges the Z-side computation by [eq_refl]
   (binary Z literals). The PLAIN decimal literal in the goal rides
   the structural [nat_of_num_uint_dec] leaf (delta §5.4 follow-up)
   — the kernel computes [Z.of_num_uint] in binary instead of
   normalizing the unary numeral, so 2^24 scale is cheap again. *)
Theorem pb_nat_walker_pow_axiom_free :
  forall x : nat, (x < 2^24)%nat -> (x <= 16777215)%nat.
Proof. intros x h. proof_broker_walker. Qed.

Print pb_nat_walker_pow_axiom_free.
Print Assumptions pb_nat_walker_pow_axiom_free.

(* D2-scale plain decimal (the 2^64-2^32+1 Goldilocks prime): the
   structural leaf is value-independent, so a literal that unary
   normalization could NEVER reach (2^64 ≈ 10^19 constructors)
   closes in term mode. Pins the leaf route on the term-mode
   consumer; the walker consumer is pinned by the 2^24 goal above
   (both routes share [push_nat_to_z]). *)
Theorem pb_nat_term_big_dec_axiom_free :
  forall x y : nat,
    (x + 1 <= y)%nat -> (y <= 18446744069414584321)%nat ->
    (x <= 18446744069414584320)%nat.
Proof. intros x y h1 h2. proof_broker_term. Qed.

Print pb_nat_term_big_dec_axiom_free.
Print Assumptions pb_nat_term_big_dec_axiom_free.

(* A big-decimal BASE under a folded pow (in-contract: any exponent
   <= 256): the pow arm's cast-premise shim [nat_push_pow_cast]
   recurses the base through the structural leaf. The base is the
   D2-scale prime (2^64-2^32+1) ON PURPOSE: at this scale unary
   normalization is UNREACHABLE (~10^19 constructors), so deleting
   the cast routing turns this theorem red rather than merely slow —
   the pin is load-bearing (a 2^24-scale base would regress to
   6GB/139s but still build green under CI's limits). *)
Theorem pb_nat_term_big_pow_axiom_free :
  forall x y : nat,
    (x + 1 <= y)%nat ->
    (y <= 18446744069414584321 ^ 2)%nat ->
    (x <= 340282366762482138490186164457219031040)%nat.
Proof. intros x y h1 h2. proof_broker_term. Qed.

Print pb_nat_term_big_pow_axiom_free.
Print Assumptions pb_nat_term_big_pow_axiom_free.

