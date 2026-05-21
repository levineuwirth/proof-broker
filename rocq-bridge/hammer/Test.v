(** End-to-end Phase-3 worked-example test for the Rocq HOL
    closer (opt-in via [ProofBrokerHammer]).

    Mirrors lean-bridge/Test/TacticMathlib.lean's
    [hol_function_composition_axiom_free]. Function composition
    is supplied as a local UF parameter [comp] rather than
    Stdlib's polymorphic [compose] — same logical shape, no
    implicit-argument elaboration in the reifier, and the IR
    fragment is still "HOL" because the goal/hyps quantify over
    function types and equality is at function type.

    [proof_broker] reifies this to a higher-order IR
    ([order = "higher_order"]), [order] routes dispatch past the
    first-order SMT adapters to Vampire (THF), the minted Tier-3
    [tstp-thf] cert re-verifies through [Tier3_tptp]'s provenance
    gate ([Verified_tier3_provenance]), and the registered
    [proof_broker_hol_closer] ([hauto] from coq-hammer) emits
    the kernel proof term. Cert-gated and axiom-free in the same
    sense as [lia]/[lra]/[congruence] — the [Print Assumptions]
    footprint stays within the documented Rocq closer ceiling
    (pinned in [tools/axiom_allowlist.json]).

    Build success of this file is the test: any failure to
    elaborate [proof_broker] (Vampire missing, cert verifier
    rejecting, [hauto] failing to close) fails the build, and the
    trust-footprint gate independently parses [Print Assumptions]
    against the allowlist. *)

From Stdlib Require Import ZArith.
From ProofBroker Require Import ProofBrokerTermMode ProofBrokerHol.
From ProofBrokerHammer Require Import ProofBrokerHammer.
Declare ML Module "proof_broker_rocq.plugin".

Open Scope Z_scope.

Theorem pb_hol_function_composition_axiom_free :
  forall (f g : Z -> Z) (P : (Z -> Z) -> Prop)
         (comp : (Z -> Z) -> (Z -> Z) -> Z -> Z),
    (forall h : Z -> Z, P h -> P (comp h h)) ->
    P f ->
    f = g ->
    P (comp g g).
Proof.
  intros f g P comp h1 h2 h3.
  proof_broker.
Qed.

(* [Print <name>.] markers anchor each [Print Assumptions] block
   in build output for [tools/check_axioms.py]; mirrors the
   pattern in [rocq-bridge/theories/Test.v]. *)
Print pb_hol_function_composition_axiom_free.
Print Assumptions pb_hol_function_composition_axiom_free.
