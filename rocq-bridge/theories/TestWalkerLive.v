(** End-to-end production path through the Alethe walker
    (cvc5 -> Tier-3 cert -> walker -> kernel), walker-STRICT.

    [proof_broker_walker] runs the full live pipeline — reify the
    goal, dispatch to cvc5, verify the minted cert — then closes ONLY
    via [Alethe_walker.walk_proof_into_goal] on that cert, with NO
    [lia] fallback. Plain [proof_broker] wraps the walker in
    [tclORELSE _ lia], so a regression anywhere in the LIVE walker
    path (cert-envelope shape, trace extraction from the cert, the
    walk itself) is silently masked by the fallback; this guards it.

    Goal is example1 (the canonical [n + m = 10, 0 <= m |- n <= 10]):
    cvc5 mints a Tier-3 alethe-2024 trace using the boolean-cleanup
    cluster (equiv_pos2 / hole / cong + the byContra wrapper), so a
    successful close proves the walker reconstructs a *real* live cert
    end-to-end, not just a committed corpus fixture. Footprint is the
    classical baseline ([classic] from the em case-splits,
    [propositional_extensionality] from the Prop-equality holes) — the
    same as the committed snapshot replay, but reached through the
    production dispatch rather than a hand-fed trace.

    Isolated in its own file (not in Test.v): the [Print] below dumps
    the full reconstructed term, and dune truncates per-action output
    head+tail — folding it into Test.v would evict sibling
    [Print Assumptions] blocks from the trust-footprint gate (the
    TestSnapshot.v lesson). *)

From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Classical_Prop PropExtensionality.
From ProofBroker Require Import ProofBrokerTermMode.

Declare ML Module "proof_broker_rocq.plugin".

Open Scope Z_scope.

Theorem pb_walker_live_axiom_free :
  forall n m : Z, n + m = 10 -> 0 <= m -> n <= 10.
Proof.
  intros n m h1 h3.
  proof_broker_walker.
Qed.

Print pb_walker_live_axiom_free.
Print Assumptions pb_walker_live_axiom_free.
