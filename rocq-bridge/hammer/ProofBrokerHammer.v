(** [proof_broker_rocq_hammer]: coq-hammer-based HOL closer opt-in
    for [proof_broker] (roadmap §Phase 3 deliverable 1 home-side,
    Rocq parity).

    Importing this module redefines [proof_broker_hol_closer]
    (defined fail-closed in [ProofBroker.ProofBrokerHol]) to
    [hauto] — coq-hammer's reconstruction tactic, the closest
    Rocq has to Lean's [aesop]. Mirror of the
    [ProofBrokerMathlib]-style opt-in pattern on the Lean side:
    the core Rocq plugin stays Stdlib-only, with
    [coq-hammer-tactics] as a separate opam package the user
    opts into.

    Soundness. The cert-verification gate (Tier-3 TSTP provenance
    for Vampire-minted certs) ensures [hauto] runs only on goals
    the broker has already accepted as provable. Whatever proof
    term [hauto] emits is kernel-checked by Rocq, and the test
    theorem's [Print Assumptions] footprint is gated by
    [tools/check_axioms.py]. Audit H1: no closer ever closes a
    goal via an admitted axiom; an [hauto] failure is a tactic
    failure with the goal left OPEN.

    Users can further override locally:

        Ltac proof_broker_hol_closer ::= my_custom_closer.

    *)

(* [coq-hammer-tactics] (the package this opam-depends on) exposes
   the reconstruction tactics under [Hammer.Tactics]: [hauto],
   [sauto], [scrush], etc. We use [coq-hammer-tactics] rather than
   the full [coq-hammer] package because we only need the
   reconstruction layer — the ATP-prediction stage that ships an
   external ATP isn't relevant here (the broker has already chosen
   which Tier-3 cert to close). Lighter opam dep footprint, same
   closer reach for the goals Vampire-HOL is already producing
   certs for. *)
From Hammer Require Import Tactics.
From ProofBroker Require Import ProofBrokerHol.

Ltac proof_broker_hol_closer ::= hauto.
