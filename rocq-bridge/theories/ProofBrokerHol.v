(** Default HOL closer hook for [proof_broker] (roadmap §Phase 3
    deliverable 1 home-side, Rocq parity).

    The plugin's [closer_for_fragment "HOL" | "FOL"] dispatches
    to [Ltac proof_broker_hol_closer]; this file provides the
    {b default} definition: a fail-with-directive that leaves
    the goal OPEN and tells the user how to register a real
    closer. Audit H1: an un-registered HOL goal is a tactic
    failure, never an admitted theorem.

    Opt-in extensions:

    * [Require Import ProofBrokerHammer] redefines this Ltac to
      [hauto] from [coq-hammer] — the closest Rocq equivalent of
      Lean's [aesop]. Mirrors the [ProofBrokerMathlib] opt-in
      pattern on the Lean side: the core plugin remains
      Stdlib-only, with Hammer as a separate opam package.

    * Users can also redefine the closer locally:

        Ltac proof_broker_hol_closer ::= my_closer.

      The cert-verification gate (Tier-3 TSTP provenance for
      Vampire-minted certs) keeps the path sound — the closer
      runs on a goal the broker has already accepted as
      provable. Whatever proof term it emits is checked by the
      Rocq kernel, and the test theorem's [Print Assumptions]
      footprint is gated by [tools/check_axioms.py]. *)

Ltac proof_broker_hol_closer :=
  fail 1
    "proof_broker: no HOL closer registered for this fragment. "
    "[Require Import ProofBrokerHammer] enables coq-hammer's "
    "[hauto] (mirror of Lean's [aesop]); alternatively redefine "
    "[Ltac proof_broker_hol_closer ::= <your_closer>.] locally. "
    "The goal is OPEN until a sound closer fires — never "
    "admitted via an axiom (audit H1).".
