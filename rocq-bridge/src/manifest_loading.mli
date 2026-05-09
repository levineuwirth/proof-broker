(** Locate + load the cvc4/cvc5/z3 adapter manifests that ship under
    [examples/]. Mirrors [lean-bridge/ProofBroker/Tactic.lean]'s
    convention so the env-var [PROOF_BROKER_EXAMPLES_DIR] works for
    both bridges. Falls back to [<cwd>/../examples] when unset. *)

val load_default : unit -> Proof_broker.Manifest.t list
(** Returns the manifests for any of [cvc4]/[cvc5]/[z3] that exist in
    the resolved directory. Order is the input order [cvc4; cvc5; z3];
    [Manifest.sort_by_max_tier_descending] is the caller's job if a
    tier-first ordering is wanted. Raises [CErrors.user_err] when
    zero manifests load (the directory is wrong or empty). *)
