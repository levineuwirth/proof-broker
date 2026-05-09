(** Locate + load adapter manifests shipped under [examples/].

    Mirrors [lean-bridge/ProofBroker/Tactic.lean]'s convention so
    [PROOF_BROKER_EXAMPLES_DIR] works for both bridges. The fallback
    walks upward from cwd looking for [examples/manifest-cvc4.json];
    Lean's fixed [<cwd>/../examples] doesn't transfer because dune's
    [rocq compile] cwd lives at a varying depth under [_build/]. *)

val load_default : unit -> Proof_broker.Manifest.t list
(** All of [cvc4]/[cvc5]/[z3] that exist in the resolved dir, in
    that order. Caller sorts by tier if a tier-first ordering is
    wanted. Raises [CErrors.user_err] when zero manifests load. *)

val load_named : string list -> Proof_broker.Manifest.t list
(** Manifests for the user-supplied adapter names, in the given
    order. Each name is resolved as [manifest-<name>.json];
    unknown names raise [CErrors.user_err]. The bracketed-list
    form intentionally bypasses [sort_by_max_tier_descending] so
    the caller's order is the actual dispatch order — same
    discipline as Lean's [proof_broker [cvc5, z3]] form. *)
