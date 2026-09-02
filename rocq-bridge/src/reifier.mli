(** Reify a Rocq goal-state into a [Proof_broker.Ir.t] tagged for LIA.

    The cross-system test the Phase 4 probe is built around: the IR
    produced here must be byte-identical (modulo source_system fields)
    to what Lean's reifier produces for the corresponding goal, so the
    same dispatch + verify pipeline accepts both. That means using
    Lean's typeclass-flavored [App] symbols ([HAdd.hAdd], [LE.le], ...)
    even though the underlying Rocq operators are [Z.add], [Z.le], etc.
    The SDK's Farkas linearizer accepts both vocabularies, but matching
    Lean's exact emission is the load-bearing test. *)

exception Reify_error of string

val nat_atoms : (string * EConstr.t) list ref
(** R3-M1: [payload_id ↦ nat subterm] for every atomized nonlinear ℕ
    product of the LAST [build_ir] run (reset on entry; the plugin's
    tactic execution is single-threaded). [pb_rocq_main] snapshots it
    into the extraction path right after reification. *)

val nat_literal : Evd.evar_map -> EConstr.t -> Z.t option
(** Structural nat-literal walker ([O]/[S]-chains and
    [Nat.of_num_uint (Number.UIntDecimal _)] big-literal forms; no
    reduction). Shared with [Term_mode]'s push-cast so the lift's
    literal/atom decisions coincide with the reifier's. *)

val r_nat_pow : EConstr.t option Lazy.t
(** [Nat.pow], resolved by qualid (no lib_ref registration). *)

val r_nat_of_num_uint : EConstr.t option Lazy.t
(** [Nat.of_num_uint], resolved by qualid. [Term_mode] matches it to
    route big-decimal literal leaves through the structural
    [nat_of_num_uint_dec] lemma instead of unary kernel conversion. *)

val r_uint_decimal_ctor : EConstr.t option Lazy.t
(** [Number.UIntDecimal], resolved by qualid (scopes the leaf route
    to the decimal constructor the literal fold understands). *)

val r_z_of_nat : EConstr.t option Lazy.t
(** [Z.of_nat], resolved by qualid. *)

val reify_z_literal :
  Environ.env -> Evd.evar_map -> EConstr.t -> string option
(** Walk a [Z]-typed closed literal — [Z0]/[Zpos p]/[Zneg p] with [p]
    built from [xH]/[xO]/[xI] — and flatten to a decimal string. *)

val reify_term :
  Environ.env -> Evd.evar_map -> EConstr.t -> Proof_broker.Ir.shell_term
(** Reify a single [Z]-typed expression or [Prop]-typed formula in
    the LIA fragment. Raises [Reify_error] on anything outside it. *)

val build_ir : Proofview.Goal.t -> Proof_broker.Ir.t
(** Reify the current goal + named [Prop] hypotheses + [Z]-typed locals
    into an [Ir.t] with [logic_classification.first_order_fragment =
    "LIA"], [tier = "goal"], [source_system = {name = "rocq"; version}]. *)
