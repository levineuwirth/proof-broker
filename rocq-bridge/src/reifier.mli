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
