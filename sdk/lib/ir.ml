(** IR types for spec v1.0.

    Mirrors [schemas/v1.0/ir.schema.json]. The shell calculus is a tagged
    variant with inline records (one per [node] discriminator). Top-level
    metadata maps that this Phase-0 spike does not yet structure as ADTs
    ([type_metadata], [definitional_metadata]) are stored as
    [Yojson.Safe.t] pass-through; full ADTs follow in Phase 1+. *)

type type_ref = string
(** A type reference. Either a shell primitive ("Int", "Nat", "Bool",
    "String", "Prop", "Type", "Real", "Rat", a "Bitvec(n)" form, or a
    function arrow) or a key into [type_metadata] / [context.type_vars]. *)

type binder = {
  var : string;
  ty : type_ref;
}

type shell_term =
  | Forall  of { var : string; ty : type_ref; body : shell_term }
  | Exists  of { var : string; ty : type_ref; body : shell_term }
  | Lambda  of { binders : binder list; body : shell_term }
  | Implies of { antecedent : shell_term; consequent : shell_term }
  | And     of { left : shell_term; right : shell_term }
  | Or      of { left : shell_term; right : shell_term }
  | Not     of { operand : shell_term }
  | Eq      of { ty : type_ref; left : shell_term; right : shell_term }
  | App     of { symbol : string; type_args : type_ref list; args : shell_term list }
  | Var     of { name : string }
  | Const   of { name : string }
  | Num_lit of { value : string; ty : type_ref }
  | Opaque  of { payload_id : string }

type goal = {
  shell : shell_term;
  payloads : (string * Yojson.Safe.t) list option;
}

type free_var = { name : string; ty : type_ref }

type hypothesis = { name : string; shell : shell_term }

type library_slice_entry = {
  entity_name : string;
  shell : shell_term;
  selection_reason : string option;
}

type context = {
  type_vars : string list;
  free_vars : free_var list;
  hypotheses : hypothesis list;
  library_slice : library_slice_entry list option;
}

type logic_classification = {
  order : string;
  features_used : string list;
  first_order_fragment : string;
  decidable_theory : string option;
}

type provenance = {
  library : string;
  version : string;
  module_path : string option;
  content_hash : string;
}

type budget = {
  wall_time_ms : int option;
  memory_mb : int option;
}

type rewriter_preferences = {
  enable_quotient_elimination : bool option;
  enable_definition_unfolding : string list option;
  disable_passes : string list option;
}

type user_directives = {
  preferred_backend : [ `Null | `String of string ] option;
  (** Three states: [None] = field absent; [Some `Null] = explicit JSON
      null (no preference set); [Some (`String s)] = backend named. *)
  tier_preference : string list option;
  rewriter_preferences : rewriter_preferences option;
  budget : budget option;
}

type source_system = { name : string; version : string }

type t = {
  ir_version : string;
  source_system : source_system;
  tier : string;
  logic_classification : logic_classification;
  goal : goal;
  context : context;
  type_metadata : (string * Yojson.Safe.t) list;
  (** Pass-through: structured ADTs deferred to Phase 1+. *)
  definitional_metadata : (string * Yojson.Safe.t) list;
  (** Pass-through: structured ADTs deferred to Phase 1+. *)
  library_provenance : (string * provenance) list;
  user_directives : user_directives option;
}
