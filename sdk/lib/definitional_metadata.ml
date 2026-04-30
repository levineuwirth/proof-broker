(** Typed view of [definitional_metadata] entries (spec v1.0 §4.6,
    [schemas/v1.0/ir.schema.json]).

    Same approach as [Type_metadata]: the wire form remains JSON
    pass-through inside [Ir.t]; this module supplies a typed
    decoder that consumers (passes, future adapters) can call when
    they need structured access. The five v1 kinds —
    [primitive_arithmetic], [typeclass_method], [defined_function],
    [lifted_to_quotient], [constructor], [eliminator] — each get a
    typed variant; unknown kinds round-trip through [OtherKind]
    with the original JSON preserved. *)

module SM = Map.Make (String)

(** [primitive_arithmetic] entry. [theory_tag] is consumed by SMT
    adapters to map into LIA / LRA / etc.; the type system does not
    look at it. *)
type primitive_arithmetic = {
  abstract_signature : string;
  theory_tag : string;
}

(** [typeclass_method] entry. [specialization_targets] is preserved
    as JSON for now (a list of {theory, operator} objects); typed
    adapters can promote it later. *)
type typeclass_method = {
  method_name : string;
  host_class : string;
  abstract_role : string;
  specialization_targets : Yojson.Safe.t;
}

(** [defined_function] entry. The [definitional_equation] is the
    universal-quantified equality that [Definition_unfolding] uses
    to unfold use sites; [extensional_axiom] and [concept_tag] are
    optional metadata. *)
type defined_function = {
  abstract_signature : string;
  definitional_equation : Ir.shell_term;
  extensional_axiom : Ir.shell_term option;
  concept_tag : string option;
}

(** [lifted_to_quotient] entry. The lifting witness is the proof
    that [underlying_function] respects the host's equivalence
    relation; the lifting layer needs it to invert a
    [Quotient_elimination] unfolding. *)
type lifted_to_quotient = {
  host_type : string;
  underlying_function_name : string;
  underlying_function_shell : Ir.shell_term option;
  lifting_obligation_shape : string option;
  lifting_witness : string option;
}

(** Top-level entry. [Constructor] / [Eliminator] are placeholders
    for inductive types; structured fields are deferred until a
    consumer pass appears. *)
type entry =
  | PrimitiveArithmetic of {
      symbol : string;
      data : primitive_arithmetic;
    }
  | TypeclassMethod of {
      symbol : string;
      data : typeclass_method;
    }
  | DefinedFunction of {
      symbol : string;
      data : defined_function;
    }
  | LiftedToQuotient of {
      symbol : string;
      data : lifted_to_quotient;
    }
  | Constructor of {
      symbol : string;
      raw : Yojson.Safe.t;
    }
  | Eliminator of {
      symbol : string;
      raw : Yojson.Safe.t;
    }
  | OtherKind of {
      symbol : string;
      kind : string;
      raw : Yojson.Safe.t;
    }

(* --- low-level field readers (private) ------------------------------- *)

let json_string_field (j : Yojson.Safe.t) (k : string) : string option =
  match j with
  | `Assoc pairs ->
    (match List.assoc_opt k pairs with
     | Some (`String s) -> Some s
     | _ -> None)
  | _ -> None

let json_field (j : Yojson.Safe.t) (k : string) : Yojson.Safe.t option =
  match j with
  | `Assoc pairs -> List.assoc_opt k pairs
  | _ -> None

let parse_shell_opt (j : Yojson.Safe.t) : Ir.shell_term option =
  try Some (Codec.shell_of_json j)
  with Codec.Decode_error _ -> None

(* --- per-kind parsers ------------------------------------------------ *)

let parse_primitive_arithmetic (meta : Yojson.Safe.t)
  : primitive_arithmetic option =
  match
    json_string_field meta "abstract_signature",
    json_string_field meta "theory_tag"
  with
  | Some sig_, Some tag ->
    Some { abstract_signature = sig_; theory_tag = tag }
  | _ -> None

let parse_typeclass_method (meta : Yojson.Safe.t)
  : typeclass_method option =
  match
    json_string_field meta "method_name",
    json_string_field meta "host_class",
    json_string_field meta "abstract_role"
  with
  | Some m, Some h, Some r ->
    let targets = match json_field meta "specialization_targets" with
      | Some j -> j
      | None -> `List []
    in
    Some {
      method_name = m;
      host_class = h;
      abstract_role = r;
      specialization_targets = targets;
    }
  | _ -> None

let parse_defined_function (meta : Yojson.Safe.t)
  : defined_function option =
  match
    json_string_field meta "abstract_signature",
    json_field meta "definitional_equation"
  with
  | Some sig_, Some eq_j ->
    (match parse_shell_opt eq_j with
     | Some equation ->
       let extensional =
         match json_field meta "extensional_axiom" with
         | Some j -> parse_shell_opt j
         | None -> None
       in
       let concept = json_string_field meta "concept_tag" in
       Some {
         abstract_signature = sig_;
         definitional_equation = equation;
         extensional_axiom = extensional;
         concept_tag = concept;
       }
     | None -> None)
  | _ -> None

let parse_lifted_to_quotient (meta : Yojson.Safe.t)
  : lifted_to_quotient option =
  match
    json_string_field meta "host_type",
    json_field meta "underlying_function"
  with
  | Some host, Some uf ->
    (match json_string_field uf "name" with
     | Some name ->
       let shell =
         match json_field uf "shell" with
         | Some j -> parse_shell_opt j
         | None -> None
       in
       let obligation_shape, witness =
         match json_field meta "lifting_obligation" with
         | Some lo ->
           json_string_field lo "shape",
           json_string_field lo "witness"
         | None -> None, None
       in
       Some {
         host_type = host;
         underlying_function_name = name;
         underlying_function_shell = shell;
         lifting_obligation_shape = obligation_shape;
         lifting_witness = witness;
       }
     | None -> None)
  | _ -> None

(** [parse (symbol, meta)] classifies a single
    [definitional_metadata] entry into a typed [entry]. Per-kind
    field shape errors yield [None]; entirely-unknown [kind]s
    instead become [OtherKind] so consumers can opt into walking
    past them. *)
let parse (symbol, meta : string * Yojson.Safe.t) : entry option =
  match json_string_field meta "kind" with
  | Some "primitive_arithmetic" ->
    (match parse_primitive_arithmetic meta with
     | Some data -> Some (PrimitiveArithmetic { symbol; data })
     | None -> None)
  | Some "typeclass_method" ->
    (match parse_typeclass_method meta with
     | Some data -> Some (TypeclassMethod { symbol; data })
     | None -> None)
  | Some "defined_function" ->
    (match parse_defined_function meta with
     | Some data -> Some (DefinedFunction { symbol; data })
     | None -> None)
  | Some "lifted_to_quotient" ->
    (match parse_lifted_to_quotient meta with
     | Some data -> Some (LiftedToQuotient { symbol; data })
     | None -> None)
  | Some "constructor" ->
    Some (Constructor { symbol; raw = meta })
  | Some "eliminator" ->
    Some (Eliminator { symbol; raw = meta })
  | Some kind ->
    Some (OtherKind { symbol; kind; raw = meta })
  | None -> None

(* --- helpers --------------------------------------------------------- *)

(** [parse_all ir] returns a symbol-keyed map of typed entries. *)
let parse_all (ir : Ir.t) : entry SM.t =
  List.fold_left
    (fun acc (sym, meta) ->
      match parse (sym, meta) with
      | Some e -> SM.add sym e acc
      | None -> acc)
    SM.empty ir.definitional_metadata

(** Symbol-keyed map of just [DefinedFunction] entries. *)
let defined_functions (ir : Ir.t) : defined_function SM.t =
  SM.fold
    (fun sym e acc ->
      match e with
      | DefinedFunction { data; _ } -> SM.add sym data acc
      | _ -> acc)
    (parse_all ir) SM.empty

(** Symbol-keyed map of just [LiftedToQuotient] entries. *)
let lifted_symbols (ir : Ir.t) : lifted_to_quotient SM.t =
  SM.fold
    (fun sym e acc ->
      match e with
      | LiftedToQuotient { data; _ } -> SM.add sym data acc
      | _ -> acc)
    (parse_all ir) SM.empty

(** Lookup helpers. *)

let find_defined_function (ir : Ir.t) (symbol : string)
  : defined_function option =
  SM.find_opt symbol (defined_functions ir)

let find_lifted_to_quotient (ir : Ir.t) (symbol : string)
  : lifted_to_quotient option =
  SM.find_opt symbol (lifted_symbols ir)
