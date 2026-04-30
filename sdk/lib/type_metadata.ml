(** Typed view of [type_metadata] entries (spec v1.0 §4.5,
    [schemas/v1.0/ir.schema.json]).

    The wire form remains a JSON pass-through inside [Ir.t] so that
    unknown construction kinds or future schema extensions round-trip
    losslessly. This module supplies a typed-decoder layer that
    consumers (passes, validators, future-typed adapters) can call
    when they need structured access. Anything that doesn't parse
    cleanly is returned as [Other] with the original JSON preserved;
    callers decide whether unknown shapes are an error for their
    use case.

    v1 covers the [type_constructor_application] kind in detail
    (because [Quotient_elimination] consumes it), with full structure
    only for [construction_kind = "quotient"]. Other construction
    kinds (inductive / sigma / refinement / higher_inductive) parse
    into a [ConstructorOther] variant carrying the raw JSON, ready
    to be promoted when a pass needs them. *)

module SM = Map.Make (String)

(** Parsed equivalence relation. The shell is the lambda
    [\a b => relation_body a b]; the proof is the name of the
    equivalence proof in the home system. *)
type equivalence_relation = {
  shell : Ir.shell_term;
  equivalence_proof : string;
}

(** Quotient-construction view: spec §4.5.2.
    [arguments] is the constructor application's type-level
    arguments (e.g., [n] for [MyZMod n]); the lifting layer needs
    them when reconstructing the original quotient type. *)
type quotient_constructor = {
  name : string;
  underlying_type : string;
  equivalence_relation : equivalence_relation;
  elimination_principle : string;
  equality_principle : string;
  arguments : Ir.shell_term list;
}

(** Constructor block of a [type_constructor_application] entry.
    Quotient is fully typed; other construction kinds live in
    [ConstructorOther] until a consumer needs them. *)
type constructor_block =
  | Quotient of quotient_constructor
  | ConstructorOther of {
      construction_kind : string;
      raw : Yojson.Safe.t;
    }

(** Top-level type-metadata entry. [TypeConstructorApplication]
    is the v1 covered shape; [OtherKind] preserves the JSON for
    forward compatibility (e.g., [type_alias] entries the schema
    might add later). *)
type entry =
  | TypeConstructorApplication of {
      qtype : string;
      constructor : constructor_block;
    }
  | OtherKind of {
      qtype : string;
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

let json_list_field (j : Yojson.Safe.t) (k : string) : Yojson.Safe.t list =
  match json_field j k with
  | Some (`List xs) -> xs
  | _ -> []

(* --- parsers --------------------------------------------------------- *)

let parse_equivalence_relation (j : Yojson.Safe.t)
  : equivalence_relation option =
  match json_field j "shell", json_string_field j "equivalence_proof" with
  | Some shell_j, Some proof ->
    (try
       let shell = Codec.shell_of_json shell_j in
       Some { shell; equivalence_proof = proof }
     with Codec.Decode_error _ -> None)
  | _ -> None

let parse_quotient_constructor (ctor : Yojson.Safe.t)
  : quotient_constructor option =
  match
    json_string_field ctor "name",
    json_string_field ctor "underlying_type",
    json_field ctor "equivalence_relation",
    json_string_field ctor "elimination_principle",
    json_string_field ctor "equality_principle"
  with
  | Some name, Some underlying, Some eqv_obj, Some elim, Some eq ->
    (match parse_equivalence_relation eqv_obj with
     | Some equivalence_relation ->
       let arguments =
         List.filter_map
           (fun arg_j ->
             try Some (Codec.shell_of_json arg_j)
             with Codec.Decode_error _ -> None)
           (json_list_field ctor "arguments")
       in
       Some {
         name;
         underlying_type = underlying;
         equivalence_relation;
         elimination_principle = elim;
         equality_principle = eq;
         arguments;
       }
     | None -> None)
  | _ -> None

let parse_constructor (ctor : Yojson.Safe.t) : constructor_block option =
  match json_string_field ctor "construction_kind" with
  | Some "quotient" ->
    (match parse_quotient_constructor ctor with
     | Some q -> Some (Quotient q)
     | None -> None)
  | Some other ->
    Some (ConstructorOther { construction_kind = other; raw = ctor })
  | None -> None

(** [parse (qtype, meta)] turns a single [type_metadata] map entry
    into a typed [entry], or [None] if the entry's shape is too
    malformed to even classify. Unknown kinds become [OtherKind] —
    not [None] — because the schema deliberately leaves room for
    future extensions and consumers should be able to walk past
    them. *)
let parse (qtype, meta : string * Yojson.Safe.t) : entry option =
  match json_string_field meta "kind" with
  | Some "type_constructor_application" ->
    (match json_field meta "constructor" with
     | Some ctor ->
       (match parse_constructor ctor with
        | Some constructor ->
          Some (TypeConstructorApplication { qtype; constructor })
        | None -> None)
     | None -> None)
  | Some kind ->
    Some (OtherKind { qtype; kind; raw = meta })
  | None -> None

(* --- helpers --------------------------------------------------------- *)

(** [parse_all ir] walks [ir.type_metadata] and returns a name-keyed
    map of entries that successfully classified. Off-shape entries
    (e.g., maps that lack a [kind] field) are silently dropped —
    the Python validator is the authoritative checker for such
    schema violations. *)
let parse_all (ir : Ir.t) : entry SM.t =
  List.fold_left
    (fun acc (qtype, meta) ->
      match parse (qtype, meta) with
      | Some e -> SM.add qtype e acc
      | None -> acc)
    SM.empty ir.type_metadata

(** [quotient_constructors ir] is the subset of typed entries whose
    constructor block is [Quotient]. Common case for
    [Quotient_elimination]. *)
let quotient_constructors (ir : Ir.t) : quotient_constructor SM.t =
  SM.fold
    (fun name e acc ->
      match e with
      | TypeConstructorApplication { constructor = Quotient q; _ } ->
        SM.add name q acc
      | _ -> acc)
    (parse_all ir) SM.empty

(** Lookup helper: returns the typed [quotient_constructor] for
    [qtype] if [type_metadata.[qtype]] is a quotient construction. *)
let find_quotient (ir : Ir.t) (qtype : string)
  : quotient_constructor option =
  SM.find_opt qtype (quotient_constructors ir)
