(** Refinement record (spec v1.0 §6.3, schema
    [schemas/v1.0/refinement-record.schema.json]).

    A refinement record is a structured description of an adapter's
    translation choices when refining an IR document into
    backend-native input. The reconstruction layer reads it in
    reverse during lifting; missing or unrecorded decisions are
    soundness-relevant per spec Requirement [Refinement record
    completeness]. *)

(** Specialization kind discriminator. New kinds added on the
    schema side that this OCaml version doesn't yet know land in
    [Other_kind] so the codec is forward-compatible. *)
type specialization_kind =
  | Type_specialization
  | Method_specialization
  | Axiomatization
  | Definition_unfolding
  | Logic_encoding
  | Rendering
  | Other_kind of string

let specialization_kind_to_string = function
  | Type_specialization -> "type_specialization"
  | Method_specialization -> "method_specialization"
  | Axiomatization -> "axiomatization"
  | Definition_unfolding -> "definition_unfolding"
  | Logic_encoding -> "logic_encoding"
  | Rendering -> "rendering"
  | Other_kind s -> s

let specialization_kind_of_string = function
  | "type_specialization" -> Type_specialization
  | "method_specialization" -> Method_specialization
  | "axiomatization" -> Axiomatization
  | "definition_unfolding" -> Definition_unfolding
  | "logic_encoding" -> Logic_encoding
  | "rendering" -> Rendering
  | s -> Other_kind s

(** One translation decision. [justification] and [soundness_witness]
    are required by the schema for the three soundness-critical kinds
    ([type_specialization], [method_specialization],
    [axiomatization]); the codec stores them as [option] so the
    schema check is the validator's job, not the codec's. *)
type specialization = {
  kind : specialization_kind;
  source : string;
  target : string;
  justification : string option;
  soundness_witness : string option;
}

type t = {
  adapter : string;
  adapter_version : string;
  specializations : specialization list;
  fragment : string;
  auxiliary : Yojson.Safe.t option;
}

(* --- codec ----------------------------------------------------------- *)

let assoc j = match j with
  | `Assoc pairs -> pairs
  | _ -> raise (Codec.Decode_error ("expected object", j))

let str = function
  | `String s -> s
  | j -> raise (Codec.Decode_error ("expected string", j))

let req k pairs : Yojson.Safe.t =
  try List.assoc k pairs
  with Not_found ->
    raise (Codec.Decode_error
             ("missing required field: " ^ k, `Assoc pairs))

let opt = List.assoc_opt

let specialization_of_json (j : Yojson.Safe.t) : specialization =
  let pairs = assoc j in
  {
    kind = specialization_kind_of_string (str (req "kind" pairs));
    source = str (req "source" pairs);
    target = str (req "target" pairs);
    justification = Option.map str (opt "justification" pairs);
    soundness_witness = Option.map str (opt "soundness_witness" pairs);
  }

let specialization_to_json (s : specialization) : Yojson.Safe.t =
  let f = [
    "kind", `String (specialization_kind_to_string s.kind);
    "source", `String s.source;
    "target", `String s.target;
  ] in
  let f = match s.justification with
    | None -> f
    | Some v -> f @ [ "justification", `String v ]
  in
  let f = match s.soundness_witness with
    | None -> f
    | Some v -> f @ [ "soundness_witness", `String v ]
  in
  `Assoc f

let of_json (j : Yojson.Safe.t) : t =
  let pairs = assoc j in
  let specs = match req "specializations" pairs with
    | `List xs -> List.map specialization_of_json xs
    | other ->
      raise (Codec.Decode_error
               ("expected array at specializations", other))
  in
  {
    adapter = str (req "adapter" pairs);
    adapter_version = str (req "adapter_version" pairs);
    specializations = specs;
    fragment = str (req "fragment" pairs);
    auxiliary = opt "auxiliary" pairs;
  }

let to_json (rr : t) : Yojson.Safe.t =
  let f = [
    "adapter", `String rr.adapter;
    "adapter_version", `String rr.adapter_version;
    "specializations",
    `List (List.map specialization_to_json rr.specializations);
    "fragment", `String rr.fragment;
  ] in
  let f = match rr.auxiliary with
    | None -> f
    | Some v -> f @ [ "auxiliary", v ]
  in
  `Assoc f
