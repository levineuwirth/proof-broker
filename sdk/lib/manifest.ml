(** Adapter capability manifest (spec v1.0 §7.4, schema
    [schemas/v1.0/adapter-manifest.schema.json]).

    A manifest declares what an adapter can dispatch into: which
    logic fragments, which type constructions, which tiers / trace
    formats / witness kinds it produces, and the rewriting pipeline
    it prefers as preprocessing.

    This module supplies the OCaml-side typed ADTs plus codec.
    Capability matching against an [Ir.t] lives in
    [Capability_match]. The Python validator
    ([tools/check.py]) remains authoritative for schema-level
    rules (uniqueItems, the [tiers_produced ⇒ trace_formats_produced]
    conditional, etc.); the codec here parses any document that
    has the required field shapes and silently preserves
    schema-violation cases on round-trip rather than rejecting
    them — division of responsibility consistent with the metadata
    decoders in [Type_metadata] / [Definitional_metadata]. *)

(** Optional pass step inside [preferred_rewrite_pipeline]. The
    [config] field is intentionally JSON pass-through; per-pass
    config schemas vary too widely to type uniformly here. *)
type pass_step = {
  pass : string;
  config : Yojson.Safe.t option;
}

type concurrency = {
  supports_cancellation : bool option;
  expected_latency_ms : int option;
  max_parallel_invocations : int option;
}

(** Top-level manifest. Field names match the JSON schema verbatim;
    OCaml-reserved-word collisions don't arise here. *)
type t = {
  manifest_version : string;
  adapter : string;
  adapter_version : string;
  backends_supported : string list option;
  logic_fragments : string list;
  type_constructions : string list;
  max_order : string;            (* "first_order" | "higher_order" *)
  tiers_produced : int list;
  trace_formats_produced : string list option;
  witness_kinds_produced : string list option;
  preferred_rewrite_pipeline : pass_step list option;
  concurrency : concurrency option;
}

(* --- field readers (private) ----------------------------------------- *)

let assoc j = match j with
  | `Assoc pairs -> pairs
  | _ -> raise (Codec.Decode_error ("expected object", j))

let str = function
  | `String s -> s
  | j -> raise (Codec.Decode_error ("expected string", j))

let int_of = function
  | `Int n -> n
  | j -> raise (Codec.Decode_error ("expected int", j))

let bool_of = function
  | `Bool b -> b
  | j -> raise (Codec.Decode_error ("expected bool", j))

let str_list = function
  | `List xs -> List.map str xs
  | j -> raise (Codec.Decode_error ("expected array of strings", j))

let int_list = function
  | `List xs -> List.map int_of xs
  | j -> raise (Codec.Decode_error ("expected array of ints", j))

let req k pairs : Yojson.Safe.t =
  try List.assoc k pairs
  with Not_found ->
    raise (Codec.Decode_error
             ("missing required field: " ^ k, `Assoc pairs))

let opt = List.assoc_opt

(* --- pass_step ------------------------------------------------------- *)

let pass_step_of_json (j : Yojson.Safe.t) : pass_step =
  let pairs = assoc j in
  {
    pass = str (req "pass" pairs);
    config = (match opt "config" pairs with
              | None -> None
              | Some c -> Some c);
  }

let pass_step_to_json (s : pass_step) : Yojson.Safe.t =
  let fields = [ "pass", `String s.pass ] in
  match s.config with
  | None -> `Assoc fields
  | Some c -> `Assoc (fields @ [ "config", c ])

(* --- concurrency ----------------------------------------------------- *)

let concurrency_of_json (j : Yojson.Safe.t) : concurrency =
  let pairs = assoc j in
  {
    supports_cancellation = Option.map bool_of (opt "supports_cancellation" pairs);
    expected_latency_ms = Option.map int_of (opt "expected_latency_ms" pairs);
    max_parallel_invocations =
      Option.map int_of (opt "max_parallel_invocations" pairs);
  }

let concurrency_to_json (c : concurrency) : Yojson.Safe.t =
  let f = [] in
  let f = match c.supports_cancellation with
    | None -> f
    | Some b -> f @ [ "supports_cancellation", `Bool b ]
  in
  let f = match c.expected_latency_ms with
    | None -> f
    | Some n -> f @ [ "expected_latency_ms", `Int n ]
  in
  let f = match c.max_parallel_invocations with
    | None -> f
    | Some n -> f @ [ "max_parallel_invocations", `Int n ]
  in
  `Assoc f

(* --- top-level codec ------------------------------------------------- *)

let of_json (j : Yojson.Safe.t) : t =
  let pairs = assoc j in
  {
    manifest_version = str (req "manifest_version" pairs);
    adapter = str (req "adapter" pairs);
    adapter_version = str (req "adapter_version" pairs);
    backends_supported = Option.map str_list (opt "backends_supported" pairs);
    logic_fragments = str_list (req "logic_fragments" pairs);
    type_constructions = str_list (req "type_constructions" pairs);
    max_order = str (req "max_order" pairs);
    tiers_produced = int_list (req "tiers_produced" pairs);
    trace_formats_produced =
      Option.map str_list (opt "trace_formats_produced" pairs);
    witness_kinds_produced =
      Option.map str_list (opt "witness_kinds_produced" pairs);
    preferred_rewrite_pipeline =
      (match opt "preferred_rewrite_pipeline" pairs with
       | None -> None
       | Some (`List xs) -> Some (List.map pass_step_of_json xs)
       | Some other ->
         raise (Codec.Decode_error
                  ("expected array at preferred_rewrite_pipeline", other)));
    concurrency =
      Option.map concurrency_of_json (opt "concurrency" pairs);
  }

let to_json (m : t) : Yojson.Safe.t =
  let f = [
    "manifest_version", `String m.manifest_version;
    "adapter", `String m.adapter;
    "adapter_version", `String m.adapter_version;
  ] in
  let f = match m.backends_supported with
    | None -> f
    | Some xs -> f @ [ "backends_supported",
                       `List (List.map (fun s -> `String s) xs) ]
  in
  let f = f @ [
    "logic_fragments",
    `List (List.map (fun s -> `String s) m.logic_fragments);
    "type_constructions",
    `List (List.map (fun s -> `String s) m.type_constructions);
    "max_order", `String m.max_order;
    "tiers_produced", `List (List.map (fun n -> `Int n) m.tiers_produced);
  ] in
  let f = match m.trace_formats_produced with
    | None -> f
    | Some xs -> f @ [ "trace_formats_produced",
                       `List (List.map (fun s -> `String s) xs) ]
  in
  let f = match m.witness_kinds_produced with
    | None -> f
    | Some xs -> f @ [ "witness_kinds_produced",
                       `List (List.map (fun s -> `String s) xs) ]
  in
  let f = match m.preferred_rewrite_pipeline with
    | None -> f
    | Some xs -> f @ [ "preferred_rewrite_pipeline",
                       `List (List.map pass_step_to_json xs) ]
  in
  let f = match m.concurrency with
    | None -> f
    | Some c -> f @ [ "concurrency", concurrency_to_json c ]
  in
  `Assoc f

(** Highest tier this manifest claims to produce. Empty
    [tiers_produced] (a malformed but representable manifest) is
    treated as [-1] so it sorts below every well-formed manifest. *)
let max_tier (m : t) : int =
  match m.tiers_produced with
  | [] -> -1
  | xs -> List.fold_left max min_int xs

(** Stable sort by [max_tier] descending: manifests that can mint
    higher-tier certs come first. Stability preserves the caller's
    input order within a tier — useful when a user has already
    encoded latency/policy preference among adapters at the same
    tier capability. The driver in [Dispatch] is preference-agnostic;
    callers that want a tier-preferring broker apply this first. *)
let sort_by_max_tier_descending (ms : t list) : t list =
  List.stable_sort
    (fun a b -> compare (max_tier b) (max_tier a))
    ms
