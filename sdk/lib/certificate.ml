(** Certificate envelope (spec v1.0 §6, schema
    [schemas/v1.0/certificate.schema.json]).

    A certificate is what an adapter returns on successful dispatch.
    The envelope is uniform across tiers; the [payload] field is
    discriminated by [tier]:
      0 — Oracle (trust-only)
      1 — Witness (audited check)
      2 — Lemma list / reconstruction hint
      3 — Proof trace (strategy stack)
      4 — Reserved (not implemented in v1)

    The codec does shape parsing, not soundness checking. Soundness
    is the verifier's job; see [Verifier]. The Python validator
    ([tools/check.py]) remains authoritative for schema-level
    rules (the if/then payload-shape conditional, etc.); the OCaml
    codec parses any document that has the required fields and
    leaves stricter checks to consumers.

    Forward-compat: Tier-1 [Witness_other_kind] and the [Tier4_reserved]
    variant carry raw JSON so future schema additions round-trip
    losslessly. New tier numbers beyond 4 raise [Decode_error] —
    the schema enumerates 0..4 and any value outside is a
    structural error. *)

(** Tier-1 witness sub-discriminator. *)
type witness_kind =
  | Farkas
  | Sat_assignment
  | Sat_unsat_core
  | Polynomial_positivstellensatz
  | Witness_other_kind of string

let witness_kind_to_string = function
  | Farkas -> "farkas"
  | Sat_assignment -> "sat_assignment"
  | Sat_unsat_core -> "sat_unsat_core"
  | Polynomial_positivstellensatz -> "polynomial_positivstellensatz"
  | Witness_other_kind s -> s

let witness_kind_of_string = function
  | "farkas" -> Farkas
  | "sat_assignment" -> Sat_assignment
  | "sat_unsat_core" -> Sat_unsat_core
  | "polynomial_positivstellensatz" -> Polynomial_positivstellensatz
  | s -> Witness_other_kind s

(** Per-tier payload. The codec discriminates on the cert's [tier]
    and parses the payload according to that field's value;
    tier/payload mismatches are a [Verifier] concern, not a codec
    concern — the codec accepts any well-shaped payload that fits
    the declared tier. *)
type payload =
  | Tier0_oracle of {
      claim : string;          (* always "proved" per schema *)
      backend_attestation : string option;
    }
  | Tier1_witness of {
      witness_kind : witness_kind;
      witness_data : Yojson.Safe.t;   (* discriminated by witness_kind;
                                         pass-through here, the real
                                         arithmetic check lives elsewhere *)
      checking_recipe : string;
    }
  | Tier2_lemma_list of {
      lemmas_used : Yojson.Safe.t list;
      strategy_hint : string;
      structural_hint : Yojson.Safe.t option;
    }
  | Tier3_proof_trace of {
      trace_format : string;
      trace_data : Yojson.Safe.t;
      trace_dialect_features : string list option;
      trace_annotations : string option;
    }
  | Tier4_reserved of Yojson.Safe.t   (* spec marks this reserved; we
                                         pass through without claiming
                                         to interpret *)

type backend = {
  name : string;
  version : string;
  config_hash : string;
}

type resources = {
  wall_time_ms : int;
  memory_peak_kb : int;
  budget_consumed : float option;
}

type t = {
  cert_version : string;          (* always "1.0" *)
  tier : int;
  format : string;
  goal : Ir.goal;
  dispatch_context_hash : string;
  rewrite_trace_hash : string;
  backend : backend;
  resources : resources;
  refinement_record : Refinement_record.t;
  payload : payload;
}

(* --- codec primitives ------------------------------------------------ *)

let assoc j = match j with
  | `Assoc pairs -> pairs
  | _ -> raise (Codec.Decode_error ("expected object", j))

let str = function
  | `String s -> s
  | j -> raise (Codec.Decode_error ("expected string", j))

let int_of = function
  | `Int n -> n
  | j -> raise (Codec.Decode_error ("expected int", j))

let float_of = function
  | `Float f -> f
  | `Int n -> float_of_int n
  | j -> raise (Codec.Decode_error ("expected number", j))

let str_list = function
  | `List xs -> List.map str xs
  | j -> raise (Codec.Decode_error ("expected array of strings", j))

let req k pairs : Yojson.Safe.t =
  try List.assoc k pairs
  with Not_found ->
    raise (Codec.Decode_error
             ("missing required field: " ^ k, `Assoc pairs))

let opt = List.assoc_opt

(* --- backend / resources --------------------------------------------- *)

let backend_of_json (j : Yojson.Safe.t) : backend =
  let pairs = assoc j in
  {
    name = str (req "name" pairs);
    version = str (req "version" pairs);
    config_hash = str (req "config_hash" pairs);
  }

let backend_to_json (b : backend) : Yojson.Safe.t =
  `Assoc [
    "name", `String b.name;
    "version", `String b.version;
    "config_hash", `String b.config_hash;
  ]

let resources_of_json (j : Yojson.Safe.t) : resources =
  let pairs = assoc j in
  {
    wall_time_ms = int_of (req "wall_time_ms" pairs);
    memory_peak_kb = int_of (req "memory_peak_kb" pairs);
    budget_consumed = Option.map float_of (opt "budget_consumed" pairs);
  }

let resources_to_json (r : resources) : Yojson.Safe.t =
  let f = [
    "wall_time_ms", `Int r.wall_time_ms;
    "memory_peak_kb", `Int r.memory_peak_kb;
  ] in
  let f = match r.budget_consumed with
    | None -> f
    | Some b -> f @ [ "budget_consumed", `Float b ]
  in
  `Assoc f

(* --- payload --------------------------------------------------------- *)

let payload_of_json ~(tier : int) (j : Yojson.Safe.t) : payload =
  let pairs = assoc j in
  match tier with
  | 0 ->
    Tier0_oracle {
      claim = str (req "claim" pairs);
      backend_attestation = Option.map str (opt "backend_attestation" pairs);
    }
  | 1 ->
    Tier1_witness {
      witness_kind = witness_kind_of_string (str (req "witness_kind" pairs));
      witness_data = req "witness_data" pairs;
      checking_recipe = str (req "checking_recipe" pairs);
    }
  | 2 ->
    let lemmas = match req "lemmas_used" pairs with
      | `List xs -> xs
      | other ->
        raise (Codec.Decode_error ("expected array at lemmas_used", other))
    in
    Tier2_lemma_list {
      lemmas_used = lemmas;
      strategy_hint = str (req "strategy_hint" pairs);
      structural_hint = opt "structural_hint" pairs;
    }
  | 3 ->
    Tier3_proof_trace {
      trace_format = str (req "trace_format" pairs);
      trace_data = req "trace_data" pairs;
      trace_dialect_features =
        Option.map str_list (opt "trace_dialect_features" pairs);
      trace_annotations = Option.map str (opt "trace_annotations" pairs);
    }
  | 4 -> Tier4_reserved j
  | n ->
    raise (Codec.Decode_error
             (Printf.sprintf "unsupported tier: %d (must be 0-4)" n, j))

let payload_to_json (p : payload) : Yojson.Safe.t =
  match p with
  | Tier0_oracle { claim; backend_attestation } ->
    let f = [ "claim", `String claim ] in
    (match backend_attestation with
     | None -> `Assoc f
     | Some s -> `Assoc (f @ [ "backend_attestation", `String s ]))
  | Tier1_witness { witness_kind; witness_data; checking_recipe } ->
    `Assoc [
      "witness_kind", `String (witness_kind_to_string witness_kind);
      "witness_data", witness_data;
      "checking_recipe", `String checking_recipe;
    ]
  | Tier2_lemma_list { lemmas_used; strategy_hint; structural_hint } ->
    let f = [
      "lemmas_used", `List lemmas_used;
      "strategy_hint", `String strategy_hint;
    ] in
    (match structural_hint with
     | None -> `Assoc f
     | Some s -> `Assoc (f @ [ "structural_hint", s ]))
  | Tier3_proof_trace { trace_format; trace_data; trace_dialect_features;
                        trace_annotations } ->
    let f = [
      "trace_format", `String trace_format;
      "trace_data", trace_data;
    ] in
    let f = match trace_dialect_features with
      | None -> f
      | Some xs ->
        f @ [ "trace_dialect_features",
              `List (List.map (fun s -> `String s) xs) ]
    in
    let f = match trace_annotations with
      | None -> f
      | Some s -> f @ [ "trace_annotations", `String s ]
    in
    `Assoc f
  | Tier4_reserved j -> j

(* --- top-level ------------------------------------------------------- *)

let of_json (j : Yojson.Safe.t) : t =
  let pairs = assoc j in
  let tier = int_of (req "tier" pairs) in
  {
    cert_version = str (req "cert_version" pairs);
    tier;
    format = str (req "format" pairs);
    goal = Codec.goal_of_json (req "goal" pairs);
    dispatch_context_hash = str (req "dispatch_context_hash" pairs);
    rewrite_trace_hash = str (req "rewrite_trace_hash" pairs);
    backend = backend_of_json (req "backend" pairs);
    resources = resources_of_json (req "resources" pairs);
    refinement_record =
      Refinement_record.of_json (req "refinement_record" pairs);
    payload = payload_of_json ~tier (req "payload" pairs);
  }

let to_json (c : t) : Yojson.Safe.t =
  `Assoc [
    "cert_version", `String c.cert_version;
    "tier", `Int c.tier;
    "format", `String c.format;
    "goal", Codec.goal_to_json c.goal;
    "dispatch_context_hash", `String c.dispatch_context_hash;
    "rewrite_trace_hash", `String c.rewrite_trace_hash;
    "backend", backend_to_json c.backend;
    "resources", resources_to_json c.resources;
    "refinement_record", Refinement_record.to_json c.refinement_record;
    "payload", payload_to_json c.payload;
  ]

(** Tier of a payload, regardless of envelope tier. Used by the
    verifier to detect tier/payload mismatches. *)
let payload_tier = function
  | Tier0_oracle _ -> 0
  | Tier1_witness _ -> 1
  | Tier2_lemma_list _ -> 2
  | Tier3_proof_trace _ -> 3
  | Tier4_reserved _ -> 4
