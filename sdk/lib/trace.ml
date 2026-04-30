(** Rewrite trace types matching [schemas/v1.0/rewrite-trace.schema.json].

    A [TraceEntry] records one IR-to-IR pass invocation: which pass,
    its version, the before/after content hashes (computed via
    [Hash.sha256_of_json]), the outcome, and pass-specific
    [inversion_data] sufficient for the lifting layer to invert the
    rewrite without consulting the source proof state.

    [Trace.t] (this module) aggregates entries across a pipeline
    invocation, plus the pipeline configuration and the initial/final
    IR hashes that bracket the rewrite chain. *)

type outcome =
  | Applied
  | Skipped_preconditions
  | No_op
  | Failed
(** Mirrors the [outcome] enum in the schema. *)

let outcome_to_string = function
  | Applied -> "applied"
  | Skipped_preconditions -> "skipped_preconditions"
  | No_op -> "no_op"
  | Failed -> "failed"

let outcome_of_string = function
  | "applied" -> Applied
  | "skipped_preconditions" -> Skipped_preconditions
  | "no_op" -> No_op
  | "failed" -> Failed
  | other -> raise (Codec.Decode_error
                      ("unknown outcome: " ^ other, `String other))

type entry = {
  pass : string;
  version : string;
  before_hash : string;
  after_hash : string;
  configuration : Yojson.Safe.t option;
  outcome : outcome option;
  inversion_data : Yojson.Safe.t option;
  diagnostics : string option;
}
(** A single trace entry. [configuration] and [inversion_data] are
    pass-specific JSON; the schema deliberately leaves them
    [additionalProperties: true]. The Python validator and Lean
    replayer both inspect them per-pass. *)

let entry_to_json (e : entry) : Yojson.Safe.t =
  let fields = [
    "pass", `String e.pass;
    "version", `String e.version;
    "before_hash", `String e.before_hash;
    "after_hash", `String e.after_hash;
  ] in
  let fields = match e.configuration with
    | None -> fields
    | Some c -> fields @ [ "configuration", c ]
  in
  let fields = match e.outcome with
    | None -> fields
    | Some o -> fields @ [ "outcome", `String (outcome_to_string o) ]
  in
  let fields = match e.inversion_data with
    | None -> fields
    | Some d -> fields @ [ "inversion_data", d ]
  in
  let fields = match e.diagnostics with
    | None -> fields
    | Some s -> fields @ [ "diagnostics", `String s ]
  in
  `Assoc fields

let entry_of_json (j : Yojson.Safe.t) : entry =
  let p = match j with
    | `Assoc pairs -> pairs
    | _ -> raise (Codec.Decode_error ("expected object", j))
  in
  let str_field k = match List.assoc k p with
    | `String s -> s
    | other -> raise (Codec.Decode_error ("expected string at " ^ k, other))
    | exception Not_found ->
      raise (Codec.Decode_error ("missing field: " ^ k, j))
  in
  {
    pass = str_field "pass";
    version = str_field "version";
    before_hash = str_field "before_hash";
    after_hash = str_field "after_hash";
    configuration = List.assoc_opt "configuration" p;
    outcome = (match List.assoc_opt "outcome" p with
               | None -> None
               | Some (`String s) -> Some (outcome_of_string s)
               | Some other -> raise (Codec.Decode_error
                                        ("expected string at outcome", other)));
    inversion_data = List.assoc_opt "inversion_data" p;
    diagnostics = (match List.assoc_opt "diagnostics" p with
                   | None -> None
                   | Some (`String s) -> Some s
                   | Some other -> raise (Codec.Decode_error
                                            ("expected string at diagnostics", other)));
  }

(** Pipeline-level trace document (spec v1.0 §5.6, schema
    [schemas/v1.0/rewrite-trace.schema.json]). Aggregates the entries
    produced by [Pipeline.run] together with the pipeline configuration
    actually used and the initial/final IR hashes. *)
type t = {
  trace_version : string;
  initial_ir_hash : string;
  final_ir_hash : string;
  entries : entry list;
  configuration : Yojson.Safe.t option;
}

let to_json (tr : t) : Yojson.Safe.t =
  let fields = [
    "trace_version", `String tr.trace_version;
    "initial_ir_hash", `String tr.initial_ir_hash;
    "final_ir_hash", `String tr.final_ir_hash;
    "entries", `List (List.map entry_to_json tr.entries);
  ] in
  let fields = match tr.configuration with
    | None -> fields
    | Some c -> fields @ [ "configuration", c ]
  in
  `Assoc fields

let of_json (j : Yojson.Safe.t) : t =
  let p = match j with
    | `Assoc pairs -> pairs
    | _ -> raise (Codec.Decode_error ("expected object", j))
  in
  let str_field k = match List.assoc k p with
    | `String s -> s
    | other -> raise (Codec.Decode_error ("expected string at " ^ k, other))
    | exception Not_found ->
      raise (Codec.Decode_error ("missing field: " ^ k, j))
  in
  let entries = match List.assoc "entries" p with
    | `List xs -> List.map entry_of_json xs
    | other -> raise (Codec.Decode_error ("expected array at entries", other))
    | exception Not_found ->
      raise (Codec.Decode_error ("missing field: entries", j))
  in
  {
    trace_version = str_field "trace_version";
    initial_ir_hash = str_field "initial_ir_hash";
    final_ir_hash = str_field "final_ir_hash";
    entries;
    configuration = List.assoc_opt "configuration" p;
  }
