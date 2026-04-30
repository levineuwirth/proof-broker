(** Rewrite trace types matching [schemas/v1.0/rewrite-trace.schema.json].

    A [TraceEntry] records one IR-to-IR pass invocation: which pass,
    its version, the before/after content hashes (computed via
    [Hash.sha256_of_json]), the outcome, and pass-specific
    [inversion_data] sufficient for the lifting layer to invert the
    rewrite without consulting the source proof state.

    [Trace.t] (the full document) is not yet defined here — the
    rewriter currently produces single entries per FFI call and the
    pipeline-level trace document is assembled later. The single-entry
    type is the load-bearing one for §2.1's multi-return envelope. *)

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
