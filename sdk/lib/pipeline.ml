(** Rewrite-pipeline composition (spec v1.0 §5.3 / §5.4).

    Threads an [Ir.t] through a sequence of named passes, accumulating
    a [Trace.t] whose [entries] is one trace entry per attempted pass.
    Each entry's [before_hash] equals the previous entry's [after_hash]
    (and [initial_ir_hash] equals [entries.[0].before_hash]) so the
    chain is locally verifiable.

    Failure handling. A pass can fail in two ways:
      * [Trace.outcome = Failed] returned from the pass itself
        (currently no v1 pass exposes this directly), or
      * an OCaml exception escapes the pass; this module catches it,
        synthesizes a [Failed] entry with [diagnostics] from the
        exception, and continues or aborts per [stop_on_failure].
    A pass that returns [Skipped_preconditions] or [No_op] is *not* a
    failure: its entry is appended and the pipeline continues
    regardless of [stop_on_failure].

    Timeouts. [timeout_per_pass_ms] is parsed and stored on the trace's
    [configuration] field but is not enforced in v1. Enforcement
    requires Unix signals / a worker thread; deferred. Documented as a
    known limitation rather than silently ignored — the field is
    preserved on round-trips so callers configuring a timeout do not
    lose the value. *)

type pass_step = {
  pass : string;
  config : Yojson.Safe.t option;
}

type config = {
  pipeline : pass_step list;
  stop_on_failure : bool;
  timeout_per_pass_ms : int option;
}

(** Default pipeline (spec v1.0 §5.4): propositional simplification
    followed by definition unfolding. No quotient/prenex/Skolemization
    by default; adapters that want them opt in via their preferences. *)
let default_config : config = {
  pipeline = [
    { pass = "propositional_simplification"; config = None };
    { pass = "definition_unfolding"; config = None };
  ];
  stop_on_failure = false;
  timeout_per_pass_ms = None;
}

(* --- pass registry ---------------------------------------------------- *)

(** Each pass yields the rewritten IR and the trace entry it produced.
    The pipeline trusts the pass's [before_hash] / [after_hash] /
    [outcome]: those are the pass's report on its own work, not
    re-computed here. *)
type pass_result = {
  ir : Ir.t;
  entry : Trace.entry;
}

(** Pipeline-recognized pass names. Adding a new pass to the pipeline
    is one line here plus the [Trace.entry]-producing function in the
    pass module; nothing else in this file needs to change. *)
let registry : (string, Ir.t -> pass_result) Hashtbl.t = Hashtbl.create 8

let register_pass (name : string) (run : Ir.t -> pass_result) : unit =
  Hashtbl.replace registry name run

let () =
  register_pass "propositional_simplification"
    (fun ir ->
      let r = Propositional_simplify.run ir in
      { ir = r.ir; entry = r.trace });
  register_pass "definition_unfolding"
    (fun ir ->
      let r = Definition_unfolding.run ir in
      { ir = r.ir; entry = r.trace })

(* --- config codec ----------------------------------------------------- *)

let pass_step_to_json (s : pass_step) : Yojson.Safe.t =
  let fields = [ "pass", `String s.pass ] in
  match s.config with
  | None -> `Assoc fields
  | Some c -> `Assoc (fields @ [ "config", c ])

let pass_step_of_json (j : Yojson.Safe.t) : pass_step =
  match j with
  | `Assoc pairs ->
    let pass = match List.assoc "pass" pairs with
      | `String s -> s
      | other -> raise (Codec.Decode_error ("expected string at pass", other))
      | exception Not_found ->
        raise (Codec.Decode_error ("missing field: pass", j))
    in
    let config = List.assoc_opt "config" pairs in
    { pass; config }
  | _ -> raise (Codec.Decode_error ("expected object", j))

let config_to_json (c : config) : Yojson.Safe.t =
  let fields = [
    "pipeline", `List (List.map pass_step_to_json c.pipeline);
    "stop_on_failure", `Bool c.stop_on_failure;
  ] in
  let fields = match c.timeout_per_pass_ms with
    | None -> fields
    | Some t -> fields @ [ "timeout_per_pass_ms", `Int t ]
  in
  `Assoc fields

let config_of_json (j : Yojson.Safe.t) : config =
  match j with
  | `Assoc pairs ->
    let pipeline = match List.assoc_opt "pipeline" pairs with
      | None -> default_config.pipeline
      | Some (`List xs) -> List.map pass_step_of_json xs
      | Some other ->
        raise (Codec.Decode_error ("expected array at pipeline", other))
    in
    let stop_on_failure = match List.assoc_opt "stop_on_failure" pairs with
      | None -> default_config.stop_on_failure
      | Some (`Bool b) -> b
      | Some other ->
        raise (Codec.Decode_error ("expected bool at stop_on_failure", other))
    in
    let timeout_per_pass_ms = match List.assoc_opt "timeout_per_pass_ms" pairs with
      | None -> None
      | Some (`Int n) -> Some n
      | Some other ->
        raise (Codec.Decode_error ("expected int at timeout_per_pass_ms", other))
    in
    { pipeline; stop_on_failure; timeout_per_pass_ms }
  | _ -> raise (Codec.Decode_error ("expected object", j))

(* --- exception → Failed entry ----------------------------------------- *)

(** Build a synthetic [Failed] trace entry for an exception that
    escaped a pass. [before_hash] is the IR going in; [after_hash =
    before_hash] (the contract is that a Failed pass leaves the IR
    untouched). The exception message lands in [diagnostics] so the
    pipeline trace remains the only artifact a caller needs to
    diagnose the failure. *)
let failed_entry ~pass_name ~before_hash ~exn : Trace.entry =
  {
    pass = pass_name;
    version = "1.0";
    before_hash;
    after_hash = before_hash;
    configuration = None;
    outcome = Some Failed;
    inversion_data = None;
    diagnostics = Some (Printexc.to_string exn);
  }

let unknown_pass_entry ~pass_name ~before_hash : Trace.entry =
  {
    pass = pass_name;
    version = "1.0";
    before_hash;
    after_hash = before_hash;
    configuration = None;
    outcome = Some Failed;
    inversion_data = None;
    diagnostics = Some (Printf.sprintf "unknown pass: %s" pass_name);
  }

(* --- driver ----------------------------------------------------------- *)

(** Run [config.pipeline] against [ir]. Returns the final IR and a
    [Trace.t] document. Honors [stop_on_failure]: when a pass produces
    [outcome = Failed] (either intrinsically or via exception capture),
    if [stop_on_failure] the chain halts after appending the failed
    entry, otherwise the pipeline continues with the pre-failure IR. *)
let run (config : config) (ir : Ir.t) : Ir.t * Trace.t =
  let initial_ir_hash = Hash.sha256_of_json (Codec.to_json ir) in
  let rec loop ir entries_rev = function
    | [] -> ir, List.rev entries_rev
    | step :: rest ->
      let before_hash = Hash.sha256_of_json (Codec.to_json ir) in
      let entry, ir' =
        match Hashtbl.find_opt registry step.pass with
        | None ->
          unknown_pass_entry ~pass_name:step.pass ~before_hash, ir
        | Some pass_run ->
          (try
             let r = pass_run ir in
             r.entry, r.ir
           with exn ->
             failed_entry ~pass_name:step.pass ~before_hash ~exn, ir)
      in
      let entries_rev' = entry :: entries_rev in
      let failed = entry.outcome = Some Failed in
      if failed && config.stop_on_failure then
        ir', List.rev entries_rev'
      else
        loop ir' entries_rev' rest
  in
  let final_ir, entries = loop ir [] config.pipeline in
  let final_ir_hash = Hash.sha256_of_json (Codec.to_json final_ir) in
  let trace : Trace.t = {
    trace_version = "1.0";
    initial_ir_hash;
    final_ir_hash;
    entries;
    configuration = Some (config_to_json config);
  } in
  final_ir, trace
