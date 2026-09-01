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

(** Concept tags the dispatch path always unfolds (spec §5.4): the
    dispatch default pipeline hands these to the definition-unfolding
    pass regardless of user directives, so a goal mentioning a symbol
    whose definitional metadata carries one of these tags is unfolded
    before any adapter sees it. [numeral_definition] (R3-M3) is the
    tag the Lean reifier stamps on a numeral-body constant's
    [defined_function] entry — a numeral def opaque to solvers is
    always unfolded for dispatch, and the bridge inverts the unfold
    in the lifted term. Mirrors
    [registry/patterns-v1.json].always_unfold_for_dispatch — the
    PIN markers let tools/check.py verify the two lists agree. *)
(* PIN:always-unfold-for-dispatch *)
let always_unfold_for_dispatch : string list = [
  "function_composition";
  "function_identity";
  "function_application";
  "numeral_definition";
]
(* ENDPIN:always-unfold-for-dispatch *)

(** The pipeline [Dispatch.run] / [Dispatch.run_parallel] execute on
    every dispatch (R2): [default_config]'s two passes, with the
    definition-unfolding step configured from the registry's
    [always_unfold_for_dispatch] list rather than from user
    directives (spec §5.4). User directives still add on top — the
    pass unions its step config with the IR's
    [enable_definition_unfolding] list. *)
let default_dispatch_config : config = {
  default_config with
  pipeline = [
    { pass = "propositional_simplification"; config = None };
    { pass = "definition_unfolding";
      config = Some (`Assoc [
        "concepts",
        `List (List.map (fun s -> `String s) always_unfold_for_dispatch);
      ]) };
  ];
}

(** The empty pipeline: no passes. Its trace is the identity trace
    over the input IR (zero entries, initial = final hash). Direct
    adapter callers that bypass [Dispatch.run] (unit tests) use it
    to obtain an honest [rewrite_trace_hash] for the exact IR they
    dispatch. *)
let empty_config : config = {
  pipeline = [];
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
    pass module; nothing else in this file needs to change. Each pass
    receives its [pass_step.config] (R2: previously carried but
    ignored); passes without step-level configuration ignore it. *)
let registry : (string, Yojson.Safe.t option -> Ir.t -> pass_result) Hashtbl.t =
  Hashtbl.create 8

let register_pass (name : string)
    (run : Yojson.Safe.t option -> Ir.t -> pass_result) : unit =
  Hashtbl.replace registry name run

(** Read the ["concepts"] string list out of a definition-unfolding
    step config. Absent field / non-list shapes decode to []; a
    non-string element is a config error surfaced as
    [Codec.Decode_error] (the pipeline driver converts it to a
    [Failed] entry). *)
let concepts_of_step_config (c : Yojson.Safe.t option) : string list =
  match c with
  | Some (`Assoc pairs) ->
    (match List.assoc_opt "concepts" pairs with
     | Some (`List xs) ->
       List.map (function
         | `String s -> s
         | other ->
           raise (Codec.Decode_error ("expected string in concepts", other)))
         xs
     | _ -> [])
  | _ -> []

let () =
  register_pass "propositional_simplification"
    (fun _config ir ->
      let r = Propositional_simplify.run ir in
      { ir = r.ir; entry = r.trace });
  register_pass "definition_unfolding"
    (fun config ir ->
      let r =
        Definition_unfolding.run
          ~concepts:(concepts_of_step_config config) ir
      in
      { ir = r.ir; entry = r.trace });
  register_pass "quotient_elimination"
    (fun _config ir ->
      let r = Quotient_elimination.run ir in
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

(** Build a synthetic [Failed] entry for a pass that lied about its
    own input or output hash. The pipeline computes the "true"
    before/after independently from [Codec.to_json] and compares
    against what the pass reported in its [Trace.entry]; a mismatch
    means the pass module's bookkeeping disagrees with the actual
    IR it consumed or produced, which would otherwise corrupt the
    [before_hash[i+1] = after_hash[i]] chain invariant. We replace
    the pass's entry with a [Failed] entry pinned to the real
    [before_hash] and revert to the pre-pass IR — same contract as
    [failed_entry] for an exception. *)
let hash_mismatch_entry
    ~pass_name ~before_hash
    ~(reported : Trace.entry)
    ~actual_after_hash : Trace.entry =
  let detail =
    if not (String.equal reported.before_hash before_hash) then
      Printf.sprintf
        "pass reported before_hash=%s but pipeline computed %s"
        reported.before_hash before_hash
    else
      Printf.sprintf
        "pass reported after_hash=%s but pipeline computed %s"
        reported.after_hash actual_after_hash
  in
  {
    pass = pass_name;
    version = reported.version;
    before_hash;
    after_hash = before_hash;
    configuration = reported.configuration;
    outcome = Some Failed;
    inversion_data = None;
    diagnostics = Some ("pass hash mismatch: " ^ detail);
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
             let r = pass_run step.config ir in
             let actual_after = Hash.sha256_of_json (Codec.to_json r.ir) in
             let before_ok = String.equal r.entry.before_hash before_hash in
             let after_ok = String.equal r.entry.after_hash actual_after in
             if before_ok && after_ok then r.entry, r.ir
             else
               (* Pass's bookkeeping disagrees with the actual IR.
                  Discard the pass's output and surface a Failed
                  entry so the chain invariant stays intact. *)
               hash_mismatch_entry ~pass_name:step.pass ~before_hash
                 ~reported:r.entry ~actual_after_hash:actual_after,
               ir
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

(** [identity_trace ir]: the [empty_config] pipeline's trace over
    [ir] — the honest "this IR was dispatched exactly as given"
    trace for direct-adapter callers. *)
let identity_trace (ir : Ir.t) : Trace.t = snd (run empty_config ir)

(** Canonical hash of [identity_trace ir] — the [rewrite_trace_hash]
    a direct-adapter caller passes to [Adapter.dispatch]. *)
let identity_trace_hash (ir : Ir.t) : string =
  Hash.canonical_sha256 (Trace.to_json (identity_trace ir))
