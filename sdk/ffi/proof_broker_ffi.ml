(** OCaml entry point for the C shim — generic dispatcher.

    Registers a single callback ["pb_dispatch_call"] that the C shim looks
    up via [caml_named_value]. Method-specific handlers live in a private
    registry populated at module-load; new ops land by adding a
    [register_method] call at the bottom of this file. The C ABI
    (one [pb_ffi_call] entry point) does not grow with the OCaml API.

    Wire format and envelope shape are locked in [sdk/FFI_CONVENTIONS.md]:
    every dispatch returns a JSON object of one of two shapes,
      {"status": "ok",    "payload": ...}
      {"status": "error", "error":   {"kind": ..., "message": ..., ...}}
    even when the underlying OCaml type is single-valued. Per-method
    handlers own their own success and error envelopes; the dispatcher
    only synthesizes the [unknown_method] envelope. *)

open Yojson.Safe

let envelope_ok payload =
  to_string (`Assoc [ "status", `String "ok"; "payload", payload ])

let envelope_error ~kind ~message extra =
  to_string
    (`Assoc
      [
        "status", `String "error";
        "error", `Assoc ([ "kind", `String kind; "message", `String message ] @ extra);
      ])

(* Read-only after module init: the registry is populated once at the
   bottom of this file and then only read by the dispatcher. No
   concurrency hazards; re-loading on every dispatch would be silly. *)
let registry : (string, string -> string) Hashtbl.t = Hashtbl.create 16

let register_method (name : string) (handler : string -> string) : unit =
  Hashtbl.replace registry name handler

(* ---- handlers ---------------------------------------------------- *)

let roundtrip_ir (input : string) : string =
  try
    let j = from_string input in
    let ir = Proof_broker.Codec.of_json j in
    envelope_ok (Proof_broker.Codec.to_json ir)
  with
  | Proof_broker.Codec.Decode_error (msg, j) ->
    envelope_error ~kind:"decode_error" ~message:msg
      [ "site", `String (to_string j) ]
  | Yojson.Json_error msg ->
    envelope_error ~kind:"json_parse_error" ~message:msg []

(* Multi-return envelope: [propositional_simplify : Ir.t -> Ir.t *
   trace_entry] carries both results in [payload] under named keys
   per [sdk/FFI_CONVENTIONS.md] §Multi-return envelope. *)
let propositional_simplify (input : string) : string =
  try
    let j = from_string input in
    let ir = Proof_broker.Codec.of_json j in
    let result = Proof_broker.Propositional_simplify.run ir in
    let payload = `Assoc [
      "ir", Proof_broker.Codec.to_json result.ir;
      "trace_entry", Proof_broker.Trace.entry_to_json result.trace;
    ] in
    envelope_ok payload
  with
  | Proof_broker.Codec.Decode_error (msg, j) ->
    envelope_error ~kind:"decode_error" ~message:msg
      [ "site", `String (to_string j) ]
  | Yojson.Json_error msg ->
    envelope_error ~kind:"json_parse_error" ~message:msg []

(* Same multi-return envelope shape as [propositional_simplify].
   Configuration is read from the IR's [user_directives.
   rewriter_preferences.enable_definition_unfolding] field rather
   than passed as a separate dispatcher arg. *)
let definition_unfolding (input : string) : string =
  try
    let j = from_string input in
    let ir = Proof_broker.Codec.of_json j in
    let result = Proof_broker.Definition_unfolding.run ir in
    let payload = `Assoc [
      "ir", Proof_broker.Codec.to_json result.ir;
      "trace_entry", Proof_broker.Trace.entry_to_json result.trace;
    ] in
    envelope_ok payload
  with
  | Proof_broker.Codec.Decode_error (msg, j) ->
    envelope_error ~kind:"decode_error" ~message:msg
      [ "site", `String (to_string j) ]
  | Yojson.Json_error msg ->
    envelope_error ~kind:"json_parse_error" ~message:msg []

(* [run_pipeline] takes a wrapped input of shape
     {"ir": <IR>, "config": <PipelineConfig>?}
   so the IR and the pipeline config travel together through the
   single string slot the dispatcher exposes. Missing [config] falls
   back to [Pipeline.default_config] (spec §5.4). The payload mirrors
   the multi-return shape of the per-pass methods, with the
   single-entry [trace_entry] replaced by the pipeline-level
   [Trace.t] document under key [trace]. *)
let run_pipeline (input : string) : string =
  try
    let j = from_string input in
    let pairs = match j with
      | `Assoc p -> p
      | _ -> raise (Proof_broker.Codec.Decode_error ("expected object", j))
    in
    let ir_json = match List.assoc_opt "ir" pairs with
      | Some v -> v
      | None ->
        raise (Proof_broker.Codec.Decode_error ("missing field: ir", j))
    in
    let ir = Proof_broker.Codec.of_json ir_json in
    let config = match List.assoc_opt "config" pairs with
      | None -> Proof_broker.Pipeline.default_config
      | Some c -> Proof_broker.Pipeline.config_of_json c
    in
    let final_ir, trace = Proof_broker.Pipeline.run config ir in
    let payload = `Assoc [
      "ir", Proof_broker.Codec.to_json final_ir;
      "trace", Proof_broker.Trace.to_json trace;
    ] in
    envelope_ok payload
  with
  | Proof_broker.Codec.Decode_error (msg, j) ->
    envelope_error ~kind:"decode_error" ~message:msg
      [ "site", `String (to_string j) ]
  | Yojson.Json_error msg ->
    envelope_error ~kind:"json_parse_error" ~message:msg []

(* ---- dispatcher -------------------------------------------------- *)

let dispatch (method_name : string) (input : string) : string =
  match Hashtbl.find_opt registry method_name with
  | Some handler -> handler input
  | None ->
    envelope_error ~kind:"unknown_method" ~message:method_name []

let () =
  register_method "roundtrip_ir" roundtrip_ir;
  register_method "propositional_simplify" propositional_simplify;
  register_method "definition_unfolding" definition_unfolding;
  register_method "run_pipeline" run_pipeline;
  Callback.register "pb_dispatch_call" dispatch
