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

(* ---- dispatcher -------------------------------------------------- *)

let dispatch (method_name : string) (input : string) : string =
  match Hashtbl.find_opt registry method_name with
  | Some handler -> handler input
  | None ->
    envelope_error ~kind:"unknown_method" ~message:method_name []

let () =
  register_method "roundtrip_ir" roundtrip_ir;
  Callback.register "pb_dispatch_call" dispatch
