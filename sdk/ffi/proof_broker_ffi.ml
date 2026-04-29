(** OCaml entry point for the C shim (Phase-0 FFI spike).

    Registers callbacks that the C shim looks up via [caml_named_value].
    The OCaml runtime initializer ([caml_startup] on the C side) executes
    this module's top-level bindings, which is when the registrations land
    in the runtime's named-value table.

    Wire format and envelope shape are locked in [sdk/FFI_CONVENTIONS.md]:
    every entry point returns a JSON object of one of two shapes,
      {"status": "ok",    "payload": ...}
      {"status": "error", "error":   {"kind": ..., "message": ..., ...}}
    even when the underlying OCaml type is single-valued. *)

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

let () = Callback.register "pb_roundtrip_ir" roundtrip_ir
