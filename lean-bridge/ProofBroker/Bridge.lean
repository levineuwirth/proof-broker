/-
Lean-side surface for the Phase-0 FFI spike.

`pbRoundtripIr` ships a JSON-encoded IR document through the OCaml
codec and back, returning the FFI envelope as a JSON string. The
envelope shape is locked in `sdk/FFI_CONVENTIONS.md`.
-/

namespace ProofBroker

/-- Round-trip a JSON IR document through OCaml's `Codec.of_json`
    and `Codec.to_json`. Returns the FFI envelope JSON:

      `{"status":"ok","payload":...}`           on success
      `{"status":"error","error":{"kind":...}}` on failure

    Three possible `kind` values today:
    * `"json_parse_error"` — input not lexically JSON
    * `"decode_error"`     — JSON, but not a well-typed IR
    * `"shim_failure"`     — C shim itself failed (allocator, etc.) -/
@[extern "pb_lean_roundtrip_ir"]
opaque pbRoundtripIr (input : @& String) : String

end ProofBroker
