/*
 * proof_broker_shim.h — C ABI for the Phase-0 FFI spike.
 *
 * Stable C surface that downstream callers (Lean via @[extern], C tests,
 * eventually a Rocq probe via direct linkage) bind to. Internals delegate
 * to OCaml callbacks registered in proof_broker_ffi.ml.
 *
 * Envelope shape, multi-return convention, and parse-and-compare protocol
 * live in sdk/FFI_CONVENTIONS.md.
 */

#ifndef PROOF_BROKER_SHIM_H
#define PROOF_BROKER_SHIM_H

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Initialize the OCaml runtime. Must be called once before any other
 * pb_ffi_* entry point. Idempotent: subsequent calls are no-ops.
 *
 * argv: NULL-terminated argv-style array. May be a synthetic value such
 *       as { "proof_broker_ffi", NULL }; the OCaml runtime only inspects
 *       it to populate Sys.argv.
 *
 * Returns 0 on success.
 */
int pb_ffi_init(char **argv);

/*
 * Round-trip an IR document through OCaml's Codec.of_json / Codec.to_json.
 *
 * input : NUL-terminated UTF-8 JSON string carrying an IR document.
 * out   : on return, set to a malloc'd NUL-terminated UTF-8 JSON string
 *         carrying the FFI envelope. Caller must release with pb_ffi_free.
 *         Set even on logical (decode) errors — those surface as
 *         {"status":"error", "error":{"kind":"decode_error", ...}}.
 *
 * Return codes:
 *    0  marshaling succeeded; *out holds the envelope.
 *   -1  bad arguments (NULL input or out).
 *   -2  callback table not initialized (pb_ffi_init was not called, or
 *       OCaml runtime did not register the named value).
 *   -3  OCaml callback escaped its try/with and raised an unhandled
 *       exception. Should never happen if proof_broker_ffi.ml is
 *       well-formed; report as a bug.
 *   -4  out-of-memory while copying the result.
 */
int pb_ffi_roundtrip_ir(const char *input, char **out);

/* Release a buffer produced by a pb_ffi_* call. NULL is allowed. */
void pb_ffi_free(char *p);

#ifdef __cplusplus
}
#endif

#endif /* PROOF_BROKER_SHIM_H */
