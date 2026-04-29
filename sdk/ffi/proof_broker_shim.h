/*
 * proof_broker_shim.h — C ABI for the proof_broker FFI boundary.
 *
 * One entry point ever: pb_ffi_call dispatches to a method named in
 * its first argument. New OCaml-side operations land by registering
 * a fresh method name in proof_broker_ffi.ml; the C ABI does not grow
 * with the OCaml API. Rationale, error-kind taxonomy, and envelope
 * shape are locked in sdk/FFI_CONVENTIONS.md.
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
 * Dispatch a method call through the OCaml dispatcher.
 *
 * method      : NUL-terminated UTF-8 method name (e.g. "roundtrip_ir").
 * json_input  : NUL-terminated UTF-8 JSON string carrying the method's
 *               input. The handler decides the schema; the dispatcher
 *               does not look at it.
 * out         : on return, set to a malloc'd NUL-terminated UTF-8 JSON
 *               string carrying the FFI envelope. Caller must release
 *               with pb_ffi_free. Set even on logical errors — those
 *               surface as {"status":"error", ...} envelopes with a
 *               typed kind.
 *
 * Return codes:
 *    0  dispatch succeeded; *out holds the envelope.
 *   -1  bad arguments (NULL method, json_input, or out).
 *   -2  callback table not initialized (pb_ffi_init was not called, or
 *       OCaml runtime did not register pb_dispatch_call).
 *   -3  OCaml dispatcher escaped its try/with and raised an unhandled
 *       exception. Should never happen if proof_broker_ffi.ml is
 *       well-formed; report as a bug.
 *   -4  out-of-memory while copying the result.
 *
 * Unknown methods are not rc=-1; they surface as normal envelopes with
 * kind="unknown_method", per FFI_CONVENTIONS.md.
 */
int pb_ffi_call(const char *method, const char *json_input, char **out);

/* Release a buffer produced by a pb_ffi_* call. NULL is allowed. */
void pb_ffi_free(char *p);

#ifdef __cplusplus
}
#endif

#endif /* PROOF_BROKER_SHIM_H */
