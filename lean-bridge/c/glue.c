/*
 * glue.c — Lean ↔ C ABI adapter for the Phase-0 FFI spike.
 *
 * Translates Lean's lean_object* String calling convention to the plain
 * (const char *, char **) ABI of proof_broker_shim.h. Owns the runtime
 * initialization (idempotent in the shim) and the malloc'd buffer
 * lifecycle: copies the shim's output into a Lean string, then frees the
 * shim's buffer before returning.
 *
 * Forward-declares the shim prototypes inline rather than including
 * proof_broker_shim.h so that Lake's compile invocation only needs
 * Lean's include path. The shim's C symbols resolve at link time
 * against the dune-built proof_broker_ffi.so.
 */

#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Mirrors sdk/ffi/proof_broker_shim.h. Kept in lockstep manually for
 * the Phase-0 spike — if either signature drifts, the linker's still
 * happy but behavior breaks at runtime, so treat changes there as
 * coupled. */
extern int  pb_ffi_init(char **argv);
extern int  pb_ffi_roundtrip_ir(const char *input, char **out);
extern void pb_ffi_free(char *p);

static int g_inited = 0;

static void ensure_inited(void) {
    if (g_inited) return;
    static char arg0[] = "proof_broker_lean";
    char *argv[] = { arg0, NULL };
    pb_ffi_init(argv);
    g_inited = 1;
}

/* Synthetic envelope returned when the shim itself fails (rc != 0).
 * Kept separate from the OCaml-produced envelopes so the kind tag
 * makes it obvious the failure is below the OCaml callback. */
static lean_obj_res mk_shim_failure_envelope(int rc) {
    char buf[128];
    int n = snprintf(buf, sizeof(buf),
        "{\"status\":\"error\",\"error\":{\"kind\":\"shim_failure\",\"rc\":%d}}",
        rc);
    if (n < 0 || (size_t)n >= sizeof(buf)) {
        return lean_mk_string("{\"status\":\"error\",\"error\":{\"kind\":\"shim_failure\"}}");
    }
    return lean_mk_string(buf);
}

LEAN_EXPORT lean_obj_res pb_lean_roundtrip_ir(b_lean_obj_arg input_obj) {
    ensure_inited();

    /* lean_string_cstr returns a NUL-terminated UTF-8 buffer owned by
     * the Lean object; valid for the duration of this call. */
    const char *input = lean_string_cstr(input_obj);

    char *out = NULL;
    int rc = pb_ffi_roundtrip_ir(input, &out);
    if (rc != 0 || out == NULL) {
        return mk_shim_failure_envelope(rc);
    }

    lean_obj_res result = lean_mk_string(out);
    pb_ffi_free(out);
    return result;
}
