/*
 * glue.c — Lean ↔ C ABI adapter for the proof_broker FFI boundary.
 *
 * Translates Lean's lean_object* String calling convention to the plain
 * (const char *, char **) ABI of proof_broker_shim.h. Owns the runtime
 * initialization (idempotent in the shim) and the malloc'd buffer
 * lifecycle: copies the shim's output into a Lean string, then frees the
 * shim's buffer before returning.
 *
 * One Lean extern: `pb_lean_call`, mirroring the OCaml dispatcher's
 * single C entry point. New ops do not require new glue functions.
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
#include <pthread.h>

/* Mirrors sdk/ffi/proof_broker_shim.h. Kept in lockstep manually —
 * if either signature drifts, the linker's still happy but behavior
 * breaks at runtime, so treat changes there as coupled. */
extern int  pb_ffi_init(char **argv);
extern int  pb_ffi_call(const char *method, const char *json_input, char **out);
extern void pb_ffi_free(char *p);

/* Audit M5: Lean elaboration can run on multiple worker threads
 * (snapshot parallelism), so first-call init must be race-free, and
 * pb_ffi_init's return code must not be discarded — running against
 * an uninitialized OCaml runtime would be far worse than a clean
 * failure. pthread_once serializes init; g_init_rc captures the
 * shim's status for ensure_inited's caller to act on. */
static pthread_once_t g_init_once = PTHREAD_ONCE_INIT;
static int g_init_rc = 0;

static void glue_init_once(void) {
    static char arg0[] = "proof_broker_lean";
    char *argv[] = { arg0, NULL };
    g_init_rc = pb_ffi_init(argv);
}

static int ensure_inited(void) {
    pthread_once(&g_init_once, glue_init_once);
    return g_init_rc;
}

/* Synthetic envelope returned when the shim itself fails (rc != 0).
 * Kept separate from the OCaml-produced envelopes so the kind tag
 * makes it obvious the failure is below the OCaml dispatcher. */
static lean_obj_res mk_shim_failure_envelope(int rc) {
    char buf[128];
    int n = snprintf(buf, sizeof(buf),
        "{\"status\":\"error\",\"error\":{\"kind\":\"shim_failure\",\"message\":\"shim returned rc=%d\",\"rc\":%d}}",
        rc, rc);
    if (n < 0 || (size_t)n >= sizeof(buf)) {
        return lean_mk_string("{\"status\":\"error\",\"error\":{\"kind\":\"shim_failure\",\"message\":\"shim failed\"}}");
    }
    return lean_mk_string(buf);
}

LEAN_EXPORT lean_obj_res pb_lean_call(b_lean_obj_arg method_obj, b_lean_obj_arg input_obj) {
    int init_rc = ensure_inited();
    if (init_rc != 0) {
        /* Fail closed: surface the init failure as a shim_failure
         * envelope (the tactic then throws) rather than calling into
         * an uninitialized runtime. */
        return mk_shim_failure_envelope(init_rc);
    }

    /* lean_string_cstr returns a NUL-terminated UTF-8 buffer owned by
     * the Lean object; valid for the duration of this call. */
    const char *method = lean_string_cstr(method_obj);
    const char *input  = lean_string_cstr(input_obj);

    char *out = NULL;
    int rc = pb_ffi_call(method, input, &out);
    if (rc != 0 || out == NULL) {
        return mk_shim_failure_envelope(rc);
    }

    lean_obj_res result = lean_mk_string(out);
    pb_ffi_free(out);
    return result;
}
