/*
 * proof_broker_shim.c — bridge from C ABI to the OCaml dispatcher.
 *
 * Discipline:
 *   - CAMLparam/CAMLlocal/CAMLreturn around any OCaml allocation
 *     (caml_copy_string, caml_callback2_exn). String reads (String_val,
 *     caml_string_length) before the next allocation are safe without
 *     re-rooting because the value is held in a CAMLlocal slot.
 *   - caml_named_value returns a stable GC root, no rooting needed.
 *   - The result string is copied into a malloc'd buffer before any
 *     allocation that could move the OCaml string, then handed off to C.
 *
 * Domain-lock discipline (OCaml 5 + multi-threaded callers like Lean):
 *   pb_ffi_init releases the runtime-system lock after caml_startup so
 *   that subsequent pb_ffi_call invocations on any C thread (including
 *   the one that did the init) start from a "lock not held" state. Each
 *   pb_ffi_call registers its calling thread with the OCaml runtime
 *   (idempotent — caml_c_thread_register tolerates re-registration),
 *   acquires the lock for the duration of the OCaml call, and releases
 *   on exit. Without this, a Lean elaborator that scheduled
 *   `#print axioms` or another kernel-traversing command on a worker
 *   thread different from the one that did caml_startup would trip
 *   the OCaml runtime's "no domain lock held" assertion when it
 *   reached one of our caml_*_string / caml_callback2_exn calls.
 */

#include "proof_broker_shim.h"

#include <stdlib.h>
#include <string.h>

#define CAML_NAME_SPACE
#include <caml/alloc.h>
#include <caml/callback.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>
#include <caml/threads.h>

static int g_initialized = 0;

int pb_ffi_init(char **argv) {
    if (g_initialized) return 0;
    /* dune's (modes shared_object) emits a .so whose entry point is
     * caml_startup; calling it from any thread that wants to invoke
     * OCaml callbacks runs all module initializers, including the
     * Callback.register call in proof_broker_ffi.ml. caml_startup
     * leaves the calling thread holding the runtime-system lock; we
     * release it here so subsequent pb_ffi_call invocations on any
     * thread can acquire/release on a consistent footing. */
    caml_startup(argv);
    g_initialized = 1;
    caml_release_runtime_system();
    return 0;
}

/* Acquire-then-call wrapper around the OCaml dispatch closure. Split
 * out from pb_ffi_call so the lock acquire/release lives in one place
 * and the OCaml-touching body uses CAMLparam/CAMLreturnT cleanly with a
 * single return path. */
static int pb_ffi_call_locked(const char *method, const char *json_input,
                              char **out) {
    static const value *closure = NULL;
    if (closure == NULL) {
        closure = caml_named_value("pb_dispatch_call");
        if (closure == NULL) return -2;
    }

    CAMLparam0();
    CAMLlocal3(v_method, v_input, v_out);

    v_method = caml_copy_string(method);
    v_input = caml_copy_string(json_input);
    v_out = caml_callback2_exn(*closure, v_method, v_input);
    if (Is_exception_result(v_out)) {
        CAMLreturnT(int, -3);
    }

    mlsize_t len = caml_string_length(v_out);
    char *buf = (char *)malloc(len + 1);
    if (!buf) CAMLreturnT(int, -4);
    memcpy(buf, String_val(v_out), len);
    buf[len] = '\0';

    *out = buf;
    CAMLreturnT(int, 0);
}

int pb_ffi_call(const char *method, const char *json_input, char **out) {
    if (!method || !json_input || !out) return -1;

    /* Register the calling C thread with the OCaml runtime if it isn't
     * already registered. caml_c_thread_register returns 1 on first
     * registration and ignores re-registrations, so calling it on every
     * invocation costs at most a thread-local lookup. The lock is NOT
     * held on return; we acquire it explicitly below. */
    caml_c_thread_register();
    caml_acquire_runtime_system();
    int rc = pb_ffi_call_locked(method, json_input, out);
    caml_release_runtime_system();
    return rc;
}

void pb_ffi_free(char *p) {
    free(p);
}
