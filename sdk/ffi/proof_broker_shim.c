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
#include <pthread.h>

#define CAML_NAME_SPACE
#include <caml/alloc.h>
#include <caml/callback.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>
#include <caml/threads.h>

/* Audit M5: init must be idempotent AND thread-safe. The previous
 * `if (g_initialized) return 0;` over a plain int was a data race —
 * two Lean worker threads racing the first FFI call could both pass
 * the check and call caml_startup twice (undefined behavior) and
 * double-release the runtime lock. pthread_once runs the init body
 * exactly once with full happens-before to every caller, regardless
 * of how many threads race in. g_argv is the argv for caml_startup;
 * the sole in-tree caller (lean-bridge/c/glue.c) always passes the
 * same constant argv, and only the first call's value is consumed,
 * so publishing it before pthread_once is safe. */
static pthread_once_t g_init_once = PTHREAD_ONCE_INIT;
static char **g_argv = NULL;
static int g_initialized = 0;

static void pb_ffi_init_once(void) {
    /* dune's (modes shared_object) emits a .so whose entry point is
     * caml_startup; it runs all module initializers, including the
     * Callback.register in proof_broker_ffi.ml, and returns holding
     * the runtime-system lock. We release it so subsequent
     * pb_ffi_call invocations on any thread acquire/release on a
     * consistent footing. */
    caml_startup(g_argv);
    caml_release_runtime_system();
    g_initialized = 1;
}

int pb_ffi_init(char **argv) {
    g_argv = argv;
    pthread_once(&g_init_once, pb_ffi_init_once);
    /* g_initialized is written inside the once-routine, which
     * happens-before pthread_once returns on every thread. A zero
     * here means caml_startup did not complete (it normally aborts
     * the process on failure rather than returning, so this is a
     * defensive signal, not the common path). */
    return g_initialized ? 0 : -5;
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
