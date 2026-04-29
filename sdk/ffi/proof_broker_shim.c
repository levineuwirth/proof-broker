/*
 * proof_broker_shim.c — bridge from C ABI to registered OCaml callbacks.
 *
 * Discipline:
 *   - CAMLparam/CAMLlocal/CAMLreturn around any OCaml allocation
 *     (caml_copy_string, caml_callback_exn). String reads (String_val,
 *     caml_string_length) before the next allocation are safe without
 *     re-rooting because the value is held in a CAMLlocal slot.
 *   - caml_named_value returns a stable GC root, no rooting needed.
 *   - The result string is copied into a malloc'd buffer before any
 *     allocation that could move the OCaml string, then handed off to C.
 */

#include "proof_broker_shim.h"

#include <stdlib.h>
#include <string.h>

#define CAML_NAME_SPACE
#include <caml/alloc.h>
#include <caml/callback.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

static int g_initialized = 0;

int pb_ffi_init(char **argv) {
    if (g_initialized) return 0;
    /* dune's (modes shared_object) emits a .so whose entry point is
     * caml_startup; calling it from any thread that wants to invoke
     * OCaml callbacks runs all module initializers, including the
     * Callback.register calls in proof_broker_ffi.ml. */
    caml_startup(argv);
    g_initialized = 1;
    return 0;
}

int pb_ffi_roundtrip_ir(const char *input, char **out) {
    if (!input || !out) return -1;

    static const value *closure = NULL;
    if (closure == NULL) {
        closure = caml_named_value("pb_roundtrip_ir");
        if (closure == NULL) return -2;
    }

    CAMLparam0();
    CAMLlocal2(v_in, v_out);

    v_in = caml_copy_string(input);
    v_out = caml_callback_exn(*closure, v_in);
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

void pb_ffi_free(char *p) {
    free(p);
}
