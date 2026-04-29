/*
 * test_shim.c — C-side smoke test for the OCaml↔C boundary.
 *
 * Exercises five properties of proof_broker_shim:
 *   T1  Happy path: round-trip a real IR fixture via the "roundtrip_ir"
 *       method and observe a status=ok envelope whose payload preserves
 *       at least the ir_version marker. Structural equality is the Lean
 *       side's job (parse-and-compare per sdk/FFI_CONVENTIONS.md); here
 *       we just confirm the bytes flow.
 *   T2  Lexical garbage triggers status=error / kind=json_parse_error.
 *   T3  Well-formed JSON missing required IR fields triggers
 *       status=error / kind=decode_error (Codec.of_json's domain).
 *   T4  100k round-trips of T1's input under a single runtime, asserting
 *       neither the OCaml GC nor our malloc/free discipline has a leak
 *       or a use-after-free that surfaces as a crash. Memory growth is
 *       meant to be checked externally (e.g., with `time` / RSS sampling
 *       in the CI invocation); here we just need the loop to complete.
 *   T5  Calling an unregistered method surfaces as an
 *       envelope with kind="unknown_method" and the method name in
 *       message — the dispatcher's only synthetic envelope, and the
 *       reason the C ABI's first argument is a method string at all.
 */

#include "../proof_broker_shim.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static char *slurp(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror(path); exit(2); }
    if (fseek(f, 0, SEEK_END) != 0) { perror("fseek"); exit(2); }
    long sz = ftell(f);
    if (sz < 0) { perror("ftell"); exit(2); }
    rewind(f);
    char *buf = (char *)malloc((size_t)sz + 1);
    if (!buf) { fprintf(stderr, "OOM slurping %s\n", path); exit(2); }
    if (fread(buf, 1, (size_t)sz, f) != (size_t)sz) {
        fprintf(stderr, "short read on %s\n", path);
        exit(2);
    }
    buf[sz] = '\0';
    fclose(f);
    return buf;
}

static void must_contain(const char *haystack, const char *needle, const char *what) {
    if (strstr(haystack, needle) == NULL) {
        fprintf(stderr, "FAIL %s: missing substring %s in:\n%s\n", what, needle, haystack);
        exit(1);
    }
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: %s <example.json>\n", argv[0]);
        return 2;
    }

    char *runtime_argv[] = { (char *)"proof_broker_ffi", NULL };
    pb_ffi_init(runtime_argv);

    /* ---- T1: round-trip a real IR fixture --------------------------- */
    char *input = slurp(argv[1]);
    char *out = NULL;
    int rc = pb_ffi_call("roundtrip_ir", input, &out);
    if (rc != 0) {
        fprintf(stderr, "T1 pb_ffi_call rc=%d\n", rc);
        return 1;
    }
    must_contain(out, "\"status\":\"ok\"",       "T1 status");
    must_contain(out, "\"payload\":",            "T1 payload");
    must_contain(out, "\"ir_version\":\"1.0\"",  "T1 ir_version preserved");
    pb_ffi_free(out);
    free(input);
    fprintf(stderr, "OK T1: round-trip envelope is status=ok with payload\n");

    /* ---- T2: lexical garbage -> json_parse_error -------------------- */
    out = NULL;
    rc = pb_ffi_call("roundtrip_ir", "{not json", &out);
    if (rc != 0) {
        fprintf(stderr, "T2 pb_ffi_call rc=%d\n", rc);
        return 1;
    }
    must_contain(out, "\"status\":\"error\"",          "T2 status");
    must_contain(out, "\"kind\":\"json_parse_error\"", "T2 kind");
    pb_ffi_free(out);
    fprintf(stderr, "OK T2: lexical garbage yields status=error/json_parse_error\n");

    /* ---- T3: missing IR fields -> decode_error ---------------------- */
    out = NULL;
    rc = pb_ffi_call("roundtrip_ir", "{\"foo\":42}", &out);
    if (rc != 0) {
        fprintf(stderr, "T3 pb_ffi_call rc=%d\n", rc);
        return 1;
    }
    must_contain(out, "\"status\":\"error\"",      "T3 status");
    must_contain(out, "\"kind\":\"decode_error\"", "T3 kind");
    pb_ffi_free(out);
    fprintf(stderr, "OK T3: missing fields yield status=error/decode_error\n");

    /* ---- T4: GC + alloc-discipline stress --------------------------- */
    input = slurp(argv[1]);
    const int N = 100000;
    for (int i = 0; i < N; ++i) {
        out = NULL;
        rc = pb_ffi_call("roundtrip_ir", input, &out);
        if (rc != 0) {
            fprintf(stderr, "T4 iter=%d rc=%d\n", i, rc);
            return 1;
        }
        pb_ffi_free(out);
    }
    free(input);
    fprintf(stderr, "OK T4: %d round-trips completed cleanly\n", N);

    /* ---- T5: unknown method -> kind=unknown_method ------------------ */
    out = NULL;
    rc = pb_ffi_call("does_not_exist", "{}", &out);
    if (rc != 0) {
        fprintf(stderr, "T5 pb_ffi_call rc=%d\n", rc);
        return 1;
    }
    must_contain(out, "\"status\":\"error\"",          "T5 status");
    must_contain(out, "\"kind\":\"unknown_method\"",   "T5 kind");
    must_contain(out, "\"message\":\"does_not_exist\"", "T5 message echoes method");
    pb_ffi_free(out);
    fprintf(stderr, "OK T5: unknown method yields status=error/unknown_method\n");

    return 0;
}
