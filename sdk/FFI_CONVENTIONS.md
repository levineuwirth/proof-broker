# FFI conventions

Locked decisions for the OCaml ↔ C ↔ Lean boundary. Source for the
Phase-0 FFI spike (delta.md §2.1) and downstream Phase 1+ work.

## Wire format

**JSON locked for v1.** CBOR sits behind a single
`Codec.to_wire` / `Codec.of_wire` toggle but does not get switched
on until profiling shows FFI marshaling at ≥10% of dispatch wall time
on representative workloads. Below that threshold, JSON's diagnostic
affordances — cat-able fixtures, readable CI logs, eyeball-debuggable
error envelopes — outweigh wire-size and parse-cost wins. The
Phase-0 spike measured ~54 µs/call, well below any plausible trigger.

The codec abstraction means the eventual switch is a single point of
change. The trigger is a measurable bar so the "should we move to
CBOR yet" discussion does not recur every six months.

The IR document is the canonical example; the same convention applies to
certificates, refinement records, traces, and every other artifact that
crosses the boundary.

## Multi-return envelope

Every shim entry point returns one JSON object of one of these shapes:

```json
{ "status": "ok", "payload": { ... } }
```

```json
{ "status": "error", "error": { "kind": "...", "message": "...", ... } }
```

Functions whose OCaml type is `A -> B * C` (e.g.
`quotient_elimination : Ir.t -> Ir.t * trace_entry`) carry both results
in `payload`:

```json
{ "status": "ok", "payload": { "ir": <Ir.t>, "trace_entry": <TraceEntry> } }
```

The pipeline driver (`run_pipeline`) uses the same shape with the
single-entry replaced by a full trace document under key `trace`:

```json
{ "status": "ok", "payload": { "ir": <Ir.t>, "trace": <Trace.Document> } }
```

Inputs that need to carry more than just an IR — currently
`run_pipeline`, which takes `{"ir": <Ir.t>, "config": <PipelineConfig>?}` —
follow the same envelope-style convention on the input side: an object
with named fields, optional fields omitted (never `null`).

Rationale: typed-error home; no FFI out-params; adding new return fields
is non-breaking. Adding a new error `kind` is also non-breaking provided
the Lean side treats unknown `kind` as a generic failure.

Do not return bare values from any shim entry point. Even one-result
functions wrap in `{"status": "ok", "payload": <result>}` so the calling
convention is uniform across the boundary.

**Forward compatibility.** Envelope consumers must access fields by
name (e.g., `Json.getObjVal? "payload"`), never by structurally
pattern-matching the whole object. New optional fields (`trace_entry`,
`metadata`, ...) can then be added to `payload` or `error` without
breaking existing decoders. The Lean-side decoder in
`lean-bridge/Main.lean` follows this convention; treat it as the
reference shape for any new envelope consumer.

## Method dispatch

One C ABI entry point ever:

```c
int pb_ffi_call(const char *method,
                const char *json_input,
                char **out);
```

Method names are strings carried in the first argument; payloads are
JSON in the second; the output buffer always carries the standard
envelope. New OCaml-side operations land by registering a callback
under a fresh method name and adding a typed Lean-side wrapper; the
C ABI does not grow with the OCaml API.

Rationale: per-method named C entry points (e.g.,
`pb_ffi_quotient_eliminate`, `pb_ffi_propositional_simplify`) become a
per-method tax — every new pass requires coordinated changes across
three files in two languages. The dispatcher trades C-level static
typing (which the C compiler cannot meaningfully enforce on
JSON-shaped payloads anyway) for an ABI that does not grow. The
Lean-side typed wrappers preserve everything a Lean caller actually
wants from typing:

```lean
namespace ProofBroker

-- pb_lean_call is the Lean-side C glue that adapts Lean's lean_object*
-- string ABI to the shim's plain-C `pb_ffi_call` ABI; see
-- lean-bridge/c/glue.c. The dispatcher rationale applies to the C
-- ABI underneath, not to this Lean-facing symbol.
@[extern "pb_lean_call"]
private opaque pbCall (method : @& String) (input : @& String) : String

def quotientEliminate (ir : IR) : Except FfiError IR := ...
def propositionalSimplify (ir : IR) : Except FfiError IR := ...

end ProofBroker
```

Each typed wrapper handles its own envelope decoding and error
propagation; callers see typed results plus a typed `FfiError`
inductive (one constructor per `kind` value, plus a forward-compat
`.other` catch-all), never the raw envelope. See
`lean-bridge/ProofBroker/Bridge.lean` for the reference shape.

**Unknown method.** If `method` is not registered on the OCaml side,
the dispatcher returns the standard error envelope with a distinct
`kind`:

```json
{
  "status": "error",
  "error": {
    "kind": "unknown_method",
    "message": "<method-name>"
  }
}
```

The distinct `kind` lets callers separate "method exists but rejected
the input" (`decode_error`, `validation_error`, ...) from "method not
in this build" (`unknown_method`); the latter typically signals SDK
↔ Lean-bridge version skew.

## Comparison protocol

Across the FFI, never byte-compare JSON. Lean and OCaml produce JSON
with different key orders; byte comparison fails on documents that are
semantically equal.

Both sides parse, normalize (recursive key sort), then compare. The
OCaml-side reference implementation is `Codec.normalize` in
`sdk/lib/codec.ml`. The Lean side will need an equivalent normalizer
when round-trip equality tests cross the boundary.

## Pass-through metadata

`type_metadata` and `definitional_metadata` are JSON pass-through in the
OCaml IR until proper ADTs land in Phase 1+. The codec round-trips them
faithfully because it does not look at the values.

**Do not add OCaml-side validation logic for these maps in the
meantime.** Any such logic would be rewritten when the ADTs arrive.
The Python `tools/check.py` validator is the single source of truth
for these maps until the ADTs land. When that migration happens, plan
to *move* validation rather than duplicate it across the two languages.

## Decode errors at the FFI boundary

`Codec.Decode_error (msg, j)` carries a string message and the offending
JSON value. The OCaml-side representation keeps `j` as a structured
`Yojson.Safe.t` for richer diagnostics inside OCaml. At the C-shim
boundary, render `j` to a string (with `Yojson.Safe.to_string`) and
populate the error envelope:

```json
{
  "status": "error",
  "error": {
    "kind": "decode_error",
    "message": "<msg>",
    "site": "<rendered j>"
  }
}
```

Rendering at the shim boundary (rather than at the raise site inside
OCaml) preserves the structured representation for any OCaml-internal
diagnostic path that later wants it.

## What's not yet decided

- Whether the shim is stateful (holding e.g. a parsed registry) or
  stateless (each call re-loads). Decision belongs to whoever writes
  the shim; constraints from this document apply either way.
- The Lean-side error type that `{"status": "error", ...}` envelopes
  decode into. Probably an inductive matching this document's `kind`
  values, with a catch-all for forward compatibility.

## Phase-0 spike outcome

The Phase-0 round-trip spike landed end-to-end. The full chain
(Lean → C glue → OCaml → C glue → Lean, with parse-and-compare
normalization at the Lean end) round-trips all three IR fixtures with
structural equality, and the error path surfaces decode failures as
typed `kind` values in the envelope.

Measured cost on x86-64 Linux, OCaml 5.4.1, Lean 4.30.0-rc2:

| Metric                              | Result                          |
|-------------------------------------|---------------------------------|
| Per-call cost (parse + decode + encode + serialize, small IR) | ~54 µs |
| RSS after warmup, held over 100k iterations                   | 5.7 MB stable, no growth |
| Decode-error propagation                                      | typed `kind="decode_error"` reaches Lean |
| JSON-parse-error propagation                                  | typed `kind="json_parse_error"` reaches Lean |

Implication for the §2.2 +20–30% Lean-plugin estimate (delta.md): the
band stays as standing estimate; Phase 0 came in at the low end of it.
The estimate's load-bearing concern was always boundary-design
durability across diverse ops — whether the FFI surface holds up as
new methods, new error kinds, and new envelope payloads land — not
the marshaling code volume itself. The marshaling code is small and
now front-loaded, so the meaningful Phase 1 recalibration happens at
mid-checkpoint, when we know what fraction of total Lean-plugin effort
the FFI machinery represents across a real distribution of ops.

The §5 condition-6 off-ramp does not trigger. The lone wrinkle (lld +
glibc; see Toolchain notes below) is operational rather than
architectural — a one-line link-flag tweak, not a packaging restructure.

### Toolchain notes

- Lean 4.30's bundled lld defaults to `--no-allow-shlib-undefined`,
  which rejects linking against `proof_broker_ffi.so`'s transitive
  glibc symbol references on systems where the lld bundles an older
  glibc than the system's libc was built against. The lake build
  passes `-Wl,--allow-shlib-undefined`; runtime resolution by the
  dynamic loader is unaffected. If a future Lean release ships a
  different bundled toolchain or this becomes a portability problem,
  revisit by either rebuilding the OCaml side against the older
  glibc or switching the Lean build to use the system toolchain.
- The shim is loaded via `$ORIGIN`-relative rpath in the Lean
  executable so the test self-resolves the `.so` without
  `LD_LIBRARY_PATH`. Production distribution will need a different
  story (per §2.1 distribution-bundle scaffold), but for development
  this keeps the layout obvious.
