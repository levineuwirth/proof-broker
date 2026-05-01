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

The capability matcher (`match_adapters`) returns parallel arrays of
adapter names plus structured rejection reasons:

```json
{ "status": "ok",
  "payload": {
    "matches":    [ { "adapter": "cvc5" } ],
    "rejections": [ { "adapter": "vampire",
                      "reason": { "kind": "logic_out_of_fragment",
                                  "detail": "..." } } ]
  } }
```

The reason `kind` is a small enumeration (`match`, `order_too_high`,
`logic_out_of_fragment`, `type_construction_not_supported`); typed
Lean callers decode it into a sum type, raw callers can just inspect
the string. New reason kinds added on the OCaml side decode into a
forward-compat `otherReason` variant on the Lean side rather than
failing the envelope.

The certificate envelope verifier (`verify_certificate`) follows the
same `{ok, reason: {kind, detail?}}` pattern:

```json
{ "status": "ok",
  "payload": {
    "ok": true,
    "reason": { "kind": "verified_envelope" }
  } }
```

`reason.kind` covers two layers, gated on what `verify_certificate`
checked. The envelope layer's kinds are `verified_envelope`,
`hash_mismatch`, `tier_payload_mismatch`, `cert_version_mismatch`.
When envelope checks pass and the cert is Tier 1 / `farkas`, an
arithmetic Farkas verifier runs and the kind graduates to
`verified_farkas` (success) or one of the Farkas-specific failure
kinds: `farkas_unknown_hypothesis`, `farkas_nonlinear`,
`farkas_bad_coefficient`, `farkas_negative_coefficient`,
`farkas_not_contradictory`, `farkas_malformed_witness`. The verifier
dispatches on the IR's
`logic_classification.first_order_fragment`: `"LRA"` keeps strict
inequalities (`<`, `>`, `¬(≤)`) explicit and accepts a residual `≥
0` whenever a strict witness contributed positively; anything else
(including `"LIA"`) folds strictness into `≤` via the Z-only +1
trick and requires a strictly-positive residual. For Tiers
0/2/3 (and Tier 1 witness kinds beyond Farkas), the envelope check
passes through and the reason is `tier_check_deferred` /
`unsupported_witness_kind` — `ok` is `true` in those cases, signalling
"envelope verified, soundness not checked". Strict consumers should
gate on `reason.kind in {verified_envelope, verified_farkas}` rather
than `ok` alone. New reason kinds land in the Lean wrapper's
`otherCertReason` variant.

Inputs that need to carry more than just an IR — `run_pipeline`
(`{"ir": <Ir.t>, "config": <PipelineConfig>?}`), `match_adapters`
(`{"ir": <Ir.t>, "manifests": [<Manifest>, ...]}`),
`verify_certificate` (`{"cert": <Certificate>, "ir": <Ir.t>,
"trace": <Trace.t>?}`), `dispatch_to_adapter` (`{"adapter": "<name>",
"ir": <Ir.t>}`) — follow the same envelope-style convention on the
input side: an object with named fields, optional fields omitted
(never `null`).

**Adapter dispatch.** `dispatch_to_adapter` returns a two-shape
payload: on success `{"ok": true, "cert": <Certificate>}`, on adapter
failure `{"ok": false, "failure": {"kind": ..., "detail": ...}}`. The
distinction matters: a `Failed` outcome (sat returned, unknown
returned, solver crash, IR couldn't be serialized to SMT-LIB) is the
adapter doing its job and reporting an honest negative result, not a
plumbing error. Plumbing errors (input couldn't be parsed) still go
through the standard error envelope. Failure kinds: `sat_returned`,
`unknown_returned`, `timeout`, `solver_error`, `parse_error`,
`unsupported_ir`, `adapter_not_found`.

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

`type_metadata` and `definitional_metadata` are stored as JSON
pass-through in `Ir.t` (the wire form), but the OCaml side now carries
typed decoder modules — `Type_metadata` and `Definitional_metadata` —
that classify each entry into a typed variant on demand. Passes consume
the typed view (`find_quotient`, `find_defined_function`,
`find_lifted_to_quotient`, etc.) rather than field-fishing into the
JSON directly.

The wire form remains JSON because:
* unknown `kind` values round-trip losslessly through `OtherKind`
  variants — forward-compatible with schema extensions;
* the codec doesn't have to grow when a new kind is added;
* the Python validator continues to operate on the JSON form.

**Promotion criteria** (recorded so future authors know when to add
typed coverage for a new kind): a `kind` graduates from `OtherKind` to
its own variant when at least one OCaml-side consumer (a pass, an
adapter, a verifier component) needs to read its fields. Adding the
variant does not require a wire-format change.

The Lean side keeps `typeMetadata` / `definitionalMetadata` as
`Json` pass-through in `IR.lean` because no Lean-side consumer reads
their fields yet; when one appears, mirror the OCaml typed decoders
into Lean modules under the same names.

Adapter manifests follow the same stance: typed ADTs and capability-
matching logic live on the OCaml side (`Manifest`, `Capability_match`,
`Registry`); the Lean-side `runMatchAdapters` accepts manifests as
opaque `Json` values and only decodes the structured *response*
(matches/rejections + typed reason). When a Lean-side consumer needs
to read manifest fields directly (e.g., a Lean tactic that filters
manifests before submitting), graduate to a typed Lean `Manifest`
ADT then.

Certificates extend the same pattern: the OCaml-side `Certificate` /
`Refinement_record` ADTs carry the typed envelope and per-tier
discriminated payload; the Lean-side `runVerifyCertificate` accepts
certificates as `Json` and decodes only the structured verification
result. The graduation criterion holds — when a Lean tactic needs
to introspect cert fields (e.g., extract the goal for display),
mirror the typed ADT into Lean.

The Python `tools/check.py` validator remains authoritative for
schema-level rules (required fields, kind-discriminator legality,
cross-document references). The OCaml typed decoders silently drop
off-shape entries rather than reporting them; that's a deliberate
division of responsibility — the validator catches structural bugs,
the typed decoders give consumers structured access.

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
