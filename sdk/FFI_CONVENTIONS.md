# FFI conventions

Locked decisions for the OCaml ↔ C ↔ Lean boundary. Source for the
Phase-0 FFI spike (delta.md §2.1) and downstream Phase 1+ work.

## Wire format

JSON during FFI bring-up; CBOR later, behind a single
`Codec.to_wire` / `Codec.of_wire` toggle. JSON is debuggable and
inspectable — eyes on the wire is irreplaceable while the shim itself is
under development. The codec abstracts the choice so that the switch-over
to CBOR is a single point of change once the shim is stable.

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

Rationale: typed-error home; no FFI out-params; adding new return fields
is non-breaking. Adding a new error `kind` is also non-breaking provided
the Lean side treats unknown `kind` as a generic failure.

Do not return bare values from any shim entry point. Even one-result
functions wrap in `{"status": "ok", "payload": <result>}` so the calling
convention is uniform across the boundary.

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

- The exact set of shim entry points. The Phase-0 spike will start with
  one (round-trip a single IR document) and grow incrementally.
- Whether the shim is stateful (holding e.g. a parsed registry) or
  stateless (each call re-loads). Decision belongs to whoever writes
  the shim; constraints from this document apply either way.
- The Lean-side error type that `{"status": "error", ...}` envelopes
  decode into. Probably an inductive matching this document's `kind`
  values, with a catch-all for forward compatibility.
