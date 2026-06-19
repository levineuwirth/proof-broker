"""Canonical JSON hash — Python mirror of `sdk/lib/codec.ml`'s
`canonical_bytes` + `sdk/lib/hash.ml`'s `canonical_sha256`.

This module is the Python side of the locked v1 cross-document hash
invariants. It MUST produce byte-identical output to the OCaml side
on every input the v1 schemas can express. Cross-tested by
`tests/cross_canonical/` on every CI run; see the OCaml docstring
in `Codec.canonical_bytes` for the full format specification.

Format pinned (do not change without bumping cert/IR schema versions):

  - Recursive key sort of every object — `sorted(d.keys())` on every
    nested dict. On valid UTF-8 strings this agrees byte-for-byte
    with OCaml's `String.compare` because UTF-8 preserves
    lexicographic order.
  - Serialization via `json.dumps` with:
      * `ensure_ascii=False`  — emit non-ASCII as raw UTF-8 bytes,
        matching `Yojson.Safe.to_string`'s default (NOT `\\uXXXX`).
      * `separators=(",", ":")`  — no whitespace anywhere.
      * `sort_keys=True`  — redundant given the explicit
        canonicalization below, but a belt-and-suspenders guard
        against `json.dumps`'s implementation re-emitting in input
        order somehow.

No floats appear in any v1 canonical input (IR, trace, manifest); only
ints, strings, bools, null, lists, objects. Float-formatting drift
between Yojson and Python is structurally avoided.
"""
from __future__ import annotations

import hashlib
import json
from typing import Any


def _canonicalize(obj: Any) -> Any:
    """Return `obj` with every nested dict's keys sorted (byte-wise).

    Lists, scalars are returned unchanged structurally — but each
    list element is canonicalized recursively. Strings, ints, bools,
    None pass through.
    """
    if isinstance(obj, dict):
        return {k: _canonicalize(obj[k]) for k in sorted(obj.keys())}
    if isinstance(obj, list):
        return [_canonicalize(x) for x in obj]
    return obj


def canonical_bytes(obj: Any) -> bytes:
    """The locked v1 canonical bytestream — mirror of OCaml
    `Codec.canonical_bytes`.

    Returns UTF-8 bytes (not a str) because the OCaml side hashes
    over bytes and platform encoding assumptions must not creep in.
    """
    canon = _canonicalize(obj)
    s = json.dumps(
        canon,
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    )
    return s.encode("utf-8")


def canonical_sha256(obj: Any) -> str:
    """SHA-256 of `canonical_bytes(obj)` in the schema-compliant
    `"sha256:<64hex>"` form — mirror of OCaml `Hash.canonical_sha256`.
    """
    return "sha256:" + hashlib.sha256(canonical_bytes(obj)).hexdigest()
