(** Content-addressable hashing for IR documents and trace fragments.

    The wire format is "sha256:<64 lowercase hex chars>" matching the
    schema's [ContentHash] regex. Hashes are computed over a normalized
    JSON serialization (recursive key sort, see [Codec.normalize]) so
    the digest is stable across map-iteration orders on either side
    of the FFI. *)

(** [sha256_of_string s] computes the SHA-256 of [s] and renders it
    as the schema-compliant ["sha256:..."] string. *)
let sha256_of_string (s : string) : string =
  let hex = Digestif.SHA256.(to_hex (digest_string s)) in
  "sha256:" ^ hex

(** [canonical_sha256 j] is THE locked v1 canonical hash of a JSON
    document — the function the cross-document hash invariants
    (cert.dispatch_context_hash, rewrite_trace_hash, config_hash)
    are computed by, and the function [tools/canonical_hash.py]
    mirrors byte-for-byte. See [Codec.canonical_bytes] for the
    bytestream specification. *)
let canonical_sha256 (j : Yojson.Safe.t) : string =
  sha256_of_string (Codec.canonical_bytes j)

(** Legacy name retained for existing call sites — identical to
    [canonical_sha256]. New code should call [canonical_sha256]
    directly. *)
let sha256_of_json = canonical_sha256
