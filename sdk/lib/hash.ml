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

(** [sha256_of_json j] normalizes [j] (recursive key sort) before
    hashing, so semantically-equal JSON documents that differ only in
    key order produce the same hash. This is the canonical
    content-hash function used by the rewriter to populate
    [before_hash] and [after_hash] in trace entries. *)
let sha256_of_json (j : Yojson.Safe.t) : string =
  sha256_of_string (Yojson.Safe.to_string (Codec.normalize j))
