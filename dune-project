(lang dune 3.21)
(name proof_broker)
(generate_opam_files true)

; The new (using rocq …) extension is announced but unimplemented as of
; dune 3.22; staying on the deprecated (using coq …) until the rename
; ships. Suppresses the deprecated_coq_lang warning so our build is
; quiet — the warning otherwise fires on every build.
(using coq 0.8)
(warnings (deprecated_coq_lang disabled))

(package
 (name proof_broker)
 (synopsis "Proof Broker SDK shared library (OCaml)")
 (description "OCaml implementation of the Proof Broker SDK per spec v1.0. Hosts the IR rewriter, certificate verifier core, dispatcher, and cache. The Rocq plugin links this library directly; the Lean plugin invokes it via a C-FFI shim with serialized-data marshaling.")
 (depends
  (ocaml (>= 5.0))
  dune
  (yojson (>= 3.0))
  (digestif (>= 1.0))
  (zarith (>= 1.13))
  (alcotest :with-test)))

(package
 (name proof_broker_rocq)
 (synopsis "Proof Broker Rocq plugin (Phase 4 architectural probe)")
 (description "Rocq plugin that direct-links the proof_broker OCaml library — no FFI, no JSON marshaling. Reifies LIA goals from Constr into the IR, dispatches through the broker, prints the verified cert. The point is to test whether the IR is genuinely cross-system or accidentally Lean-shaped (delta.md §1.1).")
 (depends
  (ocaml (>= 5.0))
  dune
  proof_broker
  (rocq-runtime (>= 9.0))))
