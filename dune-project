(lang dune 3.21)
(name proof_broker)
(generate_opam_files true)

; Rocq/Coq build extension. dune 3.24 (2026-06-21) DELETED `(using coq …)`
; from the dune language and only `(using rocq 0.11)` parses there — but
; every published rocq-runtime (<= 9.2.0) declares `dune {>= "3.8" & <
; "3.24"}` (`opam show rocq-runtime.9.2.0`), so a dune-3.24 workspace
; cannot host the Rocq bridge at all. Hence the `(dune (< 3.24))` pin in
; every package's depends below (the lower bound comes from `(lang dune
; 3.21)`), staying on `(using coq 0.8)`, and suppressing the
; deprecated_coq_lang warning that otherwise fires on every build.
; WATCH(rocq-dune-3.24): when a rocq-runtime release lifts the `< 3.24`
; bound, migrate to `(lang dune 3.24)` + `(using rocq 0.11)` and drop the
; pin here AND in .github/workflows/validate.yml (the `dune<3.24` opam
; install lines). Tracked in the roadmap decide-list.
(using coq 0.8)
(warnings (deprecated_coq_lang disabled))

(package
 (name proof_broker)
 (synopsis "Proof Broker SDK shared library (OCaml)")
 (description "OCaml implementation of the Proof Broker SDK per spec v1.0. Hosts the IR rewriter, certificate verifier core, dispatcher, and cache. The Rocq plugin links this library directly; the Lean plugin invokes it via a C-FFI shim with serialized-data marshaling.")
 (depends
  (ocaml (>= 5.0))
  (dune (< 3.24))
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
  (dune (< 3.24))
  proof_broker
  ; rocq-runtime is the base runtime library (Constr, EConstr, Proofview
  ; et al.) — it's what the plugin code links against. The `coqc` binary
  ; (still expected by dune's `(using coq 0.8)` extension) lives in
  ; coq-core, a separate compat package that wraps rocq's renamed
  ; binary. coq-stdlib provides the Stdlib theory the plugin's .v files
  ; depend on (rocq-bridge/theories/dune has `(theories Stdlib)`); it
  ; also makes `coqc --config` succeed, which dune calls during build.
  ; All three are required at build time.
  ; Upper bound < 9.2: rocq-runtime 9.2.0 changed the signature of
  ; `Assumptions.assumptions` (now `... -> GlobRef.t list ->
  ; ContextObjectMap.t`; 9.1 took an owner GlobRef + a Constr.t), which
  ; breaks the audit-H1 axiom-footprint gate call in
  ; rocq-bridge/src/llm_replay.ml. Adapting that call is a soundness-
  ; gate change and gets its own reviewed PR; until then CI and local
  ; builds resolve the 9.1.1 stack that was green on 2026-06-19.
  ; WATCH(rocq-9.2-assumptions-api): lift the bound together with the
  ; llm_replay.ml migration (roadmap decide-list).
  (rocq-runtime (and (>= 9.0) (< 9.2)))
  (coq-core (and (>= 9.0) (< 9.2)))
  (coq-stdlib (and (>= 9.0) (< 9.2)))))

(package
 (name proof_broker_rocq_hammer)
 (synopsis "Proof Broker Rocq plugin — coq-hammer HOL closer opt-in")
 (description "Optional opt-in extension to proof_broker_rocq: registers coq-hammer's hauto as the HOL/FOL closer (Ltac proof_broker_hol_closer). Mirrors lean-bridge/ProofBrokerMathlib's role on the Lean side (which registers Mathlib's aesop). With this package imported, the proof_broker tactic can close Vampire-minted Tier-3 HOL certs; without it, the core plugin's default Ltac fails with a directive to install/import this package (audit H1: HOL goals stay OPEN until a sound closer fires).")
 (depends
  (ocaml (>= 5.0))
  (dune (< 3.24))
  proof_broker_rocq
  ; Same < 9.2 bound as proof_broker_rocq (WATCH(rocq-9.2-assumptions-api)).
  (rocq-runtime (and (>= 9.0) (< 9.2)))
  (coq-core (and (>= 9.0) (< 9.2)))
  (coq-stdlib (and (>= 9.0) (< 9.2)))
  (coq-hammer-tactics (>= 1.3))))
