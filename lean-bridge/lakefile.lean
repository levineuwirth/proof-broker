/-
Lake project for the Phase-0 FFI spike's Lean side.

Builds:
* `ProofBroker` lean_lib — Lean surface (extern wrapper + tactic).
* `libpbglue` static lib — C glue bridging Lean's lean_object* String
  ABI to the shim's plain (const char *, char **) ABI.
* `roundtripTest` exe — Main.lean: round-trip a fixture and verify
  structural equality after normalization.
* `ProofBrokerTest` lean_lib — Test/Tactic.lean: real Lean goals
  closed end-to-end by `by proof_broker` against the broker. Build
  success is the test.

The exe links dynamically against the dune-built proof_broker_ffi.so
sitting in ../sdk/_build/default/ffi (relative to this lakefile's dir).
We pass `-l:proof_broker_ffi.so` so the linker accepts the bare filename
(no `lib` prefix), and an `$ORIGIN`-relative `-rpath` so the produced
binary self-resolves the .so without LD_LIBRARY_PATH at runtime.

Pre-condition: `opam exec -- dune build --root=sdk` has populated
sdk/_build/default/ffi/proof_broker_ffi.so before `lake build` is run.
-/

import Lake
open System Lake DSL

package «proof-broker-bridge»

/-- Linker args needed to make the FFI symbols (`pb_lean_call` from
    libpbglue, `pb_ffi_call` from proof_broker_ffi.so) reachable from
    the `roundtripTest` exe at runtime.

    The `--allow-shlib-undefined` flag is needed because
    `proof_broker_ffi.so` references libc/pthread symbols indirectly
    via OCaml's runtime; see `sdk/FFI_CONVENTIONS.md` "Toolchain notes". -/
def ffiLinkArgs : Array String := #[
  "-L../sdk/_build/default/ffi",
  "-l:proof_broker_ffi.so",
  "-Wl,-rpath,$ORIGIN/../../../../sdk/_build/default/ffi",
  "-Wl,--allow-shlib-undefined"
]

lean_lib ProofBroker where
  precompileModules := true

target «glue.o» pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "glue.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "glue.c"
  let flags := #[
    "-I", (← getLeanIncludeDir).toString,
    "-fPIC", "-Wall", "-O2"
  ]
  buildO oFile srcJob flags #[] "cc" getLeanTrace

extern_lib «libpbglue» pkg := do
  let name := nameToStaticLib "pbglue"
  let glueO ← fetch <| pkg.target ``«glue.o»
  buildStaticLib (pkg.staticLibDir / name) #[glueO]

@[default_target]
lean_exe roundtripTest where
  root := `Main
  -- If linking fails with errors like "undefined reference: pthread_*@GLIBC_2.X
  -- referenced by ../sdk/_build/default/ffi/proof_broker_ffi.so (disallowed by
  -- --no-allow-shlib-undefined)", see sdk/FFI_CONVENTIONS.md "Toolchain notes"
  -- — the --allow-shlib-undefined flag below is the documented fix.
  moreLinkArgs := ffiLinkArgs

/-- Tactic-elaboration tests. Each `example ... := by proof_broker`
    in `Test/Tactic.lean` is a real Lean goal that elaborates only
    if the broker dispatches and the cert verifies. Build success of
    this lib is the test.

    The `--load-dynlib` flags below pull in the FFI shared libs at
    elaboration time so the `pb_lean_call` reference inside
    `ProofBroker.Bridge.so` (loaded automatically by Lake because
    `ProofBroker` is precompiled) resolves under `dlopen`. Both
    paths are cwd-relative; the build must be invoked from
    `lean-bridge/`. The OCaml-side FFI .so must already exist —
    run `opam exec -- dune build --root=sdk` first. -/
@[default_target]
lean_lib ProofBrokerTest where
  roots := #[`Test.Tactic]
  precompileModules := false
  moreLeanArgs := #[
    "--load-dynlib=.lake/build/lib/libpbglue.so",
    "--load-dynlib=../sdk/_build/default/ffi/proof_broker_ffi.so"
  ]

/-- Axiom-dependency check for the Tier 1 LIA closer. Compiled in
    its own elaborator process (separate `lean_lib` from
    `ProofBrokerTest`), with one `proof_broker` invocation
    followed by one `#print axioms`. The build emits the axiom
    list as an info line; CI grep / human inspection asserts the
    trust axiom `proofBrokerCertSound` is absent. Splitting from
    `ProofBrokerTest` sidesteps an OCaml lifecycle panic that
    appears when many FFI calls + kernel-traversing commands
    coexist in a single module. -/
@[default_target]
lean_lib ProofBrokerAxiomCheck where
  roots := #[`Test.AxiomCheck]
  precompileModules := false
  moreLeanArgs := #[
    "--load-dynlib=.lake/build/lib/libpbglue.so",
    "--load-dynlib=../sdk/_build/default/ffi/proof_broker_ffi.so"
  ]
