/-
Lake project for the Phase-0 FFI spike's Lean side.

Builds:
* `ProofBroker` lean_lib — Lean surface (extern wrapper).
* `libpbglue` static lib — C glue bridging Lean's lean_object* String
  ABI to the shim's plain (const char *, char **) ABI.
* `roundtripTest` exe — Main.lean: round-trip a fixture and verify
  structural equality after normalization.

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
  moreLinkArgs := #[
    "-L../sdk/_build/default/ffi",
    "-l:proof_broker_ffi.so",
    "-Wl,-rpath,$ORIGIN/../../../../sdk/_build/default/ffi",
    "-Wl,--allow-shlib-undefined"
  ]
