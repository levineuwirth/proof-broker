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

The exe links dynamically against the dune-built proof_broker_ffi.so.
At lakefile-eval time we discover where the .so lives, trying in
order:
  1. `$PROOF_BROKER_FFI_DIR` env var — explicit override.
  2. `opam var proof_broker:lib` — the directory `opam install
     proof_broker` populates (per the `(install ...)` stanza in
     sdk/ffi/dune).
  3. `../_build/default/sdk/ffi` — in-repo dev fallback when the
     SDK has only been built (not installed). Pre-condition for
     this path: `opam exec -- dune build` has populated the
     workspace _build tree before `lake build` is run.

The linker gets `-l:proof_broker_ffi.so` so it accepts the bare
filename (no `lib` prefix), and an absolute `-rpath` pointing at the
discovered directory so the produced binary self-resolves the .so
without LD_LIBRARY_PATH at runtime.
-/

import Lake
open System Lake DSL

package «proof-broker-bridge»

/-- Mathlib is an OPTIONAL dep: the core `ProofBroker` lib only
    closes LIA goals (via core Lean's `omega`), and is built
    Mathlib-free so projects that just need LIA support don't
    pay the Mathlib build cost. The `ProofBrokerMathlib` lib
    below opts in to Mathlib for LRA support (`linarith` closer
    + `Real` reifier). The require version tracks the
    `lean-toolchain` (v4.30.0-rc2). -/
require «mathlib» from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0-rc2"

/-- Locate the directory containing `proof_broker_ffi.so`. Resolution
    order:
      1. `$PROOF_BROKER_FFI_DIR` env var (explicit override).
      2. `opam var proof_broker:lib` — the install location populated
         by the `(install ...)` stanza in `sdk/ffi/dune` after
         `opam install proof_broker` (or `dune install`).
      3. `../_build/default/sdk/ffi` — in-repo dev fallback when only
         `opam exec -- dune build` has run.

    The returned path is the directory that contains the .so, not
    the .so itself. Callers append `proof_broker_ffi.so` as needed.
    Falls all the way through to the dev path silently — the lib
    will later fail to link/load with a clear error if the .so
    really isn't anywhere on disk. -/
unsafe def discoverFfiDirImpl : String :=
  let attempt : BaseIO String := do
    match (← IO.getEnv "PROOF_BROKER_FFI_DIR") with
    | some d => pure d
    | none =>
      let opamResult ← (IO.Process.output {
        cmd := "opam"
        args := #["var", "proof_broker:lib"]
      }).toBaseIO
      match opamResult with
      | .ok { stdout, exitCode := 0, .. } =>
        let trimmed := stdout.trim
        if trimmed.isEmpty then pure "../_build/default/sdk/ffi"
        else pure trimmed
      | _ => pure "../_build/default/sdk/ffi"
  unsafeBaseIO attempt

@[implemented_by discoverFfiDirImpl]
opaque ffiDir : String

/-- Absolute path to the FFI .so. Most call sites need the full
    file path (eg. `--load-dynlib`), a couple need just the directory
    (`-L`, `-rpath`); both forms come from `ffiDir`. -/
def ffiSoPath : String :=
  ffiDir ++ "/proof_broker_ffi.so"

/-- Linker args needed to make the FFI symbols (`pb_lean_call` from
    libpbglue, `pb_ffi_call` from proof_broker_ffi.so) reachable from
    the `roundtripTest` exe at runtime.

    The `--allow-shlib-undefined` flag is needed because
    `proof_broker_ffi.so` references libc/pthread symbols indirectly
    via OCaml's runtime; see `sdk/FFI_CONVENTIONS.md` "Toolchain notes". -/
def ffiLinkArgs : Array String := #[
  s!"-L{ffiDir}",
  "-l:proof_broker_ffi.so",
  s!"-Wl,-rpath,{ffiDir}",
  "-Wl,--allow-shlib-undefined"
]

/-- Absolute `--load-dynlib=` arg for `libLake_shared.so`, computed
    at lakefile-eval time from `LEAN_SYSROOT`. Mathlib's precompiled
    `.so` (`libmathlib_Mathlib.so`) NEEDs `libLake_shared.so` at
    runtime. Lake's `getAugmentedEnv` advertises the toolchain's
    `lib/lean` on `LD_LIBRARY_PATH` (visible via `lake env`), but
    the env doesn't propagate to lean's elaboration subprocess on
    every system, so the dlopen of `libmathlib_Mathlib.so` fails
    with "libLake_shared.so: cannot open shared object file" when
    a Mathlib-using lib is built. Loading libLake_shared.so
    explicitly via `--load-dynlib` puts its symbols in the
    elaborator's process image so the dynamic loader resolves
    Mathlib's `.so` against the global namespace, no
    `LD_LIBRARY_PATH` needed.

    `LEAN_SYSROOT` is set by Lake itself when invoking the
    lakefile elaborator, so the env lookup at this top-level
    `def` is reliable. We fall back to a bare filename if it's
    somehow missing — that case will fail later but with a clear
    error rather than silent breakage. -/
unsafe def libLakeSharedDynlibArgImpl : String :=
  match unsafeBaseIO (IO.getEnv "LEAN_SYSROOT") with
  | some sr => s!"--load-dynlib={sr}/lib/lean/libLake_shared.so"
  | none => "--load-dynlib=libLake_shared.so"

@[implemented_by libLakeSharedDynlibArgImpl]
opaque libLakeSharedDynlibArg : String

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
  -- referenced by proof_broker_ffi.so (disallowed by
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
    run `opam exec -- dune build` first. -/
@[default_target]
lean_lib ProofBrokerTest where
  roots := #[`Test.Tactic]
  precompileModules := false
  moreLeanArgs := #[
    "--load-dynlib=.lake/build/lib/libpbglue.so",
    s!"--load-dynlib={ffiSoPath}"
  ]

/-- Mathlib-flavored opt-in extension. Importing
    `ProofBrokerMathlib` registers a `ReifierExt` that adds Real
    reification and routes LRA certs through `linarith`. Builds
    independently of the core `ProofBroker` lib so projects
    without Mathlib in their closure can ignore it. -/
lean_lib ProofBrokerMathlib where
  precompileModules := true
  roots := #[`ProofBrokerMathlib]
  moreLeanArgs := #[libLakeSharedDynlibArg]

/-- Tactic-elaboration tests for the Mathlib opt-in. Same shape
    as `ProofBrokerTest`: build success is the test. Separated so
    the LIA-only test lib (`ProofBrokerTest`) doesn't pull in
    Mathlib transitively. -/
@[default_target]
lean_lib ProofBrokerTestMathlib where
  roots := #[`Test.TacticMathlib]
  precompileModules := false
  moreLeanArgs := #[
    "--load-dynlib=.lake/build/lib/libpbglue.so",
    s!"--load-dynlib={ffiSoPath}",
    libLakeSharedDynlibArg
  ]

