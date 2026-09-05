/-
Lake project for the Lean bridge — the production Lean-side build
(it started life as the Phase-0 FFI spike's Lean side).

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
    `lean-toolchain` (v4.32.0 — a Lake workspace has one toolchain and
    one Mathlib chosen by the root project, so the bridge must compile
    under the version its downstream consumers pin; R0.5). -/
require «mathlib» from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.32.0"

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

/-- Absolute path to this package's `libpbglue.so`, the shared form
    of the `extern_lib «libpbglue»` below. `__dir__` is the directory
    of THIS lakefile, filled in by Lake at config-elaboration time,
    so the path does not depend on where `lake` was invoked from
    (R4.1: it used to be spelled `.lake/build/lib/libpbglue.so`,
    which only resolved when the build ran from `lean-bridge/`). -/
def glueSoPath : String :=
  (__dir__ / ".lake" / "build" / "lib" / "libpbglue.so").normalize.toString

/-- **The consumer recipe.** Elaboration-time `--load-dynlib` flags
    that every `lean_lib` whose modules call `proof_broker` /
    `proof_broker_term` / `proof_broker_walker` needs on its
    `moreLeanArgs`.

    `ProofBroker` is precompiled, so Lake loads its module shared
    object into the elaborator automatically — but that object has
    two unresolved C symbols: `pb_lean_call` (in `libpbglue.so`,
    this package's `extern_lib`, which Lake does NOT load for a
    *downstream* module) and `pb_ffi_call` (in the OCaml SDK's
    `proof_broker_ffi.so`, which Lake has never heard of). Both must
    be pre-loaded, in this order.

    A downstream project cannot import this definition — Lake
    lakefiles are not modules — so it reproduces these two flags
    with its own path discovery. `CONSUMERS.md` carries the
    copy-pasteable block and the demo project
    (`~/Repos/research/proof-broker-demo/lakefile.lean`) is the
    worked example. -/
def proofBrokerLeanArgs : Array String := #[
  s!"--load-dynlib={glueSoPath}",
  s!"--load-dynlib={ffiSoPath}"
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
    paths are absolute (`proofBrokerLeanArgs` above), so the build
    does not have to be invoked from `lean-bridge/`. The OCaml-side
    FFI .so must already exist — run `opam exec -- dune build`
    first. -/
@[default_target]
lean_lib ProofBrokerTest where
  roots := #[`Test.Tactic, `Test.TacticStress]
  precompileModules := false
  moreLeanArgs := proofBrokerLeanArgs

/-- Live-strict walker suite over the corpus (R1.5). Generated by
    `tools/gen_corpus_replay.py` from `corpus/goals/*.json`: each
    theorem closes ONLY via `proof_broker_walker` (live cvc5
    dispatch → Tier-3 mint → Alethe walker → kernel; no `omega`
    fallback), so build success proves the full production path
    per goal. Same dynlib setup as `ProofBrokerTest`. -/
@[default_target]
lean_lib ProofBrokerCorpusLive where
  roots := #[`Test.CorpusWalkerLive]
  precompileModules := false
  moreLeanArgs := proofBrokerLeanArgs

/-- Mathlib-flavored opt-in extension. Importing
    `ProofBrokerMathlib` registers a `ReifierExt` that adds Real
    reification and routes LRA certs through `linarith`. Builds
    independently of the core `ProofBroker` lib so projects
    without Mathlib in their closure can ignore it.

    NOT precompiled (delta.md §5.1, reconsideration record of
    2026-08-30): `precompileModules := true` here made Lake build
    `Mathlib:shared` (every Mathlib module's `.c.o` — ~17k of the
    17,382 jobs `lake build` scheduled with the precompile on
    2026-08-30, and the bulk of the lean-bridge CI job: 15m09 on the
    last green `main` run, 2026-06-19) and load the precompiled Mathlib
    `.so` into the elaborator — which needed the `libLake_shared.so`
    `--load-dynlib` workaround under Lean v4.30 and fails outright
    under v4.32 / Lake 5.0 (`symbol lookup error: … libmathlib_Mathlib.so:
    undefined symbol: initialize_proofwidgets_ProofWidgets_…`, the
    library `.so`s are loaded without cross-linking). Nothing in this
    lib needs native code: its `initialize` registration and closers
    run in the interpreter, and the FFI-bearing `ProofBroker` core
    lib below stays precompiled. Result (dated measurement, delta.md
    §5.1): 878 build jobs from an incremental `lake build` on the R0.5
    tree, 2026-08-30 (885 from `lake clean` on the same tree), instead
    of 17,382 — and no dynlib plumbing for Mathlib at all. -/
lean_lib ProofBrokerMathlib where
  precompileModules := false
  roots := #[`ProofBrokerMathlib]

/-- Tactic-elaboration tests for the Mathlib opt-in. Same shape
    as `ProofBrokerTest`: build success is the test. Separated so
    the LIA-only test lib (`ProofBrokerTest`) doesn't pull in
    Mathlib transitively. -/
@[default_target]
lean_lib ProofBrokerTestMathlib where
  roots := #[`Test.TacticMathlib]
  precompileModules := false
  moreLeanArgs := proofBrokerLeanArgs

