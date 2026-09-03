# Using the Proof Broker bridge from your own Lean project

One page. Everything a downstream Lake project needs to call
`proof_broker` / `proof_broker_term` / `proof_broker_walker`, and
nothing else.

The worked example this page was extracted from is the R4 fellowship
demo (`proof-broker-demo`), a separate Lake project that closes the
`verinf` bracket-spike obligations against this bridge.

## 1. What has to exist before `lake build`

The Lean bridge is a thin shell over the OCaml SDK. Three artifacts,
in this order:

| artifact | built by | where it lands |
|---|---|---|
| `proof_broker_ffi.so` | `opam exec -- dune build sdk` in the proof-broker repo | `_build/default/sdk/ffi/` |
| `libpbglue.so` | `lake build` of the bridge (its `extern_lib`) | `lean-bridge/.lake/build/lib/` |
| `examples/manifest-*.json` | checked in | proof-broker repo root |

Solvers (`cvc5`, `z3`, `cvc4`, `vampire`) must be on `PATH`; the
manifests name them.

    cd /path/to/proof-broker
    opam exec -- dune build sdk
    export PROOF_BROKER_FFI_DIR=$PWD/_build/default/sdk/ffi
    cd /path/to/your-project
    lake build

`PROOF_BROKER_FFI_DIR` is the only variable you normally need to set.
The manifests are found on their own (§4).

## 2. `lakefile.toml` is not enough

The two `--load-dynlib` paths below are absolute and machine-specific,
so they have to be *computed*. Use `lakefile.lean`.

## 3. The recipe

```lean
import Lake
open System Lake DSL

package «your-project»

require «proof-broker-bridge» from git
  "https://github.com/<owner>/proof-broker" @ "<tag>" / "lean-bridge"
-- during development, a sibling checkout instead:
-- require «proof-broker-bridge» from ".." / "proof-broker" / "lean-bridge"

private unsafe def firstDirWith (probe : String) (cands : List FilePath) : BaseIO String := do
  for d in cands do
    if ← (d / probe).pathExists then return d.normalize.toString
  return (cands.headD "." |>.normalize.toString)

unsafe def pbBridgeLibDirImpl : String :=
  unsafeBaseIO do
    let fromEnv := (← IO.getEnv "PROOF_BROKER_BRIDGE_LIB_DIR").map FilePath.mk
    firstDirWith "libpbglue.so" (fromEnv.toList ++ [
      __dir__ / ".lake" / "packages" / "proof-broker-bridge" / ".lake" / "build" / "lib",
      __dir__ / ".." / "proof-broker" / "lean-bridge" / ".lake" / "build" / "lib"
    ])

@[implemented_by pbBridgeLibDirImpl] opaque pbBridgeLibDir : String

unsafe def pbFfiDirImpl : String :=
  unsafeBaseIO do
    match ← IO.getEnv "PROOF_BROKER_FFI_DIR" with
    | some d => return (FilePath.mk d).normalize.toString
    | none =>
      firstDirWith "proof_broker_ffi.so"
        [__dir__ / ".." / "proof-broker" / "_build" / "default" / "sdk" / "ffi"]

@[implemented_by pbFfiDirImpl] opaque pbFfiDir : String

def proofBrokerLeanArgs : Array String := #[
  s!"--load-dynlib={pbBridgeLibDir}/libpbglue.so",
  s!"--load-dynlib={pbFfiDir}/proof_broker_ffi.so"
]

lean_lib YourLib where
  moreLeanArgs := proofBrokerLeanArgs
```

`__dir__` is Lake's directory-of-this-lakefile constant, so the two
probe lists work from any current directory. Put
`proofBrokerLeanArgs` on **every** `lean_lib` whose modules call the
tactic; a lib without it elaborates fine right up to the first
tactic call.

The mirror of this definition inside the bridge is
`proofBrokerLeanArgs` in `lean-bridge/lakefile.lean`. A downstream
project cannot import it — Lake config files are not Lean modules —
so the block above is a copy, and the two are kept in step by hand.

### Why both flags

`ProofBroker` is a precompiled library, so Lake loads its module
shared object into the elaborator for you. That object has two
unresolved C symbols that Lake does not chase for a downstream
module. Drop either flag and you get (measured, Lean v4.32.0):

| flags | failure |
|---|---|
| neither | `Could not find native implementation of external declaration 'ProofBroker.pbCall'` |
| bridge lib only | `libproof_…_ProofBroker.so: undefined symbol: pb_lean_call` |
| + `libpbglue.so` | `libpbglue.so: undefined symbol: pb_ffi_init` |
| + `proof_broker_ffi.so` | builds |

`libLake_shared.so` is **not** needed. It was part of the recipe only
while `ProofBrokerMathlib` was precompiled under Lean v4.30
(`delta.md` §5.1).

## 4. Manifests

The tactic reads adapter manifests from `examples/manifest-*.json`.
Resolution order:

1. `$PROOF_BROKER_EXAMPLES_DIR`, used verbatim if set — an explicit
   override that is wrong fails loudly rather than falling through.
2. `<cwd>/../examples` — the in-repo convention.
3. The directory that ships with the bridge you built against,
   derived from where `ProofBroker.Tactic.olean` was loaded from.

Step 3 is what makes a downstream build work with no variable set,
under both a git require and a path require. Set
`PROOF_BROKER_EXAMPLES_DIR` if you vendor the manifests elsewhere.

## 5. Which tactic

| tactic | closes with | use when |
|---|---|---|
| `proof_broker` | certificate-gated re-proof (`omega`/`linarith`), walker when the cert is Tier 3 | default |
| `proof_broker_term` | the Farkas witness, as a proof term | you want the certificate to be structurally load-bearing |
| `proof_broker_walker` | the Alethe walker only, no fallback | regression-guarding the live walker path |
| `proof_broker?` | same as `proof_broker`, plus a `logInfo` trace of the extraction path | debugging |

`proof_broker [cvc5, z3]` restricts and orders dispatch.

## 6. Axiom footprint

Nothing the bridge does adds an axiom: goals it closes depend on the
usual `[propext, Classical.choice, Quot.sound]` (often less). Gate it
in your own CI with `tools/check_axioms.py` — see
`tools/AXIOM_GUARD.md` in the proof-broker repo, which documents the
allowlist format for external projects.

## 7. Troubleshooting

| symptom | cause |
|---|---|
| `Could not find native implementation of external declaration 'ProofBroker.pbCall'` | the lib is not precompiled or you invoked `lean` by hand without Lake's dynlibs |
| `undefined symbol: pb_lean_call` | missing `--load-dynlib=…/libpbglue.so` |
| `undefined symbol: pb_ffi_init` | missing `--load-dynlib=…/proof_broker_ffi.so` |
| `no manifests found in …` | none of §4's three candidates has `manifest-cvc5.json` |
| `no adapter capable of fragment …` | the goal's fragment is outside the manifests' advertised capabilities, or no solver on `PATH` |
| a stale `.so` after switching branches in the proof-broker repo | re-run `opam exec -- dune build sdk`; the `.so` is not per-branch |
