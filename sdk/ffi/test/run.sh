#!/usr/bin/env bash
#
# Build and run the C-side smoke test against the dune-built shared object.
# Invoked from CI and runnable locally with the proof-broker opam switch active.
#
# Pre-condition: either `opam exec -- dune build sdk` (workspace-rooted,
# what CI runs) or `opam exec -- dune build --root=sdk` (sdk-rooted,
# Phase-0 sub-project invocation pattern) has populated the FFI shared
# object somewhere under _build/. We check both layouts.

set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
SRC="$HERE/test_shim.c"
EXAMPLE="$ROOT/examples/example1-lia-typeclass.json"

# Workspace-rooted build (dune build sdk from repo root) lands here:
SO_WORKSPACE="$ROOT/_build/default/sdk/ffi/proof_broker_ffi.so"
# Sdk-rooted build (dune build --root=sdk) lands here:
SO_SDKROOT="$ROOT/sdk/_build/default/ffi/proof_broker_ffi.so"

if [ -f "$SO_WORKSPACE" ]; then
  SO="$SO_WORKSPACE"
elif [ -f "$SO_SDKROOT" ]; then
  SO="$SO_SDKROOT"
else
  echo "missing proof_broker_ffi.so — checked:" >&2
  echo "  $SO_WORKSPACE" >&2
  echo "  $SO_SDKROOT" >&2
  echo "Run \`opam exec -- dune build sdk\` (workspace-rooted) or" >&2
  echo "\`dune build --root=sdk\` first." >&2
  exit 1
fi

OCAML_INC="$(opam exec -- ocamlc -where)"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

# dl* functions live in libdl on Linux but in libSystem on macOS — no
# separate -ldl flag exists on Darwin and passing one may break the
# link. Select the platform-appropriate trailing libraries.
case "$(uname -s)" in
  Linux)  EXTRA_LIBS=(-lm -lpthread -ldl) ;;
  Darwin) EXTRA_LIBS=(-lm -lpthread) ;;
  *)      EXTRA_LIBS=(-lm -lpthread) ;;
esac

# -Wl,-rpath sets the loader search path so the test exe can find the .so
# without LD_LIBRARY_PATH gymnastics. The .so has no SONAME, so the linker
# records its bare basename in DT_NEEDED.
cc -std=c11 -Wall -Wextra -O2 \
   -I"$OCAML_INC" \
   "$SRC" "$SO" \
   -Wl,-rpath,"$(dirname "$SO")" \
   -o "$TMP/test_shim" \
   "${EXTRA_LIBS[@]}"

"$TMP/test_shim" "$EXAMPLE"
