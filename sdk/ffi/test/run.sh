#!/usr/bin/env bash
#
# Build and run the C-side smoke test against the dune-built shared object.
# Invoked from CI and runnable locally with the proof-broker opam switch active.
#
# Pre-condition: `opam exec -- dune build --root=sdk` has populated
# sdk/_build/default/ffi/proof_broker_ffi.so.

set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
SO="$ROOT/sdk/_build/default/ffi/proof_broker_ffi.so"
SRC="$HERE/test_shim.c"
EXAMPLE="$ROOT/examples/example1-lia-typeclass.json"

if [ ! -f "$SO" ]; then
  echo "missing $SO — run \`opam exec -- dune build --root=sdk\` first" >&2
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
