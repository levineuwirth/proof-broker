#!/usr/bin/env bash
# Build the diagnostic executables against the CURRENT SDK, record what was
# built, and — in --verify mode — check that what is about to be LOADED is
# what was recorded.
#
# Why this exists. The diagnostic executables link `proof_broker` statically
# and the Lean probe loads shared objects by path, so an artifact built before
# an SDK change keeps reporting the OLD SDK's behavior, silently. It happened
# twice in this campaign: a stale `sdk/ffi/proof_broker_ffi.so` under the
# probe, and stale `negcheck.exe` AND `diag.exe` for a whole pass.
# `dune build sdk/lib` rebuilds none of them, so the build is a step inside
# the gate rather than one someone remembers.
#
# Modes:
#   (default)         build, then write the ledger logs/diag_binaries.txt
#   --verify [P ...]  do NOT build. Check the named files against the ledger,
#                     matched BY BASENAME. With no paths, check the default
#                     FFI. Callers that can be pointed at a different file by
#                     environment overrides must pass the path they actually
#                     resolved — verifying the default and loading an override
#                     checks nothing (R6 checkpoint-2 final review, issue 2).
set -u
cd "$(dirname "${BASH_SOURCE[0]}")/.."
ROOT="$(cd ../.. && pwd)"
EXES="diag negcheck exact_budget"
OUT=logs/diag_binaries.txt
FFI_DEFAULT="$ROOT/_build/default/sdk/ffi/proof_broker_ffi.so"
BRIDGE_LIB="$ROOT/lean-bridge/.lake/build/lib"

# --- verify -------------------------------------------------------------
if [ "${1:-}" = "--verify" ]; then
  shift
  [ -r "$OUT" ] || {
    echo "build_diag --verify: no $OUT; run tools/build_diag.sh first" >&2
    exit 2; }
  set -- "${@:-$FFI_DEFAULT}"
  rc=0
  for path in "$@"; do
    base="$(basename "$path")"
    if [ ! -f "$path" ]; then
      echo "build_diag --verify: $path is missing" >&2; rc=2; continue
    fi
    want=$(awk -v b="$base" '$NF == "("b")" {print $2}' "$OUT")
    if [ -z "$want" ]; then
      echo "build_diag --verify: $base is not in the ledger $OUT — the probe" >&2
      echo "  is about to load a file this campaign never recorded" >&2
      rc=2; continue
    fi
    got=$(sha256sum "$path" | cut -d' ' -f1)
    if [ "$want" != "$got" ]; then
      echo "build_diag --verify: $path is not the file the ledger records." >&2
      echo "  ledger=$want" >&2
      echo "  disk  =$got" >&2
      echo "  Run tools/build_diag.sh (a pass against a stale binary measures" >&2
      echo "  the previous SDK — it has happened here)." >&2
      rc=2
    fi
  done
  exit "$rc"
fi

# --- build --------------------------------------------------------------
TARGETS="sdk/ffi sdk/lib"
for e in $EXES; do TARGETS="$TARGETS experiments/c1-cert-recovery/diag/$e.exe"; done
if ! (cd "$ROOT" && dune build $TARGETS) ; then
  echo "build_diag: dune build failed" >&2
  exit 2
fi

# Everything the probe LOADS plus everything the tracers ARE. Each line ends
# with "(<basename>)" so --verify can look a resolved path up by basename.
record() {
  if [ -f "$1" ]; then
    printf '  %-16s %s  (%s)\n' "$(basename "$1" | cut -c1-16)" \
      "$(sha256sum "$1" | cut -d' ' -f1)" "$(basename "$1")"
  else
    printf '  %-16s MISSING  (%s)\n' "$(basename "$1" | cut -c1-16)" "$(basename "$1")"
  fi
}
{
  echo "# diagnostic executables, the shared objects the probe loads, and the"
  echo "# SDK they link. $(date -Is). Rebuilt by tools/build_diag.sh, which"
  echo "# every campaign entry point runs before any timing or probing."
  for e in $EXES; do
    record "$ROOT/_build/default/experiments/c1-cert-recovery/diag/$e.exe"
  done
  record "$FFI_DEFAULT"
  record "$BRIDGE_LIB/libpbglue.so"
  record "$BRIDGE_LIB/libproof_x2dbroker_x2dbridge_ProofBroker.so"
  record "$ROOT/_build/default/sdk/lib/.proof_broker.objs/native/proof_broker__Farkas_search.cmx"
} > "$OUT"

for e in $EXES; do
  p="$ROOT/_build/default/experiments/c1-cert-recovery/diag/$e.exe"
  [ -x "$p" ] || { echo "build_diag: $e.exe missing after build" >&2; exit 2; }
done
cat "$OUT"
