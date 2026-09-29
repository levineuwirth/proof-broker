#!/usr/bin/env bash
# Capture the IR of every corpus case, then run the OCaml stage tracer on it.
# Sequential; nothing else may run while this is in flight.
set -u
cd "$(dirname "${BASH_SOURCE[0]}")/.."

# Build preflight. The diagnostic executables and the FFI shared object must be
# the ones that link the CURRENT SDK before ANY timing or probing starts: a
# statically linked tracer, or a probe loading a stale `proof_broker_ffi.so`,
# reports the previous SDK's behavior silently, and has done so twice in this
# campaign. `BUILD_DIAG` is the seam the preflight self-test injects a failing
# helper through (tools/test_runner_preflight.sh).
"${BUILD_DIAG:-tools/build_diag.sh}" > /dev/null || {
  echo "$(basename "$0"): diagnostic build failed — refusing to run" >&2
  exit 2
}

STAMP="$(cat logs/STAMP)"
RAW="raw/$STAMP"
mkdir -p "$RAW" "runs/$STAMP/irlogs"
PROBE="${PROBE_BIN:-tools/probe.sh}"
DIAG="${DIAG_BIN:-../../_build/default/experiments/c1-cert-recovery/diag/diag.exe}"
for f in ir/*.dump.lean; do
  id="$(basename "$f" .dump.lean)"
  "$PROBE" "$f" > "runs/$STAMP/irlogs/$id.capture.log" 2>&1
  rc=$?
  if [ ! -f "ir/$id.json" ]; then
    echo "NO IR   $id (probe exit $rc)"; continue
  fi
  "$DIAG" "ir/$id.json" "$RAW" "$id" > "$RAW/$id.stdout" 2>"$RAW/$id.stderr"
  echo "ok      $id (probe exit $rc, diag exit $?)"
done
