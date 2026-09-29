#!/usr/bin/env bash
# The HELD-OUT cases, run for the first time — checkpoint 2 only.
#
# These were defined at checkpoint 1 and deliberately left unrun so their
# results could not steer that checkpoint's diagnosis. They are the
# out-of-sample evidence for the repair, so they are run ONCE, here, after the
# repair was designed and implemented, and their results are reported as
# out-of-sample rather than folded into the in-sample table.
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

PROBE="${PROBE_BIN:-tools/probe.sh}"
STAMP="$(cat logs/STAMP)"
D="runs/$STAMP/heldout"
mkdir -p "$D"
for f in heldout/*.lean; do
  b="$(basename "$f" .lean)"
  log="$D/$b.log"
  "$PROBE" "$f" > "$log" 2>&1
  ex=$(grep -o 'EXIT=[0-9]*' "$log")
  rep=$(grep -o 'closer=[^ ]* backend=[^ ]* tier=[^ ]* format=[^ ]*' "$log" | tail -1)
  err=$(grep -m1 ': error: ' "$log" | sed 's/.*error: //' | cut -c1-80)
  printf '%-34s %s | %s\n' "$b" "$ex" "${rep:-${err:-ok}}"
done
