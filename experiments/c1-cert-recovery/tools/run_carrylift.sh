#!/usr/bin/env bash
# The fixed-helper comparison, reproduced: the four CarryLift copies (verbatim
# from the completed case study) elaborated here, two warm passes each, against
# an imports-only baseline. This is the reproduction of the case study's
# 4/4 · 4/4 · 4/4 · 3/4 result on THIS machine, with THESE binaries.
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
D="runs/$STAMP/carrylift"
mkdir -p "$D"
printf 'import RmsNormBracket.Model\nimport ProofBroker\nimport ProofBrokerMathlib\n' \
  > "$D/imports_only.lean"
for f in imports_only CarryLift CarryLiftGrind CarryLiftPB CarryLiftPBTerm; do
  if [ "$f" = imports_only ]; then src="$D/imports_only.lean"; else src="corpus/carrylift/$f.lean"; fi
  for pass in 1 2; do
    log="$D/${f}_${pass}.log"
    "$PROBE" "$src" > "$log" 2>&1
    trailer=$(grep -o 'EXIT=[0-9]* WALL=[0-9.]*s' "$log")
    tac=$(grep -o 'tactic execution [0-9.]*m\?s' "$log" | tail -1 | sed 's/tactic execution //')
    nrep=$(grep -c 'proof_broker report:' "$log")
    nerr=$(grep -c ': error: ' "$log")
    echo "$f | pass $pass | $trailer | tactic ${tac:-n/a} | reports $nrep | errors $nerr"
  done
done
echo
echo "# per-site report lines (pass 2)"
for f in CarryLiftPB CarryLiftPBTerm; do
  grep -n 'proof_broker report:\|: error: ' "$D/${f}_2.log" | sed "s/^/$f: /"
done
