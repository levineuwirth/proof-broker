#!/usr/bin/env bash
# Focused test: a FAILING BUILD PREFLIGHT MUST STOP EVERY ENTRY POINT, before
# any probe or tracer runs.
#
# Two things this test has to get right, and the second one it got wrong once.
#
# 1. It asserts BOTH halves per entry point: the runner exits nonzero, AND no
#    probe and no tracer was invoked — counted by canaries substituted through
#    the PROBE_BIN / DIAG_BIN / NEGCHECK_BIN seams. A positive control runs
#    first, so the test cannot pass because a seam is dead.
#
# 2. IT RUNS IN ITS OWN CAMPAIGN. The first version ran the real runners
#    against the real `logs/STAMP`, so its positive controls overwrote the
#    campaign's own evidence: `results.json` reduced to one case, every
#    carry-comparison, held-out and IR-capture log truncated, every
#    negative-check JSON deleted — and it exited 0 while doing it
#    (R6 checkpoint-2 final review, issue 1). Everything now happens in a
#    temporary campaign root built by `setup_temp_campaign`, and the test
#    additionally SNAPSHOTS the real runs/ raw/ logs/ trees and fails if a
#    single byte of them moved.
set -u
cd "$(dirname "${BASH_SOURCE[0]}")/.."
REAL="$PWD"
fails=0

# --- a manifest of the real evidence, so we can prove we did not touch it ---
# This test's OWN output file is excluded: a caller that redirects the test
# into logs/ would otherwise trip the guard on the test's own log, which says
# nothing about whether the runners touched the campaign.
SELF_LOG=logs/runner_preflight_selftest.txt
snapshot() {
  find runs raw logs -type f -printf '%p %s %T@\n' 2>/dev/null \
    | grep -v "^$SELF_LOG " | LC_ALL=C sort
}
BEFORE="$(mktemp)"; snapshot > "$BEFORE"

# --- a throwaway campaign with just enough fixtures to drive every loop -----
setup_temp_campaign() {
  local T; T="$(mktemp -d)"
  mkdir -p "$T"/{tools,logs,ir,heldout,corpus/carrylift,raw,runs}
  cp "$REAL"/tools/*.sh "$REAL"/tools/*.py "$T/tools/"
  echo "TESTSTAMP" > "$T/logs/STAMP"
  # one input per loop, so each runner has something to iterate over
  printf -- '-- preflight test placeholder\n' > "$T/ir/X.dump.lean"
  printf '{}\n'                               > "$T/ir/X.json"
  printf -- '-- preflight test placeholder\n' > "$T/heldout/X.omega.lean"
  for f in CarryLift CarryLiftGrind CarryLiftPB CarryLiftPBTerm; do
    printf -- '-- preflight test placeholder\n' > "$T/corpus/carrylift/$f.lean"
  done
  mkdir -p "$T/runs/TESTSTAMP/lean"
  printf -- '-- preflight test placeholder\n' > "$T/runs/TESTSTAMP/lean/X.omega.lean"
  # run_negchecks iterates the expectation manifest and skips any case with no
  # captured IR, so give every one of them a placeholder or the positive
  # control would count zero invocations for the wrong reason
  ( cd "$T" && python3 tools/negcheck_expectations.py 2>/dev/null \
      | while read -r id exp; do
          [ "$exp" = no-ir ] || printf '{}\n' > "ir/$id.json"
        done )
  echo "$T"
}

run_in() {                       # run_in <campaign> <env...> -- <cmd...>
  local T="$1"; shift
  ( cd "$T" && env "$@" )
}

control() {                      # seams live under a PASSING preflight
  local name="$1"; shift
  local T; T="$(setup_temp_campaign)"
  local canary="$T/canary.log"; : > "$canary"
  ( cd "$T" && CANARY_FILE="$canary" BUILD_DIAG=/bin/true \
      PROBE_BIN="$REAL/tools/canary_probe.sh" \
      DIAG_BIN="$REAL/tools/canary_probe.sh" \
      NEGCHECK_BIN="$REAL/tools/canary_probe.sh" \
      "$@" ) > /dev/null 2>&1
  local calls; calls=$(wc -l < "$canary")
  local verdict=ok
  if [ "$calls" -eq 0 ]; then
    verdict="FAIL (seam is dead: the canary was never called)"
    fails=$((fails + 1))
  fi
  printf '  %-26s invocations=%-4s %s\n' "$name" "$calls" "$verdict"
  rm -rf "$T"
}

check() {                        # nothing runs under a FAILING preflight
  local name="$1"; shift
  local T; T="$(setup_temp_campaign)"
  local canary="$T/canary.log"; : > "$canary"
  ( cd "$T" && CANARY_FILE="$canary" BUILD_DIAG="$REAL/tools/build_fault_stub.sh" \
      PROBE_BIN="$REAL/tools/canary_probe.sh" \
      DIAG_BIN="$REAL/tools/canary_probe.sh" \
      NEGCHECK_BIN="$REAL/tools/canary_probe.sh" \
      "$@" ) > /dev/null 2>&1
  local rc=$?
  local calls; calls=$(wc -l < "$canary")
  local verdict=ok
  if [ "$rc" -eq 0 ]; then
    verdict="FAIL (exited 0 despite a failing preflight)"; fails=$((fails + 1))
  elif [ "$calls" -ne 0 ]; then
    verdict="FAIL ($calls probe/tracer invocation(s) after a failing preflight)"
    fails=$((fails + 1))
  fi
  printf '  %-26s exit=%-3s invocations=%-3s %s\n' "$name" "$rc" "$calls" "$verdict"
  rm -rf "$T"
}

echo "# positive control: with a passing preflight the seams are live"
control "capture_ir.sh"         ./tools/capture_ir.sh
control "run_carrylift.sh"      ./tools/run_carrylift.sh
control "run_heldout_broker.sh" ./tools/run_heldout_broker.sh
control "run.py"                python3 tools/run.py runs/TESTSTAMP
control "run_negchecks.sh"      ./tools/run_negchecks.sh
echo

echo "# a failing build preflight must stop every entry point"
check "capture_ir.sh"         ./tools/capture_ir.sh
check "run_carrylift.sh"      ./tools/run_carrylift.sh
check "run_heldout_broker.sh" ./tools/run_heldout_broker.sh
check "run_negchecks.sh"      ./tools/run_negchecks.sh
check "run.py"                python3 tools/run.py runs/TESTSTAMP
echo

echo "# the real campaign's evidence must be untouched by this test"
AFTER="$(mktemp)"; snapshot > "$AFTER"
if diff -q "$BEFORE" "$AFTER" > /dev/null; then
  echo "  runs/ raw/ logs/            unchanged                        ok"
else
  echo "  runs/ raw/ logs/            CHANGED — the test wrote to the real campaign:"
  diff "$BEFORE" "$AFTER" | head -20 | sed 's/^/    /'
  fails=$((fails + 1))
fi
rm -f "$BEFORE" "$AFTER"

echo
if [ "$fails" -eq 0 ]; then
  echo "all entry points refuse to run on a failed preflight, and the real"
  echo "campaign was not touched"
else
  echo "$fails check(s) FAILED"
fi
exit "$fails"
