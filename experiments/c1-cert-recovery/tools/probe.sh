#!/usr/bin/env bash
# Elaborate one Lean file of THIS campaign against the same dependency closure
# the completed VerInf case study measures against.
#
# Derived from the case study's tools/probe.sh (itself derived from the demo's
# R4 probe). Two deliberate differences, both about NOT touching the case
# study:
#   * the case study's olean output dir is on LEAN_PATH READ-ONLY (so
#     `import RmsNormBracket.Model` resolves to the exact olean whose hash the
#     baseline records) and this campaign's own `.build` is appended for
#     modules written here;
#   * nothing is ever written under the case-study worktree.
# Everything measured — the 8G cap, the EXIT/WALL trailer outside the memory
# scope, PEAK_RSS_BYTES inside it, PROOF_BROKER_REPORT=1 — is unchanged.
#
# Usage: tools/probe.sh [--olean] <file.lean>     (redirect to a .log)
set -u
C="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

DEMO="${PROOF_BROKER_DEMO:-/home/jeans/Repos/research/proof-broker-demo}"
PB="${PROOF_BROKER_REPO:-/home/jeans/Repos/research/proof-broker}"
CS="${CASE_STUDY:-/home/jeans/Repos/research/verinf/.claude/worktrees/rmsnorm-proof-broker-case-study}"
B="$PB/lean-bridge/.lake/build/lib"
FFI="${PROOF_BROKER_FFI_DIR:-$PB/_build/default/sdk/ffi}"
OLEAN=""
if [ "${1:-}" = "--olean" ]; then OLEAN=1; shift; fi
SRC="$1"
LP=""
for p in Cli batteries Qq aesop proofwidgets importGraph LeanSearchClient plausible mathlib; do
  LP="$LP$DEMO/.lake/packages/$p/.lake/build/lib/lean:"
done
LP="$LP$B/lean:$DEMO/.lake/build/lib/lean:$CS/lean/RmsNormBracket/.build:$C/.build"
CAP="${PROBE_MEMMAX:-8G}"

# Verify the shared objects THIS probe resolved — not the defaults. The paths
# below are swung by PROOF_BROKER_REPO / PROOF_BROKER_FFI_DIR, so verifying
# the repository default and then loading an override would check nothing
# (R6 checkpoint-2 final review, issue 2). Cheap: three sha256, no dune, ~12 ms
# on a ~3.5 s run; the entry points do the actual build first.
"$C/tools/build_diag.sh" --verify \
  "$FFI/proof_broker_ffi.so" \
  "$B/libpbglue.so" \
  "$B/libproof_x2dbroker_x2dbridge_ProofBroker.so" || exit 2

export LEAN_PATH="$LP"
export PROBE_B="$B" PROBE_FFI="$FFI"
export PROOF_BROKER_REPORT=1
export PROOF_BROKER_EXAMPLES_DIR="$PB/examples"
OUTARGS=()
if [ -n "$OLEAN" ]; then
  mod="$(basename "${SRC%.lean}")"
  mkdir -p "$C/.build"
  OUTARGS=(-o "$C/.build/$mod.olean" -i "$C/.build/$mod.ilean")
fi
start="$EPOCHREALTIME"
systemd-run --user --scope --quiet \
  -p MemoryMax="$CAP" -p MemorySwapMax=0 \
  bash -c '
    lean \
      --load-dynlib="$PROBE_B/libpbglue.so" \
      --load-dynlib="$PROBE_FFI/proof_broker_ffi.so" \
      --load-dynlib="$PROBE_B/libproof_x2dbroker_x2dbridge_ProofBroker.so" \
      "$@"
    rc=$?
    peak="$(cat /sys/fs/cgroup"$(cut -d: -f3 /proc/self/cgroup)"/memory.peak 2>/dev/null || echo unknown)"
    printf "PEAK_RSS_BYTES=%s\n" "$peak"
    exit "$rc"
  ' probe "${OUTARGS[@]}" "$SRC"
rc=$?
end="$EPOCHREALTIME"
wall="$(awk -v a="$start" -v b="$end" "BEGIN{printf \"%.1f\", b-a}")"
printf "EXIT=%d WALL=%ss CAP=%s\n" "$rc" "$wall" "$CAP"
exit "$rc"
