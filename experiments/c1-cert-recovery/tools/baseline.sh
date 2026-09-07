#!/usr/bin/env bash
# Record the identity of everything this campaign loads. Hashes, not HEADs:
# the probe loads sibling-checkout .so/.olean files that a checkout HEAD does
# not identify. Re-run at the END of the campaign too and diff, so a rebuild
# that moved a binary under us is visible.
set -u
C="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PB="${PROOF_BROKER_REPO:-/home/jeans/Repos/research/proof-broker}"
DEMO="${PROOF_BROKER_DEMO:-/home/jeans/Repos/research/proof-broker-demo}"
CS="${CASE_STUDY:-/home/jeans/Repos/research/verinf/.claude/worktrees/rmsnorm-proof-broker-case-study}"

h() { if [ -f "$1" ]; then printf '  %-58s %s  (mtime %s)\n' "$2" \
        "$(sha256sum "$1" | cut -d' ' -f1)" "$(date -r "$1" '+%Y-%m-%d\ %H:%M')";
      else printf '  %-58s MISSING\n' "$2"; fi; }

echo "# campaign baseline, recorded $(date -Is)"
echo "# host $(uname -srm), $(nproc) cpus"
echo
echo "proof-broker      $PB"
echo "  HEAD            $(git -C "$PB" rev-parse HEAD) ($(git -C "$PB" rev-parse --abbrev-ref HEAD))"
echo "  worktree dirty  $(git -C "$PB" status --porcelain | wc -l) path(s)"
h "$PB/lean-bridge/.lake/build/lib/libpbglue.so"                            "libpbglue.so"
h "$PB/lean-bridge/.lake/build/lib/libproof_x2dbroker_x2dbridge_ProofBroker.so" "libproof-broker-bridge_ProofBroker.so"
h "$PB/_build/default/sdk/ffi/proof_broker_ffi.so"                          "sdk/ffi/proof_broker_ffi.so"
h "$PB/lean-bridge/.lake/build/lib/lean/ProofBroker/Tactic.olean"           "ProofBroker/Tactic.olean"
h "$PB/lean-bridge/.lake/build/lib/lean/ProofBrokerMathlib.olean"           "ProofBrokerMathlib.olean"
for m in cvc4 cvc5 z3 vampire; do h "$PB/examples/manifest-$m.json" "examples/manifest-$m.json"; done
echo
echo "proof-broker-demo $DEMO"
echo "  HEAD            $(git -C "$DEMO" rev-parse HEAD) ($(git -C "$DEMO" rev-parse --abbrev-ref HEAD))"
h "$DEMO/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" "Mathlib.olean"
echo "  lake-manifest pins:"
python3 - "$DEMO/lake-manifest.json" <<'PY'
import json,sys
m=json.load(open(sys.argv[1]))
for p in m.get("packages",[]):
    print("    %-24s %s" % (p.get("name"), p.get("rev") or p.get("inputRev") or ""))
PY
echo
echo "verinf case study $CS"
echo "  HEAD            $(git -C "$CS" rev-parse HEAD) ($(git -C "$CS" rev-parse --abbrev-ref HEAD 2>/dev/null))"
echo "  dirty           $(git -C "$CS" status --porcelain | wc -l) path(s)"
h "$CS/lean/RmsNormBracket/.build/RmsNormBracket/Model.olean" "case-study Model.olean"
echo
echo "toolchain"
echo "  lean-toolchain (case study)  $(cat "$CS/lean/RmsNormBracket/lean-toolchain")"
echo "  lean                         $( (cd "$CS/lean/RmsNormBracket" && lean --version) 2>&1 | head -1)"
echo "  elan                         $(elan --version 2>&1 | head -1)"
echo "  dune                         $(dune --version 2>&1 | head -1)"
echo "  ocaml                        $(ocaml -version 2>&1 | head -1)"
echo "solvers (PATH binaries the adapters spawn)"
printf '  %-10s %s\n' z3      "$(z3 --version 2>&1 | head -1)   [$(command -v z3)]"
printf '  %-10s %s\n' cvc5    "$(cvc5 --version 2>&1 | head -1) [$(command -v cvc5)]"
printf '  %-10s %s\n' cvc4    "$(cvc4 --version 2>&1 | head -1) [$(command -v cvc4)]"
printf '  %-10s %s\n' vampire "$(vampire --version 2>&1 | head -1) [$(command -v vampire)]"
