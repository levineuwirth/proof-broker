#!/usr/bin/env bash
# tools/PbDiag.lean copies four private front-end functions out of the bridge's
# ProofBroker/Tactic.lean so the dumped IR is the IR the production tactic
# dispatches. A copy that drifts silently would make every IR in this campaign
# a different document from the one under study, so the copies are checked
# rather than trusted: for each function, the bridge's body and the copy's body
# must be identical modulo the doc comment.
set -u
cd "$(dirname "${BASH_SOURCE[0]}")/.."
PB="${PROOF_BROKER_REPO:-/home/jeans/Repos/research/proof-broker}"
SRC="$PB/lean-bridge/ProofBroker/Tactic.lean"
COPY=tools/PbDiag.lean
rc=0
for fn in normalizeGoalForBroker introLeadingNatForalls smtSymbolTailChar \
          smtReservedWords smtSafeIdent smtSanitizeIdent renameLocalsForSmt; do
  # body = from the `def`/`partial def` line to the next blank line followed by
  # a non-indented token; good enough for these seven, and any mismatch is a
  # diff a reader reads, not a verdict a script decides.
  a=$(awk -v f="$fn" '
      $0 ~ ("^(private )?(partial )?def " f " ") {p=1}
      p {print}
      p && /^$/ {exit}' "$SRC" | grep -v '^[[:space:]]*--' | sed 's/^private //; s/[[:space:]]*$//')
  b=$(awk -v f="$fn" '
      $0 ~ ("^(private )?(partial )?def " f " ") {p=1}
      p {print}
      p && /^$/ {exit}' "$COPY" | grep -v '^[[:space:]]*--' | sed 's/^private //; s/[[:space:]]*$//')
  if [ -z "$a" ]; then echo "DRIFT  $fn: not found in $SRC"; rc=1; continue; fi
  if [ -z "$b" ]; then echo "DRIFT  $fn: not found in $COPY"; rc=1; continue; fi
  if [ "$a" = "$b" ]; then echo "same   $fn"; else
    echo "DRIFT  $fn:"; diff <(printf '%s\n' "$a") <(printf '%s\n' "$b") | sed 's/^/       /'
    rc=1
  fi
done
exit $rc
