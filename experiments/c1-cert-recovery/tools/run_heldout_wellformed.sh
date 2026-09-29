#!/usr/bin/env bash
# WELL-FORMEDNESS ONLY. The held-out variants are not evaluated at this
# checkpoint: no broker closer is run on any of them and no broker result from
# them enters the diagnosis. What this does run is `omega`, so that a held-out
# set which does not elaborate — or is not actually true — is caught now
# rather than when it is supposed to judge a repair. `omega` sees no
# certificate machinery, so nothing it reports can steer the diagnosis.
set -u
cd "$(dirname "${BASH_SOURCE[0]}")/.."
STAMP="$(cat logs/STAMP)"
mkdir -p "runs/$STAMP/heldout"
for f in heldout/*.omega.lean; do
  id="$(basename "$f" .omega.lean)"
  log="runs/$STAMP/heldout/$id.omega.log"
  tools/probe.sh "$f" > "$log" 2>&1
  echo "$id | $(grep -o 'EXIT=[0-9]*' "$log") | $(grep -m1 ': error: ' "$log" | cut -c1-90)"
done
