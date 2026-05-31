#!/usr/bin/env python3
"""Walker rule-parity check (Lean <-> Rocq).

Both bridges elaborate cvc5 alethe-2024 traces per-rule. Soundness aside,
the two dispatch tables must cover the IDENTICAL set of rule names: if one
bridge learns a rule the other has not, a trace closes on one bridge and
falls through to the arithmetic fallback (omega / lia) on the other,
silently. This catches that drift.

SCOPE: compares the SET of rule-name string literals dispatched in each
walker's step-dispatch match, extracted from between

    PARITY:walker-rules BEGIN  ...  PARITY:walker-rules END

markers in each source file. It does NOT verify that equally-named arms
behave identically -- that is what the snapshot tests + replay corpus
cover. Keeping the claim narrow is the point: a cheap tripwire, not a
proof of semantic parity.

Pure text extraction: no bridge build, no solver. Runs in CI and locally
(works even when the local Rocq/Lean toolchains are unavailable).

Exit 0 if the rule sets match, 1 (with the symmetric difference) otherwise.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean-bridge" / "ProofBroker" / "Alethe.lean"
ROCQ = ROOT / "rocq-bridge" / "src" / "alethe_walker.ml"

BEGIN = "PARITY:walker-rules BEGIN"
END = "PARITY:walker-rules END"
# A dispatch arm: leading `|`, a quoted rule name, then `->` (OCaml) or `=>` (Lean).
ARM = re.compile(r'^\s*\|\s*"([^"]+)"\s*(?:->|=>)')


def extract_rules(path: Path) -> set:
    """Return the set of rule-name literals dispatched between the markers."""
    text = path.read_text(encoding="utf-8")
    try:
        block = text.split(BEGIN, 1)[1].split(END, 1)[0]
    except IndexError:
        sys.exit(f"FAIL: parity markers ({BEGIN} / {END}) not found in {path}")
    rules = set()
    for line in block.splitlines():
        m = ARM.match(line)
        if m:
            rules.add(m.group(1))
    if not rules:
        sys.exit(f"FAIL: no dispatch arms found between markers in {path}")
    return rules


def main() -> int:
    lean = extract_rules(LEAN)
    rocq = extract_rules(ROCQ)
    if lean == rocq:
        print(f"OK: walkers agree on {len(lean)} Alethe rules: "
              f"{', '.join(sorted(lean))}")
        return 0
    print("FAIL: walker rule sets diverged.")
    missing_in_rocq = sorted(lean - rocq)
    missing_in_lean = sorted(rocq - lean)
    if missing_in_rocq:
        print(f"  in Lean, missing in Rocq: {', '.join(missing_in_rocq)}")
    if missing_in_lean:
        print(f"  in Rocq, missing in Lean: {', '.join(missing_in_lean)}")
    print(f"\nKeep {ROCQ.name} and {LEAN.name} dispatch tables in lockstep, "
          f"or update this check if the divergence is intentional.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
