#!/usr/bin/env python3
"""Walker rule-parity check (Lean walker <-> Rocq walker <-> SDK mint gate).

Three consumers dispatch on cvc5 alethe-2024 rule names: the two bridge
walkers elaborate traces per-rule, and the SDK's Tier-3 mint gate
(`Tier3_alethe.check_step`) decides whether a trace may become a Tier-3
cert at all. Soundness aside, the three dispatch tables must cover the
IDENTICAL set of rule names: a rule one walker lacks makes a trace close
on one bridge and fall through to the arithmetic fallback (omega / lia)
on the other, silently; a rule the SDK gate lacks makes the trace
unmintable on the live path even though both walkers replay it (the
pre-R1 24-vs-31 gap). This catches that drift.

SCOPE: compares the SET of rule-name string literals dispatched in each
consumer's step-dispatch match, extracted from between

    PARITY:walker-rules BEGIN  ...  PARITY:walker-rules END

markers in each source file. It does NOT verify that equally-named arms
behave identically -- that is what the snapshot tests + replay corpus +
the SDK's corpus-mintability sweep cover. Keeping the claim narrow is
the point: a cheap tripwire, not a proof of semantic parity.

Pure text extraction: no bridge build, no solver. Runs in CI and locally
(works even when the local Rocq/Lean toolchains are unavailable).

Exit 0 if the rule sets match, 1 (with the per-consumer gaps) otherwise.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean-bridge" / "ProofBroker" / "Alethe.lean"
ROCQ = ROOT / "rocq-bridge" / "src" / "alethe_walker.ml"
SDK = ROOT / "sdk" / "lib" / "tier3_alethe.ml"

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


SUPPORTED_RULES = re.compile(
    r'let\s+supported_rules\s*:\s*string\s+list\s*=\s*\[(.*?)\]', re.S)


def extract_supported_rules(path: Path = SDK) -> set:
    """Return the SDK minter's [Tier3_alethe.supported_rules] set.

    The mint gate ([proof_rules_supported]) consults this LIST, not the
    [check_step] dispatch arms -- anything derived from "what the minter
    mints" (e.g. coverage's mintable count) must read this source. Same
    textual-extraction trust model as [extract_rules]; the two sets are
    pinned equal (both directions) by test_walker_parity.
    """
    m = SUPPORTED_RULES.search(path.read_text(encoding="utf-8"))
    if not m:
        sys.exit(f"FAIL: supported_rules list not found in {path}")
    rules = set(re.findall(r'"([^"]+)"', m.group(1)))
    if not rules:
        sys.exit(f"FAIL: supported_rules list empty in {path}")
    return rules


def main() -> int:
    sets = {
        "Lean walker": extract_rules(LEAN),
        "Rocq walker": extract_rules(ROCQ),
        "SDK mint gate": extract_rules(SDK),
    }
    values = list(sets.values())
    if all(v == values[0] for v in values):
        print(f"OK: walkers + SDK mint gate agree on {len(values[0])} "
              f"Alethe rules: {', '.join(sorted(values[0]))}")
        return 0
    print("FAIL: rule sets diverged across the three consumers.")
    union = set().union(*values)
    for name, v in sets.items():
        missing = sorted(union - v)
        if missing:
            print(f"  missing in {name}: {', '.join(missing)}")
    print(f"\nKeep {LEAN.name}, {ROCQ.name} and {SDK.name} dispatch "
          f"tables in lockstep, or update this check if the divergence "
          f"is intentional.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
