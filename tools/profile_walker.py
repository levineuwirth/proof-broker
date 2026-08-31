#!/usr/bin/env python3
"""Walker scale profile + gate.

The Alethe walker reconstructs a kernel proof term step-by-step from a
cvc5 trace. Its cost is dominated by two structural quantities, both
read straight off the committed trace:

  * ARITHMETIC LEAVES (`la_generic` / `la_mult_neg` / `hole` /
    `rare_rewrite`) -- each is discharged by an independent decision
    procedure call (Coq `lia` / Lean `omega`, with a `propext`-iff
    fallback for Prop-equality holes). These dominate wall-clock:
    reconstruction time tracks the leaf count far more tightly than
    the raw step count.
  * STEPS -- each non-leaf step builds one kernel sub-term (resolution
    cascades, congruence, the boolean cluster). Cheap individually,
    but the count sets the term size the kernel must re-check.

This tool turns those into a committed, reviewable profile across the
corpus size gradient (a few steps up to the ~600-step pigeonhole), so
a trace-complexity regression -- a refreshed cvc5 emitting a heavier
proof, or a new goal that balloons the leaf count -- shows up as a
diff rather than a silent slowdown. It is solver-free and
deterministic: structure only, no reconstruction is run here. The
no in-repo wall-clock baseline exists yet (in-build timings are a
decide-list item); the dynamic replay (CorpusReplay.v under coqc, the
generated live-strict CorpusWalkerLive suites on both bridges) is where
reconstruction actually happens in CI.

Modes:
  (default)  print the human-readable scale profile table.
  --check    recompute and compare against committed corpus/profile.json;
             exit 1 on any difference (so profile changes are reviewed).
  --write    (re)generate corpus/profile.json from the current traces.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TRACES = ROOT / "corpus" / "traces"
INDEX = ROOT / "corpus" / "index.json"
PROFILE = ROOT / "corpus" / "profile.json"

# Rules cvc5 emits as proof leaves: each is re-derived by a decision
# procedure (lia/omega) rather than by kernel term assembly.
LEAF_RULES = frozenset(
    {"la_generic", "la_mult_neg", "hole", "rare_rewrite"})

_RULE = re.compile(r":rule\s+([a-z_0-9]+)")
_STEP = re.compile(r"\(step\s")
_ASSUME = re.compile(r"\(assume\s")
_ANCHOR = re.compile(r"\(anchor\b")


def profile_trace(text: str) -> dict:
    """Structural cost-predictor metrics for one Alethe trace."""
    rules = _RULE.findall(text)
    histogram: dict[str, int] = {}
    for r in rules:
        histogram[r] = histogram.get(r, 0) + 1
    leaves = sum(n for r, n in histogram.items() if r in LEAF_RULES)
    return {
        "steps": len(_STEP.findall(text)),
        "assumes": len(_ASSUME.findall(text)),
        "subproofs": len(_ANCHOR.findall(text)),
        "rule_apps": len(rules),
        "distinct_rules": len(histogram),
        "arith_leaves": leaves,
        "resolution": histogram.get("resolution", 0),
    }


def compute() -> dict:
    index = json.loads(INDEX.read_text(encoding="utf-8"))
    goals = {}
    for gid, entry in index.items():
        if entry.get("result") != "unsat":
            continue
        trace = TRACES / f"{gid}.alethe"
        if not trace.exists():
            continue
        goals[gid] = profile_trace(trace.read_text(encoding="utf-8"))
    totals = {
        "goals": len(goals),
        "steps": sum(g["steps"] for g in goals.values()),
        "arith_leaves": sum(g["arith_leaves"] for g in goals.values()),
        "max_steps": max((g["steps"] for g in goals.values()), default=0),
        "max_arith_leaves":
            max((g["arith_leaves"] for g in goals.values()), default=0),
    }
    return {"goals": goals, "totals": totals}


def render(report: dict) -> str:
    goals = report["goals"]
    t = report["totals"]
    rows = sorted(goals.items(), key=lambda kv: (kv[1]["steps"], kv[0]))
    w = max((len(g) for g in goals), default=4)
    lines = [
        f"Walker scale profile: {t['goals']} unsat corpus traces, "
        f"{t['steps']} steps / {t['arith_leaves']} arithmetic leaves total.",
        "(arithmetic leaves drive reconstruction wall-clock -- one "
        "decision-procedure call each)",
        "",
        f"  {'goal':<{w}}  steps  leaves  subpf  resol  rules",
    ]
    for gid, g in rows:
        lines.append(
            f"  {gid:<{w}}  {g['steps']:>5}  {g['arith_leaves']:>6}  "
            f"{g['subproofs']:>5}  {g['resolution']:>5}  "
            f"{g['distinct_rules']:>5}")
    lines.append("")
    lines.append(
        f"  widest: {t['max_steps']} steps, "
        f"{t['max_arith_leaves']} arithmetic leaves.")
    return "\n".join(lines)


def main(argv: list) -> int:
    mode = argv[1] if len(argv) > 1 else ""
    report = compute()

    if mode == "--write":
        PROFILE.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print(f"wrote {PROFILE.relative_to(ROOT)}")
        print(render(report))
        return 0

    if mode == "--check":
        if not PROFILE.exists():
            print(f"FAIL: {PROFILE} missing; run profile_walker.py --write")
            return 1
        committed = json.loads(PROFILE.read_text(encoding="utf-8"))
        if committed == report:
            print(render(report))
            print("\nOK: scale profile matches committed baseline.")
            return 0
        print("FAIL: scale profile drifted from committed corpus/profile.json.")
        print("--- computed ---")
        print(render(report))
        print("\nRegenerate with: python tools/profile_walker.py --write "
              "(and review the diff).")
        return 1

    print(render(report))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
