#!/usr/bin/env python3
"""Walker replay-coverage report + gate.

Measures how much of the cvc5 LIA+UF fragment the Alethe walker actually
replays, by comparing each corpus trace's rule inventory (corpus/index.json,
produced by sdk/bin/corpus_gen on live cvc5) against the walker's supported
rule set (extracted from the Rocq dispatch table, the same source the
parity check uses).

A trace is STATICALLY WALKABLE iff every rule it uses has a walker dispatch
arm. That is a necessary condition, not a sufficient one (a supported rule
in an unhandled shape can still fail) -- the dynamic replay (CorpusReplay.v,
compiled under coqc in CI) is the ground-truth check for the walkable set.
This tool is the cheap, solver-free static layer: it turns "we cover the
fragment" into a measured fraction and a ranked backlog of the rules that
block the rest.

Modes:
  (default)  print the human-readable coverage report.
  --check    recompute and compare against the committed corpus/coverage.json;
             exit 1 on any difference (so coverage changes are reviewed diffs).
  --write    (re)generate corpus/coverage.json from the current index + walker.

corpus/coverage.json is the committed baseline. It changes when the corpus
grows, when cvc5 emits different rules (refreshed via corpus_gen), or when
the walker learns/loses a rule -- each a deliberate, reviewable diff.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import check_walker_parity as parity

ROOT = Path(__file__).resolve().parent.parent
INDEX = ROOT / "corpus" / "index.json"
COVERAGE = ROOT / "corpus" / "coverage.json"


def compute() -> dict:
    """Classify every corpus goal against the walker's supported rule set."""
    supported = parity.extract_rules(parity.ROCQ)
    index = json.loads(INDEX.read_text(encoding="utf-8"))

    goals = {}
    backlog: dict[str, int] = {}
    walkable = 0
    unsat = 0
    nonunsat = []
    for gid in sorted(index):
        entry = index[gid]
        result = entry.get("result")
        if result != "unsat":
            nonunsat.append(gid)
            goals[gid] = {"result": result, "walkable": False, "missing": []}
            continue
        unsat += 1
        rules = set(entry.get("rules", []))
        missing = sorted(rules - supported)
        is_walkable = not missing
        if is_walkable:
            walkable += 1
        else:
            for r in missing:
                backlog[r] = backlog.get(r, 0) + 1
        goals[gid] = {
            "result": "unsat",
            "walkable": is_walkable,
            "missing": missing,
        }

    return {
        "supported_rule_count": len(supported),
        "summary": {
            "walkable": walkable,
            "unsat": unsat,
            "total": len(index),
            "non_unsat": sorted(nonunsat),
        },
        # backlog: unsupported rule -> number of corpus goals it blocks,
        # sorted by blocking-count desc then name (the ranked rule backlog).
        "backlog": dict(sorted(backlog.items(), key=lambda kv: (-kv[1], kv[0]))),
        "goals": goals,
    }


def render(report: dict) -> str:
    s = report["summary"]
    lines = [
        f"Walker replay coverage: {s['walkable']}/{s['unsat']} unsat traces "
        f"statically walkable "
        f"({report['supported_rule_count']} rules supported).",
        "",
    ]
    for gid in sorted(report["goals"]):
        g = report["goals"][gid]
        if g["result"] != "unsat":
            lines.append(f"  ?  {gid:<22} result={g['result']} (not unsat)")
        elif g["walkable"]:
            lines.append(f"  OK {gid:<22} walkable")
        else:
            lines.append(f"  -- {gid:<22} blocked by: {', '.join(g['missing'])}")
    if report["backlog"]:
        lines.append("")
        lines.append("Ranked rule backlog (unsupported rule -> goals blocked):")
        for rule, n in report["backlog"].items():
            lines.append(f"  {n:>3}  {rule}")
    if report["summary"]["non_unsat"]:
        lines.append("")
        lines.append("WARNING: non-unsat corpus goals (mis-authored or "
                     f"solver gap): {', '.join(report['summary']['non_unsat'])}")
    return "\n".join(lines)


def main(argv: list) -> int:
    mode = argv[1] if len(argv) > 1 else ""
    report = compute()

    if mode == "--write":
        COVERAGE.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print(f"wrote {COVERAGE.relative_to(ROOT)}")
        print(render(report))
        return 0

    if mode == "--check":
        if not COVERAGE.exists():
            print(f"FAIL: {COVERAGE} missing; run check_walker_coverage.py --write")
            return 1
        committed = json.loads(COVERAGE.read_text(encoding="utf-8"))
        if committed == report:
            print(render(report))
            print("\nOK: coverage matches committed baseline.")
            return 0
        print("FAIL: coverage drifted from committed corpus/coverage.json.")
        print("--- computed ---")
        print(render(report))
        print("\nRegenerate with: python tools/check_walker_coverage.py --write "
              "(and review the diff).")
        return 1

    print(render(report))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
