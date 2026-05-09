#!/usr/bin/env python3
"""Trust-footprint gate for Lean-side `*_axiom_free` theorems.

Reads `lake build` output (from stdin or a file), parses Lean's
`#print axioms` annotations, and compares each allowlisted theorem
against `tools/axiom_allowlist.json`. Fails if any theorem grows
beyond its allowed axioms — the closure path silently started
relying on a new trust assumption — or disappears from the output
entirely (test removed without updating the allowlist).

The allowlist is a strict ceiling: actual axioms must be a subset
of allowed. Matching is by set, so axiom ordering in Lean's output
doesn't matter. Theorems found in the build output that aren't
allowlisted are ignored — the gate cares about declared axiom-free
theorems, not every theorem in the world.

Rocq isn't checked here. Rocq's `Print Assumptions` doesn't tag
the theorem name in its output (it prints "Closed under the
global context" or "Axioms: ..." with no preamble identifier),
so a positional pairing against the .v source would be the only
way. Deferred to a future iteration; the Rocq side's `Print
Assumptions` lines remain present in build output for human
inspection. See RETROSPECTIVES/phase-4.md.

Usage:
    lake build 2>&1 | python tools/check_axioms.py
    python tools/check_axioms.py < build.log
    python tools/check_axioms.py --build-output build.log
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
ALLOWLIST_PATH = REPO_ROOT / "tools" / "axiom_allowlist.json"


# Lean's `#print axioms <name>` emits one of two info-level lines.
# The "depends on axioms" form lists axioms inside `[...]`,
# comma-separated. The "does not depend on any axioms" form is the
# axiom-free signal.
RE_AXIOMS_LIST = re.compile(
    r"'(?P<name>\S+)' depends on axioms: \[(?P<axs>[^\]]*)\]"
)
RE_AXIOMS_NONE = re.compile(
    r"'(?P<name>\S+)' does not depend on any axioms"
)


def parse_lean_axioms(text: str) -> dict[str, set[str]]:
    """Map theorem-name → set of axioms (empty for "does not depend")."""
    out: dict[str, set[str]] = {}
    for m in RE_AXIOMS_LIST.finditer(text):
        axs = {
            a.strip()
            for a in m.group("axs").split(",")
            if a.strip()
        }
        out[m.group("name")] = axs
    for m in RE_AXIOMS_NONE.finditer(text):
        out[m.group("name")] = set()
    return out


def load_allowlist() -> dict[str, set[str]]:
    with ALLOWLIST_PATH.open() as f:
        data = json.load(f)
    return {
        name: set(axs)
        for name, axs in data.get("theorems", {}).items()
    }


def check(actual: dict[str, set[str]],
          allowed: dict[str, set[str]]) -> list[str]:
    """Return a list of error strings (empty on success)."""
    errors: list[str] = []
    for name, allowed_axs in allowed.items():
        if name not in actual:
            errors.append(
                f"missing: '{name}' is in the allowlist but no #print "
                f"axioms output found for it (theorem renamed or "
                f"deleted without updating tools/axiom_allowlist.json?)"
            )
            continue
        actual_axs = actual[name]
        extra = actual_axs - allowed_axs
        if extra:
            errors.append(
                f"trust-footprint regression on '{name}': "
                f"actual axioms = {sorted(actual_axs)}; "
                f"allowed = {sorted(allowed_axs)}; "
                f"new (must justify or revise allowlist) = {sorted(extra)}"
            )
        # Allowed-but-not-actual is fine — the closer got tighter, not looser.
    return errors


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--build-output", "-o", type=Path,
        help="Path to a captured build log; stdin used if omitted."
    )
    p.add_argument(
        "--allowlist", type=Path, default=ALLOWLIST_PATH,
        help="Path to the allowlist JSON. Defaults to tools/axiom_allowlist.json."
    )
    args = p.parse_args()

    if args.build_output is not None:
        text = args.build_output.read_text()
    else:
        text = sys.stdin.read()

    actual = parse_lean_axioms(text)
    if not actual:
        # No #print axioms output at all. That's suspicious — either
        # the build didn't run the relevant theorems or the parser
        # regressed against an output-format change.
        print(
            "FAIL: no #print axioms output found in input. The build "
            "probably didn't run, or Lean's output format changed.",
            file=sys.stderr,
        )
        return 1

    if args.allowlist != ALLOWLIST_PATH:
        with args.allowlist.open() as f:
            data = json.load(f)
        allowed = {
            name: set(axs)
            for name, axs in data.get("theorems", {}).items()
        }
    else:
        allowed = load_allowlist()

    errors = check(actual, allowed)
    if errors:
        print(
            f"FAIL: axiom-check found {len(errors)} regression(s):",
            file=sys.stderr,
        )
        for e in errors:
            print(f"  * {e}", file=sys.stderr)
        return 1

    print(
        f"OK: all {len(allowed)} allowlisted theorem(s) within their "
        f"axiom ceiling.",
        file=sys.stderr,
    )
    for name, axs in sorted(allowed.items()):
        actual_axs = actual.get(name, set())
        if axs:
            print(
                f"  {name}: {sorted(actual_axs)} "
                f"(allowed: {sorted(axs)})",
                file=sys.stderr,
            )
        else:
            print(f"  {name}: axiom-free", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
