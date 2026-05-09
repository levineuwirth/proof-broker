#!/usr/bin/env python3
"""Trust-footprint gate for `*_axiom_free` theorems.

Reads build output (from stdin or a file), parses both Lean's
`#print axioms` annotations and Rocq's `Print Assumptions` blocks,
and compares each allowlisted theorem against
`tools/axiom_allowlist.json`. Fails if any theorem grows beyond
its allowed axioms — the closure path silently started relying on
a new trust assumption — or disappears from the output entirely
(test removed without updating the allowlist).

Lean's #print axioms tags the theorem name in its output; Rocq's
Print Assumptions does not. To pair Rocq theorems with their
axiom signatures we rely on a `Print <name>.` line preceding each
`Print Assumptions <name>.` in the .v source — that emits a
`<name> = ...` marker in the build output the parser can anchor
on. The .v files under rocq-bridge/theories/ already follow this
convention; new ones must too if they want to be allowlisted.

The allowlist is a strict ceiling: actual axioms must be a subset
of allowed. Matching is by set, so axiom ordering in either
language's output doesn't matter. Theorems found in the build
output that aren't allowlisted are ignored — the gate cares about
declared axiom-free theorems, not every theorem in the world.

Usage:
    # Lean only (CI mode):
    lake build 2>&1 | python tools/check_axioms.py
    # Both bridges, locally:
    (lake build 2>&1; opam exec -- dune build rocq-bridge 2>&1) \\
        | python tools/check_axioms.py
    python tools/check_axioms.py --build-output build.log

CI integration: the validate.yml workflow runs the gate against
captured `lake build` output in the lean-bridge job. A rocq-bridge
job that builds the Rocq side under CI (rocq-runtime + cvc5/z3
install) doesn't exist yet; until it does, the Rocq parsing path
is dev-mode only. See RETROSPECTIVES/phase-4.md.
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


# Rocq's `Print <name>` emits a body line starting with `<name> = `;
# this is the marker we use to associate the subsequent
# `Print Assumptions` block with a theorem name. (Rocq's
# `Print Assumptions` alone doesn't include the name in its output.)
RE_ROCQ_MARKER = re.compile(r"^([A-Za-z_][\w'.]*) =\s*$")
# Inside an `Axioms:` block, each axiom name occupies a line of the
# form `<name> :` at column 0, with the axiom's type indented on
# subsequent lines. Block ends at end-of-input, a new marker line,
# a `Closed under` line, or an unindented non-matching line.
RE_ROCQ_AXIOM_NAME = re.compile(r"^([A-Za-z_][\w'.]*) :\s*$")
RE_ROCQ_CLOSED = re.compile(r"^Closed under the global context\s*$")
RE_ROCQ_AXIOMS_START = re.compile(r"^Axioms:\s*$")


def parse_rocq_axioms(text: str) -> dict[str, set[str]]:
    """Pair Rocq's Print + Print Assumptions output via marker lines.

    State machine:
      SEEKING        no current theorem; look for a `<name> =` marker.
      EXPECT_RESULT  marker seen; skip body / type / Arguments lines
                     until we hit `Closed under` or `Axioms:`.
      IN_AXIOMS      collecting axiom names from a multi-line block;
                     end on a new marker, `Closed under`, or an
                     unindented non-matching line.

    A `Print` without a corresponding `Print Assumptions` is
    silently ignored (the marker is dropped when the next
    interesting event arrives).
    """
    out: dict[str, set[str]] = {}
    state = "SEEKING"
    current_name: str | None = None
    axiom_set: set[str] | None = None

    def flush_axioms() -> None:
        nonlocal current_name, axiom_set
        if current_name is not None and axiom_set is not None:
            out[current_name] = axiom_set
        current_name = None
        axiom_set = None

    for line in text.splitlines():
        m_marker = RE_ROCQ_MARKER.match(line)
        m_closed = RE_ROCQ_CLOSED.match(line)
        m_ax_start = RE_ROCQ_AXIOMS_START.match(line)

        if state == "SEEKING":
            if m_marker:
                current_name = m_marker.group(1)
                state = "EXPECT_RESULT"
        elif state == "EXPECT_RESULT":
            if m_closed:
                if current_name is not None:
                    out[current_name] = set()
                current_name = None
                state = "SEEKING"
            elif m_ax_start:
                axiom_set = set()
                state = "IN_AXIOMS"
            elif m_marker:
                # Previous Print had no Print Assumptions; switch to new.
                current_name = m_marker.group(1)
            # else: skip body / type / Arguments lines.
        elif state == "IN_AXIOMS":
            m_ax = RE_ROCQ_AXIOM_NAME.match(line)
            if m_marker:
                flush_axioms()
                current_name = m_marker.group(1)
                state = "EXPECT_RESULT"
            elif m_closed:
                # Shouldn't normally appear mid-Axioms block; flush + restart.
                flush_axioms()
                state = "SEEKING"
            elif m_ax:
                if axiom_set is not None:
                    axiom_set.add(m_ax.group(1))
            elif line.startswith(" ") or not line.strip():
                # Type body or blank — part of the current axiom; skip.
                pass
            else:
                # Unrecognized non-indented line: assume the Axioms block
                # ended (e.g. the next vernac's output started). Flush.
                flush_axioms()
                state = "SEEKING"

    if state == "IN_AXIOMS":
        flush_axioms()
    return out


def load_allowlist(bridge: str, path: Path = ALLOWLIST_PATH) -> dict[str, set[str]]:
    """Load theorems from the allowlist filtered by bridge.

    [bridge] is one of "lean", "rocq", or "both". The allowlist
    JSON has top-level "lean" and "rocq" keys whose values are
    name → axiom-list dicts.
    """
    with path.open() as f:
        data = json.load(f)
    out: dict[str, set[str]] = {}
    if bridge in ("lean", "both"):
        for name, axs in data.get("lean", {}).items():
            out[name] = set(axs)
    if bridge in ("rocq", "both"):
        for name, axs in data.get("rocq", {}).items():
            out[name] = set(axs)
    return out


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
    p.add_argument(
        "--bridge", choices=["lean", "rocq", "both"], default="both",
        help="Which bridge's theorems to check. CI's lean-bridge job "
             "passes --bridge=lean (Rocq theorems aren't expected in "
             "its build output); rocq-bridge passes --bridge=rocq; "
             "default is both."
    )
    args = p.parse_args()

    if args.build_output is not None:
        text = args.build_output.read_text()
    else:
        text = sys.stdin.read()

    actual: dict[str, set[str]] = {}
    if args.bridge in ("lean", "both"):
        actual.update(parse_lean_axioms(text))
    if args.bridge in ("rocq", "both"):
        # Rocq parser keys are unqualified; Lean keys are qualified.
        # On the off chance both parsers find the same name (shouldn't
        # happen in practice), Lean's parse already sat in [actual]
        # and rocq's would overwrite — guard with no-overwrite.
        rocq = parse_rocq_axioms(text)
        for name, axs in rocq.items():
            actual.setdefault(name, axs)

    if not actual:
        # No axiom-related output at all. That's suspicious — either
        # the build didn't run the relevant theorems or the parser(s)
        # regressed against an output-format change.
        print(
            f"FAIL: no axiom output found in input for bridge="
            f"{args.bridge}. The build probably didn't run, or output "
            f"formats changed.",
            file=sys.stderr,
        )
        return 1

    allowed = load_allowlist(args.bridge, path=args.allowlist)

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
