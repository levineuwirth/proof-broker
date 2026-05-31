#!/usr/bin/env python3
"""Tests for check_walker_coverage's classification + backlog.

Drives compute() over a synthetic index with a pinned supported-rule set,
so the walkable/fell-through logic is covered without depending on the real
corpus or walker. Pure stdlib; run directly
(`python tools/test_walker_coverage.py`) -- exits non-zero on first failure.
"""
from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

import check_walker_coverage as cov

_PASS = 0
_FAIL = 0


def _ok(cond: bool, label: str) -> None:
    global _PASS, _FAIL
    if cond:
        _PASS += 1
        print(f"PASS  {label}")
    else:
        _FAIL += 1
        print(f"FAIL  {label}")


def _with_index(index: dict, supported: set):
    """Point cov at a synthetic index + supported-rule set, return compute()."""
    d = Path(tempfile.mkdtemp())
    idx = d / "index.json"
    idx.write_text(json.dumps(index), encoding="utf-8")
    orig_index, orig_extract = cov.INDEX, cov.parity.extract_rules
    cov.INDEX = idx
    cov.parity.extract_rules = lambda _path: set(supported)
    try:
        return cov.compute()
    finally:
        cov.INDEX, cov.parity.extract_rules = orig_index, orig_extract


def test_walkable_and_blocked() -> None:
    rep = _with_index(
        {
            "g_ok": {"result": "unsat", "rules": ["or", "resolution"]},
            "g_block": {"result": "unsat", "rules": ["or", "subproof", "xor"]},
        },
        supported={"or", "resolution"},
    )
    _ok(rep["goals"]["g_ok"]["walkable"] is True, "all-supported -> walkable")
    _ok(rep["goals"]["g_block"]["walkable"] is False, "missing rule -> blocked")
    _ok(rep["goals"]["g_block"]["missing"] == ["subproof", "xor"],
        "missing rules sorted")
    _ok(rep["summary"] == {"walkable": 1, "unsat": 2, "total": 2, "non_unsat": []},
        "summary counts")


def test_backlog_ranked_by_blocking_count() -> None:
    rep = _with_index(
        {
            "a": {"result": "unsat", "rules": ["subproof"]},
            "b": {"result": "unsat", "rules": ["subproof", "xor"]},
        },
        supported=set(),
    )
    # subproof blocks 2 goals, xor blocks 1 -> subproof ranks first.
    _ok(list(rep["backlog"].items()) == [("subproof", 2), ("xor", 1)],
        "backlog ranked by goals-blocked desc")


def test_non_unsat_flagged() -> None:
    rep = _with_index(
        {"sat_goal": {"result": "sat"}},
        supported={"or"},
    )
    _ok(rep["summary"]["non_unsat"] == ["sat_goal"], "non-unsat surfaced")
    _ok(rep["summary"]["walkable"] == 0 and rep["summary"]["unsat"] == 0,
        "non-unsat excluded from walkable/unsat counts")


def main() -> int:
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            fn()
    print(f"\n{_PASS} passed, {_FAIL} failed")
    return 1 if _FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
