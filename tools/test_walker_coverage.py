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


def _with_index(index: dict, supported: set, skips: dict | None = None,
                gate: set | None = None):
    """Point cov at a synthetic index + supported set (+ optional replay_skip
    goal files; `gate` overrides the minter's supported_rules, default =
    `supported`), return compute()."""
    d = Path(tempfile.mkdtemp())
    idx = d / "index.json"
    idx.write_text(json.dumps(index), encoding="utf-8")
    goals = d / "goals"
    goals.mkdir()
    for gid, reason in (skips or {}).items():
        (goals / f"{gid}.json").write_text(
            json.dumps({"id": gid, "replay_skip": reason}), encoding="utf-8")
    orig = (cov.INDEX, cov.GOALS, cov.parity.extract_rules,
            cov.parity.extract_supported_rules)
    cov.INDEX, cov.GOALS = idx, goals
    cov.parity.extract_rules = lambda _path: set(supported)
    cov.parity.extract_supported_rules = (
        lambda _path=None: set(supported if gate is None else gate))
    try:
        return cov.compute()
    finally:
        (cov.INDEX, cov.GOALS, cov.parity.extract_rules,
         cov.parity.extract_supported_rules) = orig


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
    _ok(rep["summary"] == {"walkable": 1, "replayed": 1, "shape_gapped": 0,
                           "unsat": 2, "total": 2, "non_unsat": []},
        "summary counts")


def test_shape_gap_splits_walkable() -> None:
    rep = _with_index(
        {
            "g_replay": {"result": "unsat", "rules": ["or"]},
            "g_gap": {"result": "unsat", "rules": ["or"]},
        },
        supported={"or"},
        skips={"g_gap": "supported rule, unhandled shape"},
    )
    # Both statically walkable; one is replay_skip'd -> shape-gapped.
    _ok(rep["summary"]["walkable"] == 2, "both statically walkable")
    _ok(rep["summary"]["replayed"] == 1 and rep["summary"]["shape_gapped"] == 1,
        "skip splits walkable into replayed + shape_gapped")
    _ok(rep["goals"]["g_gap"]["replay_skip"] == "supported rule, unhandled shape",
        "skip reason surfaced per goal")


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


def test_mintable_counts() -> None:
    rep = _with_index(
        {
            "g_in": {"result": "unsat", "rules": ["or", "resolution"]},
            "g_out": {"result": "unsat", "rules": ["or", "xor"]},
        },
        supported={"or", "resolution"},
    )
    _ok(rep["mintable"] == 1, "mintable counts SDK-gate-subset traces")
    _ok(rep["goals"]["g_in"]["mintable"] is True
        and rep["goals"]["g_out"]["mintable"] is False,
        "per-goal mintable flags")


def test_mintable_follows_minter_gate_not_arms() -> None:
    # mintable derives from the minter's supported_rules list, NOT the
    # check_step dispatch arms: a rule dispatched by an arm but absent
    # from supported_rules must not count as mintable (the minter would
    # never mint it -- overcounting was R1 ROUND 1 finding 5).
    rep = _with_index(
        {
            "g_gate": {"result": "unsat", "rules": ["or"]},
            "g_arm_only": {"result": "unsat", "rules": ["or", "xor"]},
        },
        supported={"or", "xor"},   # walker/dispatch arms (xor gate-less)
        gate={"or"},               # the minter's supported_rules
    )
    _ok(rep["goals"]["g_arm_only"]["walkable"] is True
        and rep["goals"]["g_arm_only"]["mintable"] is False,
        "arm-dispatched but gate-less rule -> walkable, not mintable")
    _ok(rep["mintable"] == 1 and rep["goals"]["g_gate"]["mintable"] is True,
        "mintable counts only supported_rules-subset traces")


def main() -> int:
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            fn()
    print(f"\n{_PASS} passed, {_FAIL} failed")
    return 1 if _FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
