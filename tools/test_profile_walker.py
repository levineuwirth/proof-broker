#!/usr/bin/env python3
"""Tests for profile_walker's per-trace structural metrics.

Drives profile_trace() over hand-built Alethe trace snippets so the
cost-predictor counting (steps / arithmetic leaves / subproofs /
resolution) is covered without depending on the real corpus. Pure
stdlib; run directly (`python tools/test_profile_walker.py`) -- exits
non-zero on first failure.
"""
from __future__ import annotations

import sys

import profile_walker as pw

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


def test_counts_basic() -> None:
    trace = (
        "(\n"
        "(assume a0 (<= x 3))\n"
        "(assume a1 (not false))\n"
        "(step t0 (cl (not (<= x 4)) (<= x 3)) :rule la_generic :args (1/1))\n"
        "(step t1 (cl (<= x 3)) :rule resolution :premises (t0 a0))\n"
        "(step t2 (cl) :rule resolution :premises (t1 a1))\n"
        ")\n"
    )
    m = pw.profile_trace(trace)
    _ok(m["steps"] == 3, "steps counted")
    _ok(m["assumes"] == 2, "assumes counted")
    _ok(m["resolution"] == 2, "resolution applications counted")
    _ok(m["arith_leaves"] == 1, "la_generic counted as arithmetic leaf")
    _ok(m["subproofs"] == 0, "no anchors -> zero subproofs")
    _ok(m["rule_apps"] == 3, "total rule applications counted")
    _ok(m["distinct_rules"] == 2, "distinct rules counted")


def test_leaf_rules_all_counted() -> None:
    trace = (
        "(step t0 (cl a) :rule hole :args (\"TRUST_THEORY_REWRITE\"))\n"
        "(step t1 (cl b) :rule rare_rewrite :args (\"evaluate\"))\n"
        "(step t2 (cl c) :rule la_mult_neg)\n"
        "(step t3 (cl d) :rule la_generic :args (1/1))\n"
        "(step t4 (cl e) :rule resolution :premises (t0 t1))\n"
    )
    m = pw.profile_trace(trace)
    _ok(m["arith_leaves"] == 4,
        "hole + rare_rewrite + la_mult_neg + la_generic are leaves")
    _ok(m["resolution"] == 1, "resolution not counted as a leaf")


def test_subproof_anchors_counted() -> None:
    trace = (
        "(anchor :step t1)\n"
        "(assume t1.a0 p)\n"
        "(step t1.t0 (cl q) :rule hole)\n"
        "(step t1 (cl q) :rule subproof :discharge (t1.a0))\n"
        "(anchor :step t2 :args ((x Int) (:= (x Int) x)))\n"
        "(step t2.t0 (cl r) :rule hole)\n"
        "(step t2 (cl r) :rule bind)\n"
    )
    m = pw.profile_trace(trace)
    _ok(m["subproofs"] == 2, "both anchors (plain + binder) counted")


def main() -> int:
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            fn()
    print(f"\n{_PASS} passed, {_FAIL} failed")
    return 1 if _FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
