#!/usr/bin/env python3
"""Tests for fuzz_resolution -- including a negative control proving the
fuzzer actually detects the dedup bug it guards against.

Pure stdlib; run directly (`python tools/test_fuzz_resolution.py`).
"""
from __future__ import annotations

import contextlib
import io
import random
import sys

import fuzz_resolution as fz

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


def test_binary_resolve_dedups() -> None:
    # (1 ∨ 2) resolved with (1 ∨ -2) on 2/-2 -> (1 ∨ 1) -> dedup (1).
    _ok(fz.binary_resolve([1, 2], [1, -2]) == [1], "shared literal deduped")
    # No pivot -> None.
    _ok(fz.binary_resolve([1, 2], [1, 2]) is None, "no pivot -> None")


def test_oracle_unsat() -> None:
    _ok(fz.is_unsat([[1, 2], [1, -2], [-1]]), "classic refutation is unsat")
    _ok(not fz.is_unsat([[1, 2], [-1]]), "satisfiable set is not unsat")


def test_resolve_chain_reaches_empty() -> None:
    _ok(fz.resolve_chain([[1, 2], [1, -2], [-1]]) == [],
        "deduping fold reaches the empty clause")


def test_properties_hold_on_correct_algorithm() -> None:
    fz._PASS, fz._FAIL = 0, 0
    fz.fuzz(random.Random(1), rounds=2000)
    fz.regression_dedup_matters()
    _ok(fz._FAIL == 0, "all properties hold on the correct algorithm")


def test_fuzzer_catches_dedup_bug() -> None:
    # Negative control: reintroduce the pigeonhole bug (resolvent without
    # dedup) and confirm the property suite fires. A guard that can't fail
    # is worthless -- this proves it can.
    orig = fz.binary_resolve

    def buggy(a, b):
        piv = fz.first_pivot(a, b)
        if piv is None:
            return None
        i, j = piv
        return [x for k, x in enumerate(a) if k != i] \
            + [x for k, x in enumerate(b) if k != j]

    fz.binary_resolve = buggy
    fz._PASS, fz._FAIL = 0, 0
    try:
        # The buggy run intentionally trips the property suite; swallow its
        # per-violation chatter so the test log stays clean.
        with contextlib.redirect_stdout(io.StringIO()):
            fz.fuzz(random.Random(2), rounds=2000)
    finally:
        fz.binary_resolve = orig
    _ok(fz._FAIL > 0, "fuzzer detects the no-dedup regression")


def main() -> int:
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            fn()
    print(f"\n{_PASS} passed, {_FAIL} failed")
    return 1 if _FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
