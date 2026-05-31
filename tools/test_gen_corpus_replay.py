#!/usr/bin/env python3
"""Tests for gen_corpus_replay's escaping + skip handling.

Pure stdlib; run directly (`python tools/test_gen_corpus_replay.py`).
"""
from __future__ import annotations

import sys

import gen_corpus_replay as gen

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


def test_coq_escape_doubles_quotes() -> None:
    _ok(gen.coq_escape('a "b" c') == 'a ""b"" c', "quotes doubled for Coq")
    _ok(gen.coq_escape("no quotes") == "no quotes", "no-op without quotes")


def test_real_v_matches_committed() -> None:
    # The committed CorpusReplay.v must be in sync with the corpus fixtures
    # (this is exactly what CI's --check enforces).
    _ok(gen.OUT.read_text(encoding="utf-8") == gen.render(),
        "committed CorpusReplay.v matches generator output")


def main() -> int:
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            fn()
    print(f"\n{_PASS} passed, {_FAIL} failed")
    return 1 if _FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
