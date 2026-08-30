#!/usr/bin/env python3
"""Tests for status_table.py — the README doc-count gate.

The gate's job is to make a hand-edited or stale README fail the schemas
job, so the tests are mostly negative controls: a tampered embedded
table fails `--check`, missing markers fail `--check`, and the numbers in
the rendered table are the ones in the JSON sources (not typed
constants). Pure stdlib; run directly (`python tools/test_status_table.py`).
"""
from __future__ import annotations

import json
import sys

import status_table as st

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


def test_counts_come_from_sources() -> None:
    d = st.collect()
    allow = json.loads(st.ALLOWLIST.read_text(encoding="utf-8"))
    index = json.loads(st.INDEX.read_text(encoding="utf-8"))
    cov = json.loads(st.COVERAGE.read_text(encoding="utf-8"))
    _ok(d["trust"]["lean"]["theorems"] == len(allow["lean"]),
        "Lean theorem count == len(allowlist.lean)")
    _ok(d["trust"]["rocq"]["theorems"] == len(allow["rocq"]),
        "Rocq theorem count == len(allowlist.rocq)")
    lean_ax = set()
    for v in allow["lean"].values():
        lean_ax.update(v)
    _ok(d["trust"]["lean"]["axioms"] == sorted(lean_ax),
        "Lean distinct axioms == union over allowlist entries")
    _ok(d["corpus"]["goals"] == len(index), "corpus goals == len(index.json)")
    _ok(d["corpus"]["steps"] == sum(g["steps"] for g in index.values()),
        "corpus steps == sum(index.json steps)")
    _ok(d["corpus"]["supported_rule_count"] == cov["supported_rule_count"],
        "supported_rule_count read from coverage.json")
    _ok(d["walker"]["lean"] == cov["supported_rule_count"]
        and d["walker"]["parity"],
        "walker rule count (parity extraction) agrees with coverage.json")
    _ok("mintable" in cov or d["corpus"]["mintable"] is None,
        "mintable reported only when coverage.json carries it")
    table = st.render(d)
    for needle in (str(len(allow["lean"])), str(len(allow["rocq"])),
                   str(len(index)), str(cov["supported_rule_count"])):
        _ok(needle in table, f"rendered table contains source-derived {needle!r}")


def test_ci_jobs_regex() -> None:
    text = """\
name: x
on:
  push:
  schedule:
    - cron: "1 2 * * 3"
jobs:
  alpha:
    runs-on: ubuntu-latest
    timeout-minutes: 7
    steps:
      - run: echo
        env:
          CVC5_VERSION: "9.9.9"
  beta:
    runs-on: ubuntu-latest
    steps: []
"""
    ci = st.ci_jobs(text)
    _ok(list(ci["jobs"].items()) == [("alpha", 7), ("beta", None)],
        "ci_jobs: names in order, timeout or None")
    _ok(ci["pins"] == {"CVC5_VERSION": ["9.9.9"]}, "ci_jobs: env pins collected")
    _ok(ci["cron"] == "1 2 * * 3", "ci_jobs: cron line collected")
    real = st.ci_jobs(st.WORKFLOW.read_text(encoding="utf-8"))
    _ok(set(real["jobs"]) >= {"schemas", "sdk", "sdk-cross-platform",
                              "lean-bridge", "rocq-bridge", "ci-status"},
        "real validate.yml: the six jobs are found")
    _ok(all(t is not None for t in real["jobs"].values()),
        "real validate.yml: every job has timeout-minutes")


def test_check_negative_controls() -> None:
    table = st.render(st.collect())
    good = "intro\n" + st.block(table) + "\noutro\n"
    _ok(st.check(good, table) == 0, "--check passes on an up-to-date block")
    # Tamper one digit inside the embedded table: must fail.
    import re
    m = re.search(r"\d", st.block(table))
    tampered = good.replace(st.block(table),
                            st.block(table[:m.start()] + ("7" if m.group() != "7" else "8")
                                     + table[m.start() + 1:]), 1)
    _ok(st.check(tampered, table) == 1, "--check fails on a tampered digit")
    _ok(st.check("no markers here\n", table) == 1, "--check fails without markers")
    # --write round-trips: writing then checking passes.
    stale = "intro\n" + st.block("| stale |\n") + "\noutro\n"
    _ok(st.check(st.write(stale, table), table) == 0,
        "write() then check() passes")
    _ok(st.write(stale, table).startswith("intro\n")
        and st.write(stale, table).endswith("\noutro\n"),
        "write() preserves the text around the block")


def main() -> int:
    test_counts_come_from_sources()
    test_ci_jobs_regex()
    test_check_negative_controls()
    print(f"\n{_PASS} passed, {_FAIL} failed")
    return 1 if _FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
