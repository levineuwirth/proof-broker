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


def test_version_note_declared_vs_pinned() -> None:
    # Synthetic inputs: the mismatch list is derived, not typed.
    bes = [("cvc5", "1.3.3", [0, 1], []), ("vampire", "5.0.1", [0], []),
           ("z3", "4.16.0", [0, 1], [])]
    pins = {"CVC5_VERSION": ["1.3.0"], "VAMPIRE_VERSION": ["v5.0.1"]}
    _ok(st.declared_vs_pinned(bes, pins) == [("cvc5", "1.3.3", "1.3.0")],
        "declared_vs_pinned: cvc5 1.3.3 vs pin 1.3.0 is reported")
    _ok(st.declared_vs_pinned(bes, {"CVC5_VERSION": ["1.3.3"],
                                    "VAMPIRE_VERSION": ["v5.0.1"]}) == [],
        "declared_vs_pinned: equal versions yield no mismatch")
    _ok(st.declared_vs_pinned([("vampire", "5.0.1", [0], [])],
                              {"VAMPIRE_VERSION": ["v5.0.1"]}) == [],
        "declared_vs_pinned: a leading 'v' on the pin is not a mismatch")
    _ok(st.declared_vs_pinned([("z3", "4.16.0", [0, 1], [])], pins) == [],
        "declared_vs_pinned: a backend without a CI env pin is skipped")
    _ok(st.declared_vs_pinned(bes, {"CVC5_VERSION": ["1.3.0", "1.3.3"]})
        == [], "declared_vs_pinned: any job's pin equal to the declared version counts")
    # Real sources: the note names exactly the drift the sources show.
    d = st.collect()
    real = st.declared_vs_pinned(d["backends"], d["ci"]["pins"])
    recomputed = []
    for m in st.MANIFESTS:
        name = m.stem.removeprefix("manifest-")
        declared = str(json.loads(m.read_text(encoding="utf-8"))["adapter_version"])
        pinned = d["ci"]["pins"].get(f"{name.upper()}_VERSION")
        if pinned and declared not in {p.removeprefix("v") for p in pinned}:
            recomputed.append((name, declared, "/".join(pinned)))
    _ok(real == recomputed, "real sources: mismatch list == manifests vs validate.yml pins")
    table = st.render(d)
    note = st.version_note(d)
    _ok(note in table and table.index(note) > table.rindex("| "),
        "rendered block carries the version note after the table")
    _ok("\n\n" in table[:table.index(note)],
        "a blank line separates the table from the note (markdown)")
    for name, dec, pin in real:
        _ok(f"{name} (declared {dec}, pinned {pin})" in note,
            f"note lists the real drift entry {name} (declared {dec}, pinned {pin})")
    if not real:
        _ok("declares the pinned version" in note, "note says there is no drift")
    # A synthetic no-drift collection renders the no-drift sentence.
    same = dict(d)
    same["backends"] = [(n, v, t, f) for n, v, t, f in d["backends"]]
    same["ci"] = dict(d["ci"])
    same["ci"]["pins"] = {**d["ci"]["pins"],
                          **{f"{n.upper()}_VERSION": [v] for n, v, _, _ in d["backends"]}}
    _ok("differs from the CI pin" not in st.version_note(same)
        and "declares the pinned version" in st.version_note(same),
        "equal declared/pinned versions render no mismatch list")


def main() -> int:
    test_counts_come_from_sources()
    test_ci_jobs_regex()
    test_check_negative_controls()
    test_version_note_declared_vs_pinned()
    print(f"\n{_PASS} passed, {_FAIL} failed")
    return 1 if _FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
