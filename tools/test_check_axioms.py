#!/usr/bin/env python3
"""Negative/format tests for the trust-footprint gate parsers.

Covers the audit C2/C3 hardening: Lean marker-hijack resistance,
conflicting-signal poisoning, Rocq inline `name : type` axiom lines,
unparsed-block poisoning, and the hard-deny set. Pure stdlib; run
directly (`python tools/test_check_axioms.py`) — exits non-zero on
the first failure.
"""
from __future__ import annotations

import sys

import check_axioms as ca


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


# ---------------------------------------------------------------------------
# Lean parser
# ---------------------------------------------------------------------------

def test_lean_basic_list_and_none() -> None:
    text = (
        "info: Test/Tactic.lean:159:0: 'A' depends on axioms: "
        "[propext, Classical.choice, Quot.sound]\n"
        "info: Test/Tactic.lean:170:0: 'B' does not depend on any axioms\n"
    )
    got = ca.parse_lean_axioms(text)
    _ok(got.get("A") == {"propext", "Classical.choice", "Quot.sound"},
        "lean: depends-on list parsed")
    _ok(got.get("B") == set(), "lean: does-not-depend parsed as empty")


def test_lean_multiline_list() -> None:
    text = (
        "info: Test/T.lean:1:0: 'M' depends on axioms: [propext,\n"
        " Classical.choice,\n"
        " Quot.sound]\n"
    )
    got = ca.parse_lean_axioms(text)
    _ok(got.get("M") == {"propext", "Classical.choice", "Quot.sound"},
        "lean: multi-line wrapped axiom list parsed")


def test_lean_marker_hijack_resisted() -> None:
    # The phrase appears mid-line in an echoed source comment / string,
    # NOT as a Lean diagnostic. Must not create or downgrade an entry.
    text = (
        "info: Test/T.lean:1:0: 'H' depends on axioms: [propext, sorryAx]\n"
        "error: some message mentioning 'H' does not depend on any axioms\n"
        "  -- a comment: 'H' does not depend on any axioms (prose)\n"
    )
    got = ca.parse_lean_axioms(text)
    _ok(got.get("H") == {"propext", "sorryAx"},
        "lean: mid-line phrase does NOT downgrade a real footprint")


def test_lean_conflict_poisoned() -> None:
    text = (
        "info: a.lean:1:0: 'C' depends on axioms: [propext, sorryAx]\n"
        "info: a.lean:1:0: 'C' does not depend on any axioms\n"
    )
    got = ca.parse_lean_axioms(text)
    _ok(got.get("C") == {ca.PARSE_POISON},
        "lean: conflicting signals for one name are poisoned")


def test_lean_hard_deny_enforced_even_if_allowlisted() -> None:
    actual = {"X": {"sorryAx"}}
    allowed = {"X": {"sorryAx"}}  # deliberately (mis)allowlisted
    errs = ca.check(actual, allowed)
    _ok(len(errs) == 1 and "UNSOUND" in errs[0],
        "check: hard-deny fails even when allowlist permits it")


def test_lean_poison_reported_as_parse_failure() -> None:
    errs = ca.check({"P": {ca.PARSE_POISON}}, {"P": set()})
    _ok(len(errs) == 1 and "parse failure" in errs[0],
        "check: parse-poison surfaces as a hard parse failure")


# ---------------------------------------------------------------------------
# Rocq parser
# ---------------------------------------------------------------------------

def test_rocq_inline_type_axiom_lines() -> None:
    # Modern Coq/Rocq >= 9: axiom name and type on ONE line. This is
    # the exact case the old `name :$` regex dropped (audit C3).
    text = (
        "r_thm = fun x => x\n"
        "Axioms:\n"
        "ClassicalDedekindReals.sig_forall_dec : forall P : nat -> Prop,"
        " (forall n, {P n} + {~ P n}) -> {n | ~ P n} + {forall n, P n}\n"
        "FunctionalExtensionality.functional_extensionality_dep :"
        " forall ..., f = g\n"
    )
    got = ca.parse_rocq_axioms(text)
    _ok(got.get("r_thm") == {
        "ClassicalDedekindReals.sig_forall_dec",
        "FunctionalExtensionality.functional_extensionality_dep",
    }, "rocq: inline `name : type` axiom lines captured")


def test_rocq_closed_is_axiom_free() -> None:
    text = "z_thm = fun x => x\nClosed under the global context\n"
    got = ca.parse_rocq_axioms(text)
    _ok(got.get("z_thm") == set(),
        "rocq: 'Closed under the global context' = axiom-free")


def test_rocq_unparsed_block_poisoned() -> None:
    # `Axioms:` seen but every member line is in a shape we can't
    # parse → must poison, not record axiom-free (audit C3 fail-open).
    text = (
        "q_thm = fun x => x\n"
        "Axioms:\n"
        "<<<garbage the parser does not understand>>>\n"
    )
    got = ca.parse_rocq_axioms(text)
    _ok(got.get("q_thm") == {ca.PARSE_POISON},
        "rocq: Axioms block parsing to zero names is poisoned")


def test_rocq_indented_continuation_skipped() -> None:
    text = (
        "k_thm = fun x => x\n"
        "Axioms:\n"
        "some_axiom : forall (a : T),\n"
        "    a = a ->\n"          # indented type continuation
        "    something\n"
    )
    got = ca.parse_rocq_axioms(text)
    _ok(got.get("k_thm") == {"some_axiom"},
        "rocq: indented type-continuation lines are not axiom names")


def main() -> int:
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            fn()
    print(f"\n{_PASS} passed, {_FAIL} failed")
    return 1 if _FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
