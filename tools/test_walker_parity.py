#!/usr/bin/env python3
"""Tests for check_walker_parity's extraction + comparison.

Drives the marker/regex logic over synthetic fixtures so the extractor is
covered independently of the real source files, then smoke-tests that the
real Lean and Rocq walkers actually agree today. Pure stdlib; run directly
(`python tools/test_walker_parity.py`) -- exits non-zero on the first failure.
"""
from __future__ import annotations

import sys
import tempfile
from pathlib import Path

import check_walker_parity as P


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


def _write(name: str, body: str) -> Path:
    d = Path(tempfile.mkdtemp())
    p = d / name
    p.write_text(body, encoding="utf-8")
    return p


def _exits(fn) -> bool:
    """True if calling fn() raises SystemExit (the extractor's failure path)."""
    try:
        fn()
        return False
    except SystemExit:
        return True


# ---------------------------------------------------------------------------
# Extraction
# ---------------------------------------------------------------------------

def test_rocq_arrow_and_marker_scoping() -> None:
    # Literals before BEGIN and after END (incl. the long error string) must
    # NOT leak into the rule set; comments between arms must be ignored.
    f = _write("w.ml", '''
    | "noise_before" -> outside_block
    match s.rule with
    (* PARITY:walker-rules BEGIN *)
    | "or" -> elab_or st s
    | "resolution" -> elab_resolution s   (* comment with "fake" literal *)
    (* PARITY:walker-rules END *)
    | other ->
      raise (Walker_error "rule '%s' not supported: or / resolution / cong")
    ''')
    _ok(P.extract_rules(f) == {"or", "resolution"},
        "rocq: extracts only arms between markers")


def test_lean_arrow_form() -> None:
    f = _write("w.lean", '''
    let x <- match s.rule with
    -- PARITY:walker-rules BEGIN
    | "or" => elabOr s
    | "cong" => elabCong ctx s
    -- PARITY:walker-rules END
    | _ => throwError "or / cong"
    ''')
    _ok(P.extract_rules(f) == {"or", "cong"},
        "lean: handles => arms and -- markers")


def test_missing_markers_exits() -> None:
    f = _write("w.ml", '| "or" -> elab_or s\n')
    _ok(_exits(lambda: P.extract_rules(f)),
        "missing markers -> SystemExit")


def test_empty_block_exits() -> None:
    f = _write("w.ml",
               "(* PARITY:walker-rules BEGIN *)\n"
               "(* nothing here *)\n"
               "(* PARITY:walker-rules END *)\n")
    _ok(_exits(lambda: P.extract_rules(f)),
        "empty marker block -> SystemExit")


def test_supported_rules_extraction() -> None:
    f = _write("t.ml", '''
    (* PARITY:walker-rules BEGIN *)
    | "or" -> check_or env step
    | "cong" -> check_cong env step
    (* PARITY:walker-rules END *)
    let supported_rules : string list = [
      "cong"; "or";
    ]
    ''')
    _ok(P.extract_supported_rules(f) == {"or", "cong"},
        "supported_rules: extracts the minter's list")


def test_supported_rules_missing_exits() -> None:
    f = _write("t.ml", '| "or" -> check_or env step\n')
    _ok(_exits(lambda: P.extract_supported_rules(f)),
        "missing supported_rules list -> SystemExit")


def test_supported_rules_empty_exits() -> None:
    f = _write("t.ml", "let supported_rules : string list = [\n]\n")
    _ok(_exits(lambda: P.extract_supported_rules(f)),
        "empty supported_rules list -> SystemExit")


# ---------------------------------------------------------------------------
# Live parity (doubles as the assertion the CI check makes)
# ---------------------------------------------------------------------------

def test_real_walkers_agree() -> None:
    lean = P.extract_rules(P.LEAN)
    rocq = P.extract_rules(P.ROCQ)
    sdk = P.extract_rules(P.SDK)
    _ok(lean == rocq == sdk,
        f"real walkers + SDK mint gate agree "
        f"(lean={len(lean)}, rocq={len(rocq)}, sdk={len(sdk)} rules); "
        f"union-minus-lean={sorted((rocq | sdk) - lean)} "
        f"union-minus-rocq={sorted((lean | sdk) - rocq)} "
        f"union-minus-sdk={sorted((lean | rocq) - sdk)}")


def test_real_sdk_arms_match_supported_rules() -> None:
    # Pins the SDK-internal sync in BOTH directions: every check_step
    # dispatch arm has a supported_rules entry (an arm the minter never
    # mints would overcount coverage's mintable) AND every
    # supported_rules entry has an arm (the OCaml
    # test_supported_rules_sync covers behavior for that direction;
    # set equality here covers both textually).
    arms = P.extract_rules(P.SDK)
    gate = P.extract_supported_rules()
    _ok(arms == gate,
        f"SDK check_step arms == supported_rules "
        f"(arms={len(arms)}, gate={len(gate)}); "
        f"arms-minus-gate={sorted(arms - gate)} "
        f"gate-minus-arms={sorted(gate - arms)}")


def main() -> int:
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            fn()
    print(f"\n{_PASS} passed, {_FAIL} failed")
    return 1 if _FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
