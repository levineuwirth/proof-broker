#!/usr/bin/env python3
"""Negative tests for tools/check.py.

For each error and warning path the checker can produce, mutate a copy of
a known-good fixture to introduce that specific bug, run the relevant
check function, and assert the expected message appears.

Also runs a positive control: every unmutated fixture must produce no
errors and no warnings (warnings included in this control because we want
the on-disk fixtures to stay 'clean' — warnings indicate gaps that
should be fixed at fixture-author time).
"""

from __future__ import annotations

import copy
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(Path(__file__).resolve().parent))

from check import (  # noqa: E402
    check_certificate,
    check_ir,
    check_ir_against_registry,
    check_manifest,
    check_trace,
)
from jsonschema import Draft202012Validator  # noqa: E402
from referencing import Registry, Resource  # noqa: E402
from referencing.jsonschema import DRAFT202012  # noqa: E402


def load(p: Path) -> dict:
    with p.open() as f:
        return json.load(f)


def cert_schema_validator() -> Draft202012Validator:
    schema_dir = ROOT / "schemas" / "v1.0"
    registry = Registry()
    cert_schema = None
    for path in sorted(schema_dir.glob("*.schema.json")):
        with path.open() as f:
            schema = json.load(f)
        registry = registry.with_resource(
            schema["$id"], Resource(contents=schema, specification=DRAFT202012)
        )
        if path.name == "certificate.schema.json":
            cert_schema = schema
    assert cert_schema is not None
    return Draft202012Validator(cert_schema, registry=registry)


REGISTRY = load(ROOT / "registry" / "patterns-v1.json")
IR1 = load(ROOT / "examples" / "example1-lia-typeclass.json")
IR2 = load(ROOT / "examples" / "example2-function-composition.json")
IR3 = load(ROOT / "examples" / "example3-quotient-zmod.json")
CERT1 = load(ROOT / "examples" / "cert-example1-tier1-farkas.json")
MANIFEST_CVC5 = load(ROOT / "examples" / "manifest-cvc5.json")
TRACE3 = load(ROOT / "examples" / "rewrite-trace-example3.json")


TESTS: list[tuple[str, callable]] = []


def test(name: str):
    def decorate(fn):
        TESTS.append((name, fn))
        return fn

    return decorate


def assert_contains(messages: list[str], pattern: str, label: str) -> None:
    if not any(pattern in m for m in messages):
        raise AssertionError(
            f"expected {label} containing {pattern!r}; got {messages}"
        )


def assert_absent(messages: list[str], pattern: str, label: str) -> None:
    if any(pattern in m for m in messages):
        raise AssertionError(
            f"expected no {label} containing {pattern!r}; got {messages}"
        )


# --- positive control --------------------------------------------------------


@test("positive control: ir1 has no errors and no warnings")
def _ctrl_ir1():
    e1, w1 = check_ir(IR1)
    e2, w2 = check_ir_against_registry(IR1, REGISTRY)
    assert not e1 and not e2 and not w1 and not w2, (e1, e2, w1, w2)


@test("positive control: ir2 has no errors and no warnings")
def _ctrl_ir2():
    e1, w1 = check_ir(IR2)
    e2, w2 = check_ir_against_registry(IR2, REGISTRY)
    assert not e1 and not e2 and not w1 and not w2, (e1, e2, w1, w2)


@test("positive control: ir3 has no errors and no warnings")
def _ctrl_ir3():
    e1, w1 = check_ir(IR3)
    e2, w2 = check_ir_against_registry(IR3, REGISTRY)
    assert not e1 and not e2 and not w1 and not w2, (e1, e2, w1, w2)


@test("positive control: cert1, manifest_cvc5, trace3 clean")
def _ctrl_others():
    for fn, doc in [
        (check_certificate, CERT1),
        (check_manifest, MANIFEST_CVC5),
        (check_trace, TRACE3),
    ]:
        e, w = fn(doc, REGISTRY)
        assert not e and not w, (fn.__name__, e, w)


# --- IR structural checks ----------------------------------------------------


@test("ir: unresolved TypeRef")
def _ir_unresolved_typeref():
    bad = copy.deepcopy(IR1)
    bad["goal"]["shell"]["args"][1]["type"] = "BogusType"
    e, _ = check_ir(bad)
    assert_contains(e, "unresolved TypeRef 'BogusType'", "error")


@test("ir: unbound Var not in free_vars")
def _ir_unbound_var():
    bad = copy.deepcopy(IR1)
    bad["context"]["hypotheses"][0]["shell"]["left"]["args"][0]["name"] = "ghost_n"
    e, _ = check_ir(bad)
    assert_contains(e, "unbound Var 'ghost_n'", "error")


@test("ir: unresolved App.symbol")
def _ir_unresolved_symbol():
    bad = copy.deepcopy(IR1)
    bad["context"]["hypotheses"][0]["shell"]["left"]["symbol"] = "Bogus.func"
    e, _ = check_ir(bad)
    assert_contains(e, "unresolved symbol 'Bogus.func'", "error")


@test("ir: Opaque payload not in goal.payloads")
def _ir_opaque_missing():
    bad = copy.deepcopy(IR1)
    bad["goal"]["shell"] = {"node": "Opaque", "payload_id": "ghost-payload"}
    bad["goal"]["payloads"] = {}
    e, _ = check_ir(bad)
    assert_contains(e, "Opaque payload 'ghost-payload'", "error")


@test("ir: declared free_var not referenced (warning)")
def _ir_unused_free_var():
    bad = copy.deepcopy(IR1)
    bad["context"]["free_vars"].append({"name": "unused_k", "type": "alpha"})
    _, w = check_ir(bad)
    assert_contains(w, "context.free_vars['unused_k']", "warning")


# --- IR registry checks ------------------------------------------------------


@test("registry: unknown logical feature")
def _reg_unknown_feature():
    bad = copy.deepcopy(IR1)
    bad["logic_classification"]["features_used"][0] = "totally_made_up_feature"
    e, _ = check_ir_against_registry(bad, REGISTRY)
    assert_contains(e, "unknown feature 'totally_made_up_feature'", "error")


@test("registry: unknown first_order_fragment")
def _reg_unknown_fragment():
    bad = copy.deepcopy(IR1)
    bad["logic_classification"]["first_order_fragment"] = "ZZZ"
    e, _ = check_ir_against_registry(bad, REGISTRY)
    assert_contains(e, "unknown fragment 'ZZZ'", "error")


@test("registry: unknown concept_tag in definitional_metadata")
def _reg_unknown_concept():
    bad = copy.deepcopy(IR2)
    bad["definitional_metadata"]["Function.comp"]["concept_tag"] = "no_such_concept"
    e, _ = check_ir_against_registry(bad, REGISTRY)
    assert_contains(e, "unknown 'no_such_concept'", "error")


@test("registry: unknown theory_classification_tag")
def _reg_unknown_theory_tag():
    bad = copy.deepcopy(IR1)
    inst = bad["type_metadata"]["alpha"]["instances"][0]
    inst["theory_classification_tags"][0] = "fake_embedding_tag"
    e, _ = check_ir_against_registry(bad, REGISTRY)
    assert_contains(e, "unknown 'fake_embedding_tag'", "error")


@test("registry: unknown axiom shape")
def _reg_unknown_axiom_shape():
    bad = copy.deepcopy(IR1)
    inst = bad["type_metadata"]["alpha"]["instances"][0]
    inst["abstract_axioms"][0] = "bogus_shape:HAdd.hAdd"
    e, _ = check_ir_against_registry(bad, REGISTRY)
    assert_contains(e, "unknown shape 'bogus_shape'", "error")


@test("registry: referenced entity has no library_provenance (warning)")
def _reg_missing_provenance():
    bad = copy.deepcopy(IR3)
    bad["library_provenance"].pop("MyZMod.ind", None)
    _, w = check_ir_against_registry(bad, REGISTRY)
    assert_contains(w, "MyZMod.ind", "warning")


# --- Certificate checks ------------------------------------------------------


@test("cert: unknown refinement_record.fragment")
def _cert_unknown_fragment():
    bad = copy.deepcopy(CERT1)
    bad["refinement_record"]["fragment"] = "BOGUS"
    e, _ = check_certificate(bad, REGISTRY)
    assert_contains(e, "unknown fragment 'BOGUS'", "error")


@test("cert: tier-3 unknown trace_format")
def _cert_unknown_trace_format():
    fake = {
        "tier": 3,
        "refinement_record": {"fragment": "FOL"},
        "payload": {"trace_format": "fake-format-1", "trace_data": ""},
    }
    e, _ = check_certificate(fake, REGISTRY)
    assert_contains(e, "unknown format 'fake-format-1'", "error")


# --- Tier 2 schema checks ----------------------------------------------------

# Synthetic Tier 2 cert template. Values that aren't relevant to the
# Tier 2 lemmas_used branch use placeholders that match the schema's
# generic shapes (ContentHash, BackendIdentity, etc.).
_DUMMY_HASH = "sha256:" + "0" * 64

_TIER2_BASE = {
    "cert_version": "1.0",
    "tier": 2,
    "format": "case_split_farkas",
    "goal": {
        "shell": {"node": "Const", "name": "True"}
    },
    "dispatch_context_hash": _DUMMY_HASH,
    "rewrite_trace_hash": _DUMMY_HASH,
    "backend": {"name": "cvc5", "version": "1.3.3", "config_hash": _DUMMY_HASH},
    "resources": {"wall_time_ms": 1, "memory_peak_kb": 1},
    "refinement_record": {
        "adapter": "cvc5",
        "adapter_version": "1.3.3",
        "specializations": [],
        "fragment": "LRA",
    },
}


@test("tier2 schema: case_split_farkas {case, witness} lemmas validate")
def _tier2_case_split_validates():
    cert = copy.deepcopy(_TIER2_BASE)
    cert["payload"] = {
        "lemmas_used": [
            {
                "case": {
                    "node": "App", "symbol": "<=", "type_args": [],
                    "args": [
                        {"node": "Var", "name": "x"},
                        {"node": "NumLit", "value": "0", "type": "Real"},
                    ],
                },
                "witness": {
                    "coefficients": [
                        {"hypothesis": "case", "coefficient": "1"},
                        {"hypothesis": "neg_goal", "coefficient": "1"},
                    ]
                },
            },
            {
                "case": {
                    "node": "App", "symbol": ">", "type_args": [],
                    "args": [
                        {"node": "Var", "name": "x"},
                        {"node": "NumLit", "value": "0", "type": "Real"},
                    ],
                },
                "witness": {
                    "coefficients": [
                        {"hypothesis": "case", "coefficient": "1"},
                    ]
                },
            },
        ],
        "strategy_hint": "case_split_farkas",
        "structural_hint": {"disjunctive_hypothesis": "h_disj"},
    }
    errors = list(cert_schema_validator().iter_errors(cert))
    assert not errors, [f"{e.json_path}: {e.message}" for e in errors]


@test("tier2 schema: library-lemma shape still validates")
def _tier2_library_lemma_validates():
    cert = copy.deepcopy(_TIER2_BASE)
    cert["format"] = "library_lemmas"
    cert["payload"] = {
        "lemmas_used": [
            {
                "name": "Nat.add_comm",
                "library": "mathlib",
                "version": "4.0.0",
                "content_hash": _DUMMY_HASH,
            }
        ],
        "strategy_hint": "smt_reconstruct",
    }
    errors = list(cert_schema_validator().iter_errors(cert))
    assert not errors, [f"{e.json_path}: {e.message}" for e in errors]


@test("tier2 schema: lemma matching neither shape rejected")
def _tier2_unknown_lemma_shape_rejected():
    cert = copy.deepcopy(_TIER2_BASE)
    cert["payload"] = {
        "lemmas_used": [
            {"random_field": "nope"}
        ],
        "strategy_hint": "case_split_farkas",
    }
    errors = list(cert_schema_validator().iter_errors(cert))
    assert errors, "expected schema rejection for unrecognized lemma shape"


@test("tier2 schema: case-split witness with negative coefficient rejected")
def _tier2_case_split_negative_coeff_rejected():
    cert = copy.deepcopy(_TIER2_BASE)
    cert["payload"] = {
        "lemmas_used": [
            {
                "case": {"node": "Const", "name": "True"},
                "witness": {
                    "coefficients": [
                        {"hypothesis": "case", "coefficient": "-1"}
                    ]
                },
            }
        ],
        "strategy_hint": "case_split_farkas",
    }
    errors = list(cert_schema_validator().iter_errors(cert))
    assert errors, "expected schema rejection for negative coefficient"


# --- Manifest checks ---------------------------------------------------------


@test("manifest: unknown logic_fragments entry")
def _manifest_unknown_fragment():
    bad = copy.deepcopy(MANIFEST_CVC5)
    bad["logic_fragments"][0] = "BOGUS"
    e, _ = check_manifest(bad, REGISTRY)
    assert_contains(e, "logic_fragments: unknown 'BOGUS'", "error")


@test("manifest: unknown type_constructions entry")
def _manifest_unknown_construction():
    bad = copy.deepcopy(MANIFEST_CVC5)
    bad["type_constructions"][0] = "no_such_construction"
    e, _ = check_manifest(bad, REGISTRY)
    assert_contains(e, "type_constructions: unknown 'no_such_construction'", "error")


@test("manifest: unknown witness_kinds_produced entry")
def _manifest_unknown_witness():
    bad = copy.deepcopy(MANIFEST_CVC5)
    bad["witness_kinds_produced"][0] = "ghost_witness"
    e, _ = check_manifest(bad, REGISTRY)
    assert_contains(e, "witness_kinds_produced: unknown 'ghost_witness'", "error")


@test("manifest: unknown trace_formats_produced entry")
def _manifest_unknown_trace_format():
    bad = copy.deepcopy(MANIFEST_CVC5)
    bad["trace_formats_produced"][0] = "ghost-format"
    e, _ = check_manifest(bad, REGISTRY)
    assert_contains(e, "trace_formats_produced: unknown 'ghost-format'", "error")


# --- Trace checks ------------------------------------------------------------


@test("trace: unknown pass name (warning)")
def _trace_unknown_pass():
    bad = copy.deepcopy(TRACE3)
    bad["entries"][0]["pass"] = "phantom_pass"
    _, w = check_trace(bad, REGISTRY)
    assert_contains(w, "phantom_pass", "warning")


# --- runner ------------------------------------------------------------------


def main() -> int:
    failures: list[tuple[str, str]] = []
    for name, fn in TESTS:
        try:
            fn()
        except AssertionError as exc:
            failures.append((name, str(exc)))
            print(f"FAIL  {name}")
        else:
            print(f"PASS  {name}")

    print()
    if failures:
        print(f"{len(failures)} of {len(TESTS)} tests failed.")
        for name, msg in failures:
            print(f"  {name}: {msg}")
        return 1
    print(f"All {len(TESTS)} negative tests pass.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
