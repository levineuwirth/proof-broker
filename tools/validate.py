#!/usr/bin/env python3
"""Validate every fixture in examples/ against the JSON Schemas.

Validates:
  - examples/*.json (IRs, certificates, adapter manifests, rewrite
    traces) against the schemas/v1.0/*.schema.json that `schema_for`
    maps each fixture name to
  - registry/patterns-v1.json (well-formed JSON only; no schema yet)

Then ALSO co-enforces the registry vocabulary (audit M3): the
schemas keep features_used / first_order_fragment / type_constructions
as open strings on purpose — registry/patterns-v1.json is the single
authoritative source. This step runs check.py's registry validators
so `python tools/validate.py` alone rejects an unknown
fragment/feature/construction.

Also runs check.py's pairing-completeness check (C2 round 1): a
cert-*.json or rewrite-trace-*-identity.json in examples/ that is
missing from the pairing maps fails validation here too — the hash
linkage below is pairing-map-driven and must not be skippable.

Usage: python tools/validate.py
"""

import json
import sys
from pathlib import Path

from jsonschema import Draft202012Validator
from referencing import Registry, Resource
from referencing.jsonschema import DRAFT202012

# Registry co-enforcement (M3): reuse check.py's vocabulary checks so
# there is exactly one implementation of "is this fragment known".
from check import (  # noqa: E402
    check_ir_against_registry,
    check_certificate,
    check_manifest,
    check_trace,
    # Cross-fixture checks on a paired cert (#18d / #24-M1 hash
    # linkage, R2.4 manifest consistency, R3-M1 witness provenance):
    # check.py owns the pairing maps, the loader and the bundle, so
    # this driver runs exactly what check.py runs.
    load_cert_pairing,
    check_paired_cert,
    # Pairing completeness (C2 round 1): the paired-cert step below is
    # pairing-map-opt-in, so an unpaired cert-*.json would silently
    # skip it; check.py owns the maps and the completeness check.
    check_fixture_pairing_completeness,
    check_unknown_fixture_names,
    emit_warnings,
)


ROOT = Path(__file__).resolve().parent.parent
SCHEMA_DIR = ROOT / "schemas" / "v1.0"
EXAMPLES = ROOT / "examples"
REGISTRY_DIR = ROOT / "registry"


def load_schemas():
    registry = Registry()
    schemas = {}
    for path in sorted(SCHEMA_DIR.glob("*.schema.json")):
        with path.open() as f:
            schema = json.load(f)
        sid = schema["$id"]
        schemas[path.name] = (sid, schema)
        registry = registry.with_resource(sid, Resource(contents=schema, specification=DRAFT202012))
    return schemas, registry


def validate(path: Path, validator: Draft202012Validator) -> list[str]:
    with path.open() as f:
        instance = json.load(f)
    return [f"{e.json_path}: {e.message}" for e in validator.iter_errors(instance)]


FILE_TO_SCHEMA = {
    "example": "ir.schema.json",
    "cert-": "certificate.schema.json",
    "manifest-": "adapter-manifest.schema.json",
    "rewrite-trace-": "rewrite-trace.schema.json",
}


def schema_for(name: str) -> str | None:
    for prefix, schema_file in FILE_TO_SCHEMA.items():
        if name.startswith(prefix):
            return schema_file
    return None


# Registry co-enforcement dispatch (M3): same prefix convention as
# FILE_TO_SCHEMA. Each callable is (doc, registry) -> (errors, warnings)
# from check.py. "example" → IR registry check; others by prefix.
REGISTRY_CHECK = {
    "example": check_ir_against_registry,
    "cert-": check_certificate,
    "manifest-": check_manifest,
    "rewrite-trace-": check_trace,
}


def registry_check_for(name: str):
    for prefix, fn in REGISTRY_CHECK.items():
        if name.startswith(prefix):
            return fn
    return None


def main() -> int:
    schemas, registry = load_schemas()

    failed = 0
    print(f"Loaded {len(schemas)} schemas: {sorted(schemas)}")
    print()

    for name, (sid, schema) in schemas.items():
        try:
            Draft202012Validator.check_schema(schema)
            print(f"OK   schemas/v1.0/{name} (meta-schema)")
        except Exception as e:
            print(f"FAIL schemas/v1.0/{name}: {e}")
            failed += 1
    print()

    validators = {
        name: Draft202012Validator(schema, registry=registry)
        for name, (sid, schema) in schemas.items()
    }

    with (REGISTRY_DIR / "patterns-v1.json").open() as f:
        patterns = json.load(f)

    # Pairing completeness (C2 round 1): every cert-*.json must key
    # into all three of check.py's cert pairing maps and every
    # rewrite-trace-*-identity.json into TRACE_IR_PAIRS — otherwise
    # the hash-linkage step below would silently skip the fixture.
    pairing_errors = check_fixture_pairing_completeness()
    if pairing_errors:
        print("FAIL examples/ pairing completeness")
        for msg in pairing_errors:
            print(f"  - {msg}")
        failed += 1
    else:
        print("OK   examples/ pairing completeness")

    name_errors = check_unknown_fixture_names()
    if name_errors:
        print("FAIL examples/ fixture-name discovery")
        for msg in name_errors:
            print(f"  - {msg}")
        failed += 1
    else:
        print("OK   examples/ fixture-name discovery")

    for example in sorted(EXAMPLES.glob("*.json")):
        schema_name = schema_for(example.name)
        if schema_name is None:
            print(f"SKIP {example.relative_to(ROOT)} (no schema mapping)")
            continue
        rel = example.relative_to(ROOT)
        errors = validate(example, validators[schema_name])

        # Registry co-enforcement (M3): a structurally-valid document
        # can still name an unknown fragment/feature/construction —
        # the schemas leave that vocabulary open by design. Fold the
        # registry errors in here so validate.py is a superset.
        reg_fn = registry_check_for(example.name)
        if reg_fn is not None:
            with example.open() as f:
                doc = json.load(f)
            reg_errors, _reg_warnings = reg_fn(doc, patterns)
            errors = errors + [f"registry: {e}" for e in reg_errors]

        # Cross-fixture checks on a paired cert: hash linkage to its
        # manifest, IR and rewrite trace (#18d / #24-M1), producibility
        # by the manifest (R2.4) and witness provenance (R3-M1). The
        # pairing maps, the loader and the check bundle live in
        # check.py and are shared with check.py's own driver and
        # tools/regen_cert_hashes.py, so this run is exactly check.py's.
        pairing = load_cert_pairing(example.name)
        if pairing is not None:
            with example.open() as f:
                cert = json.load(f)
            found = check_paired_cert(cert, str(rel), pairing)
            errors = (errors
                      + [f"hash: {e}" for e in found.hash_errors]
                      + [f"manifest: {e}" for e in found.manifest_errors]
                      + [f"witness: {e}" for e in found.witness_errors])
            hash_warnings = found.warnings
        else:
            hash_warnings = []

        if errors:
            print(f"FAIL {rel}  [{schema_name}]")
            for err in errors:
                print(f"  - {err}")
            failed += 1
        else:
            print(f"OK   {rel}  [{schema_name}]")
        # Non-blocking (version label drift between a cert and its
        # paired manifest): printed, never counted as a failure.
        emit_warnings(hash_warnings)

    for data_file in sorted(REGISTRY_DIR.glob("*.json")):
        try:
            with data_file.open() as f:
                json.load(f)
            print(f"OK   {data_file.relative_to(ROOT)} (json well-formed)")
        except json.JSONDecodeError as e:
            print(f"FAIL {data_file.relative_to(ROOT)}: {e}")
            failed += 1

    print()
    if failed:
        print(f"{failed} file(s) failed validation.")
        return 1
    print("All artifacts valid.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
