#!/usr/bin/env python3
"""Validate the Phase 0 reference artifacts against the JSON Schemas.

Validates:
  - examples/example*.json against schemas/v1.0/ir.schema.json
  - registry/patterns-v1.json (well-formed JSON only; no schema yet)

Usage: python tools/validate.py
"""

import json
import sys
from pathlib import Path

from jsonschema import Draft202012Validator
from referencing import Registry, Resource
from referencing.jsonschema import DRAFT202012


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


def main() -> int:
    schemas, registry = load_schemas()
    validators = {
        name: Draft202012Validator(schema, registry=registry)
        for name, (sid, schema) in schemas.items()
    }

    failed = 0
    print(f"Loaded {len(schemas)} schemas: {sorted(schemas)}")
    print()

    for example in sorted(EXAMPLES.glob("*.json")):
        schema_name = schema_for(example.name)
        if schema_name is None:
            print(f"SKIP {example.relative_to(ROOT)} (no schema mapping)")
            continue
        errors = validate(example, validators[schema_name])
        rel = example.relative_to(ROOT)
        if errors:
            print(f"FAIL {rel}  [{schema_name}]")
            for err in errors:
                print(f"  - {err}")
            failed += 1
        else:
            print(f"OK   {rel}  [{schema_name}]")

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
    print("All Phase 0 artifacts valid.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
