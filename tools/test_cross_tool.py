#!/usr/bin/env python3
"""Cross-tool agreement test.

For each IR fixture in examples/, invoke the OCaml round-trip CLI
(sdk/bin/round_trip_cli.ml), capture its output, and run both the
Python schema validator and the cross-document soundness checker on
the round-tripped JSON. The fixture passes iff:

  1. The OCaml CLI accepts the input (Codec.of_json doesn't raise).
  2. The OCaml CLI's output validates against the IR schema.
  3. The OCaml CLI's output passes the cross-doc checker.
  4. The output is structurally equal to the input (modulo key order).

This catches drift between the JSON Schema and the OCaml ADTs: if the
OCaml side accepts a fixture but emits something the Python validator
rejects, the two pipelines disagree about what the fixture means.

Only IR documents are exercised here (the OCaml IR codec is what we
have so far). Certificate / manifest / trace round-trip tests follow
when their OCaml ADTs land.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXAMPLES = ROOT / "examples"
SDK = ROOT / "sdk"
CLI_SOURCE_PATH = SDK / "bin" / "round_trip_cli.ml"

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check import (  # noqa: E402
    check_ir,
    check_ir_against_registry,
)
from jsonschema import Draft202012Validator  # noqa: E402
from referencing import Registry, Resource  # noqa: E402
from referencing.jsonschema import DRAFT202012  # noqa: E402


def find_cli_binary() -> Path:
    """Locate the dune-built CLI binary in either build layout.

    Workspace-rooted (the layout `dune build sdk` from repo root produces)
    is checked first since that's what the CI workflow and most local
    invocations use. The sdk-rooted layout (`dune build --root=sdk`) is
    retained as a fallback for back-compat with the Phase-0 sub-project
    invocation pattern, which some local muscle memory may still use.
    """
    candidates = [
        ROOT / "_build" / "default" / "sdk" / "bin" / "round_trip_cli.exe",
        SDK / "_build" / "default" / "bin" / "round_trip_cli.exe",
    ]
    for c in candidates:
        if c.exists():
            return c
    raise SystemExit(
        "CLI binary not found at any of:\n"
        + "\n".join(f"  {c}" for c in candidates)
        + "\nRun `opam exec -- dune build sdk` (workspace-rooted) or "
        "`dune build --root=sdk` first (with the proof-broker opam switch active)."
    )


def load_schemas():
    schema_dir = ROOT / "schemas" / "v1.0"
    registry = Registry()
    schemas = {}
    for path in sorted(schema_dir.glob("*.schema.json")):
        with path.open() as f:
            schema = json.load(f)
        schemas[path.name] = (schema["$id"], schema)
        registry = registry.with_resource(
            schema["$id"], Resource(contents=schema, specification=DRAFT202012)
        )
    return schemas, registry


def normalize(j):
    """Recursive key sort for order-insensitive equality."""
    if isinstance(j, dict):
        return {k: normalize(v) for k, v in sorted(j.items())}
    if isinstance(j, list):
        return [normalize(x) for x in j]
    return j


IR_FIXTURES = [
    "example1-lia-typeclass.json",
    "example2-function-composition.json",
    "example3-quotient-zmod.json",
]


def run_one(fixture: Path, cli: Path, ir_validator, registry) -> tuple[list[str], list[str]]:
    """Round-trip one fixture; return (errors, warnings)."""
    errors: list[str] = []
    warnings: list[str] = []

    proc = subprocess.run(
        [str(cli), str(fixture)],
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        errors.append(f"OCaml CLI rejected fixture (rc={proc.returncode}): {proc.stderr.strip()}")
        return errors, warnings

    try:
        roundtripped = json.loads(proc.stdout)
    except json.JSONDecodeError as e:
        errors.append(f"OCaml CLI emitted non-JSON output: {e}")
        return errors, warnings

    schema_errors = list(ir_validator.iter_errors(roundtripped))
    for se in schema_errors:
        errors.append(f"round-tripped output fails IR schema: {se.json_path}: {se.message}")

    e1, w1 = check_ir(roundtripped)
    e2, w2 = check_ir_against_registry(roundtripped, registry)
    for msg in e1 + e2:
        errors.append(f"round-tripped output fails cross-doc check: {msg}")
    warnings.extend(w1 + w2)

    with fixture.open() as f:
        original = json.load(f)
    if normalize(original) != normalize(roundtripped):
        errors.append("round-tripped output differs structurally from input")

    return errors, warnings


def main() -> int:
    cli = find_cli_binary()
    schemas, registry = load_schemas()

    ir_id = "https://proof-broker.dev/schemas/v1.0/ir.schema.json"
    ir_schema = next(s for sid, s in schemas.values() if sid == ir_id)
    ir_validator = Draft202012Validator(ir_schema, registry=registry)

    with (ROOT / "registry" / "patterns-v1.json").open() as f:
        patterns_registry = json.load(f)

    failed = 0
    for name in IR_FIXTURES:
        path = EXAMPLES / name
        errors, warnings = run_one(path, cli, ir_validator, patterns_registry)
        rel = path.relative_to(ROOT)
        if errors:
            print(f"FAIL {rel}")
            for e in errors:
                print(f"  ERROR  {e}")
            for w in warnings:
                print(f"  WARN   {w}")
            failed += 1
        elif warnings:
            print(f"WARN {rel}")
            for w in warnings:
                print(f"  WARN   {w}")
        else:
            print(f"OK   {rel}  [OCaml round-trip → schema + cross-doc]")

    print()
    if failed:
        print(f"{failed} fixture(s) failed cross-tool agreement.")
        return 1
    print(f"All {len(IR_FIXTURES)} fixtures: OCaml + Python pipelines agree.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
