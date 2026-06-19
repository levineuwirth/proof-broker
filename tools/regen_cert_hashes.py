#!/usr/bin/env python3
"""One-shot regenerator for the cross-document hashes in
`examples/cert-*.json`.

This is NOT a verifier — `check.py` does the verification. This is the
tool you run after editing the manifest or paired IR fixtures to
re-pin the cert hashes that should track them. Idempotent: running
on an already-correct cert leaves the file unchanged.

What it regenerates:

  * `cert.backend.config_hash` — strict-identity (#18d, locked in PR
    discussion): canonical_sha256 of the matched adapter manifest.
    Every cert has a `backend.name` that names exactly one manifest;
    `CERT_MANIFEST_PAIRS` below codifies the mapping.

  * `cert.dispatch_context_hash` — canonical_sha256 of the paired IR
    fixture. Only certs in `CERT_IR_PAIRS` pair with a shipped IR;
    the rest (synthesized for in-process tests) keep
    `_UNPAIRED_DISPATCH_CONTEXT_HASH` as a documented sentinel.

  * `cert.rewrite_trace_hash` — left at the documented no-trace
    sentinel `_NO_TRACE_HASH` for now. No example cert ships with a
    paired trace document; the schema-required field needs a value
    and the all-zeros hash is unambiguously "not a real digest." A
    future PR that ships trace-paired cert examples wires this up.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from canonical_hash import canonical_sha256  # noqa: E402
# Single source of truth for the cert↔fixture pairing maps and the
# sentinel values — defined in check.py since the *check* of these
# invariants is the audited path; regen just consumes the same
# convention. Drift between regen and check is structurally impossible.
from check import (  # noqa: E402
    CERT_MANIFEST_PAIRS,
    CERT_IR_PAIRS,
    _UNPAIRED_DISPATCH_CONTEXT_HASH,
    _NO_TRACE_HASH,
)


ROOT = Path(__file__).resolve().parent.parent
EXAMPLES = ROOT / "examples"


import re

_HASH_PATTERN_TPL = (
    r'("{field}"\s*:\s*)"sha256:[a-fA-F0-9]{{64}}"'
)


def _replace_hash(text: str, field: str, value: str) -> tuple[str, bool]:
    """Replace `"<field>": "sha256:..."` in-place, preserving the
    surrounding whitespace exactly. Returns (new_text, replaced)."""
    assert value.startswith("sha256:") and len(value) == 64 + 7, value
    pat = re.compile(_HASH_PATTERN_TPL.format(field=re.escape(field)))
    new_text, n = pat.subn(lambda m: m.group(1) + json.dumps(value), text)
    return new_text, n > 0


def main() -> int:
    changed = 0
    for cert_name in sorted(CERT_MANIFEST_PAIRS):
        cert_path = EXAMPLES / cert_name
        original = cert_path.read_text()
        text = original

        # config_hash: always paired with a manifest.
        manifest = json.loads(
            (EXAMPLES / CERT_MANIFEST_PAIRS[cert_name]).read_text()
        )
        text, did_cfg = _replace_hash(
            text, "config_hash", canonical_sha256(manifest))

        # dispatch_context_hash: paired IR if we have one, sentinel otherwise.
        ir_name = CERT_IR_PAIRS.get(cert_name)
        if ir_name is not None:
            ir = json.loads((EXAMPLES / ir_name).read_text())
            new_dch = canonical_sha256(ir)
        else:
            new_dch = _UNPAIRED_DISPATCH_CONTEXT_HASH
        text, did_dch = _replace_hash(text, "dispatch_context_hash", new_dch)

        # rewrite_trace_hash: documented no-trace sentinel.
        text, did_rth = _replace_hash(
            text, "rewrite_trace_hash", _NO_TRACE_HASH)

        if not (did_cfg and did_dch and did_rth):
            print(f"WARN     {cert_name}: missing one of the three hash fields "
                  f"(config_hash={did_cfg} dispatch_context_hash={did_dch} "
                  f"rewrite_trace_hash={did_rth})")

        if text != original:
            cert_path.write_text(text)
            print(f"updated  {cert_name}")
            changed += 1
        else:
            print(f"unchanged  {cert_name}")

    print(f"\n{changed} fixture(s) updated.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
