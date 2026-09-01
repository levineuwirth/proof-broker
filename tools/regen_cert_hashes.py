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
    fixture (`CERT_IR_PAIRS`; as of R2 every shipped cert has one).

  * the paired identity-trace fixture's hash slots (`TRACE_IR_PAIRS`):
    every hash field of an identity trace (initial, final, per-entry
    before/after) is the canonical hash of its paired IR.

  * `cert.rewrite_trace_hash` — canonical_sha256 of the paired trace
    fixture (`CERT_TRACE_PAIRS`), pinned AFTER the trace itself is
    re-pinned. The all-zeros sentinel is gone (R2): the OCaml
    verifier rejects it, and check.py errors on it.
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
    CERT_TRACE_PAIRS,
    TRACE_IR_PAIRS,
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


def _repin_identity_trace(trace_path: Path, ir_hash: str) -> bool:
    """Rewrite every hash slot of an identity-trace fixture to
    `ir_hash`, preserving formatting. Returns True if the file
    changed."""
    original = trace_path.read_text()
    text = original
    for field in ("initial_ir_hash", "final_ir_hash",
                  "before_hash", "after_hash"):
        pat = re.compile(_HASH_PATTERN_TPL.format(field=re.escape(field)))
        text = pat.sub(lambda m: m.group(1) + json.dumps(ir_hash), text)
    if text != original:
        trace_path.write_text(text)
        return True
    return False


def main() -> int:
    changed = 0

    # Pass 1: identity-trace fixtures track their paired IR's hash.
    for trace_name in sorted(TRACE_IR_PAIRS):
        ir = json.loads((EXAMPLES / TRACE_IR_PAIRS[trace_name]).read_text())
        if _repin_identity_trace(EXAMPLES / trace_name, canonical_sha256(ir)):
            print(f"updated  {trace_name}")
            changed += 1
        else:
            print(f"unchanged  {trace_name}")

    # Pass 2: certs track manifest + IR + trace.
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

        # dispatch_context_hash: canonical hash of the paired IR.
        ir = json.loads((EXAMPLES / CERT_IR_PAIRS[cert_name]).read_text())
        text, did_dch = _replace_hash(
            text, "dispatch_context_hash", canonical_sha256(ir))

        # rewrite_trace_hash: canonical hash of the paired trace
        # fixture (re-pinned in pass 1 above).
        trace = json.loads(
            (EXAMPLES / CERT_TRACE_PAIRS[cert_name]).read_text())
        text, did_rth = _replace_hash(
            text, "rewrite_trace_hash", canonical_sha256(trace))

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
