#!/usr/bin/env python3
"""Python side of the canonical-hash byte-equivalence harness.

For every fixture in tests/cross_canonical/, compute
canonical_hash.canonical_sha256 and assert it equals the value pinned
in tests/cross_canonical/expected.json. The OCaml side
(sdk/test/test_canonical_hash.ml) does the same against the same
sidecar. Both passing on a given fixture means OCaml's
Yojson.Safe.to_string + Codec.normalize and Python's json.dumps +
_canonicalize produce byte-identical output on that input — the
locked invariant every cross-document hash check downstream depends
on.

Pure stdlib; runs in CI's schemas job. Exits non-zero on the first
failing fixture so the failure is visible without scrolling.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

# Allow running directly (python tools/test_canonical_hash.py) or as a
# module — both must find canonical_hash next to this file.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import canonical_hash as ch  # noqa: E402


ROOT = Path(__file__).resolve().parent.parent
CROSS = ROOT / "tests" / "cross_canonical"


def main() -> int:
    expected = json.loads((CROSS / "expected.json").read_text())
    fixtures = sorted(
        p.name for p in CROSS.glob("*.json") if p.name != "expected.json"
    )
    failures = 0
    for name in fixtures:
        want = expected.get(name)
        if want is None:
            print(f"FAIL  {name}  (no entry in expected.json)")
            failures += 1
            continue
        obj = json.loads((CROSS / name).read_text())
        got = ch.canonical_sha256(obj)
        if got == want:
            print(f"PASS  {name}  {got}")
        else:
            print(f"FAIL  {name}")
            print(f"  expected: {want}")
            print(f"  got:      {got}")
            failures += 1
    if failures:
        print(f"\n{failures}/{len(fixtures)} fixtures failed — "
              f"OCaml and Python canonical-hash byte streams have drifted. "
              f"DO NOT update expected.json to make this pass; investigate "
              f"the divergence (see Codec.canonical_bytes docstring).",
              file=sys.stderr)
        return 1
    print(f"\nAll {len(fixtures)} fixtures pass — OCaml<->Python "
          f"canonical-hash byte agreement preserved.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
