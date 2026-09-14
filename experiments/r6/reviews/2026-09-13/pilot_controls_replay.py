#!/usr/bin/env python3
"""Replay the 17 R6-007 boundary controls against the signed, locked sources.

`test_pilot.py` presupposes an unsigned policy (`policy_frozen_disabled`,
`authorization_required`). Its last run predates the final edits to four pilot
files. This replay runs the same 17 cases over the *frozen* sources with one
substitution, recorded here: `contract.config()` returns the signed policy with
`live_enabled`, `authorization` and `live_model_calls_authorized` reset to the
unsigned values. Every other field, the lock check and the runtime check are
the frozen ones. Nothing is written to a locked file.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import pilot_contract as contract
import run as r6
import test_pilot

FROZEN = contract.config
UNSIGNED = {'live_enabled': False, 'authorization': None, 'live_model_calls_authorized': 0}


def unsigned_view():
    c = FROZEN()  # lock, runtime and chain checks run unchanged
    signed = {k: c[k] for k in UNSIGNED}
    c.update(UNSIGNED)
    unsigned_view.signed = signed
    return c


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('R6-007-CONTROLS-REPLAY.json'))
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    contract.config = unsigned_view
    test_pilot.units(args.output.resolve())
    record = json.loads(args.output.read_bytes())
    record['replay'] = {'policy_sha256': r6.sha(contract.CONFIG), 'source_lock_sha256': r6.sha(contract.LOCK),
        'sources': {f: r6.sha(ROOT/f) for f in contract.FILES},
        'substituted_fields': UNSIGNED, 'signed_values_replaced': unsigned_view.signed,
        'program_sha256': r6.sha(Path(__file__)),
        'scope': 'same 17 cases as test_pilot.py over the frozen sources; only the three signature fields are viewed as unsigned'}
    r6.write_json(args.output, record)
    print(json.dumps({'passed': record['passed'], 'check_count': record['check_count'],
                      'source_lock_sha256': record['replay']['source_lock_sha256'][:16]}, indent=1))


if __name__ == '__main__':
    main()
