#!/usr/bin/env python3
"""Observe real fsync calls for a fresh cohort slot; no fault or power-loss simulation."""
import argparse
import json
import os
from pathlib import Path
import stat
import sys
import tempfile
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import cohort_contract as contract
import cohort_ledger as ledger
import run as r6


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert not args.output.exists()
    calls = []
    with tempfile.TemporaryDirectory(prefix='r6-009-durability-review-') as temp:
        base = Path(temp); policy = contract.config()
        book = ledger.Ledger(base/'ledger', policy['campaign']['id'])
        book.activate(policy, False)
        task, draw = 'verinf-d1-70', 1
        task_dir = book.slots/task; draw_dir = task_dir/str(draw)
        assert not task_dir.exists() and not draw_dir.exists()
        original = os.fsync
        def observe(fd):
            path = Path(os.readlink(f'/proc/self/fd/{fd}'))
            calls.append({'path': str(path.relative_to(base)), 'directory': stat.S_ISDIR(os.fstat(fd).st_mode)})
            return original(fd)
        with patch.object(os, 'fsync', observe):
            permit, _ = book.reserve('review', policy, task, draw, {'reserved_micro_usd': 102400},
                                     {'contract_sha256': policy['contract_sha256'], 'request_sha256': 'b'*64}, {'accepted': True})
            reserve_end = len(calls)
            slot = book.grant_slot(permit)
            ledger.commit_grant(slot, ledger.grant_record(permit, 1))
        required = [book.slots, task_dir, draw_dir, slot]
        recorded = {c['path'] for c in calls if c['directory']}
        result = {'complete': True, 'new_task_and_draw_precondition': True,
                  'scope': 'actual fsync observation during production reserve and grant; no simulated power loss',
                  'calls': calls, 'reserve_end': reserve_end,
                  'parent_directory_fsyncs': {str(p.relative_to(base)): str(p.relative_to(base)) in recorded for p in required},
                  'missing_parent_fsyncs': [str(p.relative_to(base)) for p in required if str(p.relative_to(base)) not in recorded],
                  'program_sha256': r6.sha(Path(__file__)), 'live_model_calls': 0, 'real_credentials_read': 0}
    r6.write_json(args.output, result)
    print(json.dumps(result, indent=2))


if __name__ == '__main__': main()
