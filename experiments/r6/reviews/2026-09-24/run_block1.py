#!/usr/bin/env python3
"""R6-014 block 1: the eleven authorized draw-1 episodes, run by the operator with the operator's credential file. Never reads the file:
its path is passed to the frozen driver (`cohort_episode.py --mode live`), which mounts it for the sender alone.

Episodes run one at a time into a fresh `cohort-live-v9/`, in the rehearsals' order. After each, the live ledger is read (without the
credential): unless the slot ended as a send grant with a returned response and nothing is left open, collection **pauses** here for
review. That covers an unknown or partial send, a pre-send release and an interrupted episode; the predeclared pause rules do not depend
on proof success. A proof failure or a rejected witness does not pause. Resuming is the same command; completed slots are skipped by
their run directories, and a consumed slot can never be reserved again.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

R6 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(R6))
import cohort_contract as contract

RUNS = R6/'cohort-live-v9'
ORDER = ('l069', 'l070', 'l071', 'l078', 'l096', 'l166', 'l170', 'l175', 'l178', 'l204', 'l099')


def slot_state(task_id):
    _, s = contract.campaign_ledger(True).snapshot()
    return s, s['slots'].get(f'{task_id}/1')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--credential-file', type=Path, required=True)
    args = parser.parse_args()
    RUNS.mkdir(exist_ok=True)
    for site in ORDER:
        task_id, run = f'bracket-{site}', RUNS/f'{site}-draw1'
        if run.exists():
            if not (run/'seal.json').exists(): raise SystemExit(f'PAUSE: {run.name} exists without a seal (interrupted); review before anything else')
            print(json.dumps({'run': run.name, 'skipped': 'already recorded'}), flush=True); continue
        s, _ = slot_state(task_id)
        if s['open_reservations']: raise SystemExit(f'PAUSE: an open reservation exists before {run.name}: {s["open_reservations"]}')
        result = subprocess.run([sys.executable, str(R6/'cohort_episode.py'), '--mode', 'live', '--task', task_id, '--draw', '1',
                                 '--run-dir', str(run), '--credential-file', str(args.credential_file)], cwd=R6)
        s, slot = slot_state(task_id)
        reconciliation = json.loads((run/'campaign-reconciliation.json').read_bytes()) if (run/'campaign-reconciliation.json').exists() else None
        summary = json.loads((run/'credential-summary.json').read_bytes()) if (run/'credential-summary.json').exists() else {}
        line = {'run': run.name, 'exit': result.returncode, 'terminal': (reconciliation or {}).get('kind'), 'send_outcome': (reconciliation or {}).get('send_outcome'),
                'failure_category': summary.get('failure_category'), 'consumed': s['transmissions_consumed'], 'committed_micro_usd': s['committed_micro_usd']}
        print(json.dumps(line), flush=True)
        if not (slot and slot['consumed'] and reconciliation and reconciliation['kind'] == 'send_grant' and reconciliation.get('send_outcome') == 'returned'
                and not s['open_reservations'] and (run/'seal.json').exists()):
            raise SystemExit(f'PAUSE after {run.name}: the slot did not end as a returned send; stop and review')
    print(json.dumps({'block_1': 'complete', 'runs': len(ORDER), 'next': 'the operator disclosure scan, then the frozen evaluation'}), flush=True)


if __name__ == '__main__':
    main()
