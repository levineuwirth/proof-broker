#!/usr/bin/env python3
"""Controls for the block 2 runner's continuation gate (`run_block2.py`, revision 2). SYNTHETIC: every case is a copy of an audited block 1
run, retargeted to draw 2, changed in one relationship and resealed with the production seal; the sender and the live ledger are mocked, so
no subprocess is launched, no credential is read and nothing is sent.

Each case runs through the production `main()` twice, with the same expected decision:
* **fresh** — the mocked sender materializes the case as the episode's result; the runner then gates it;
* **restart** — the case already exists when the runner starts; the runner must gate it before any launch.
"continued" means the runner went on to attempt the next slot (the mock stops it there); "paused" and "integrity_stop" mean it stopped
without attempting another launch. The review's three probes (a sealed release on restart, a returned binding failure, a negative-control
acceptance) are among the cases; ordinary model outcomes (a proof, a closer refusal, a rejected l170 witness, an invalid response) must
continue.
"""
import argparse
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import shutil
import sys
import tempfile
from types import SimpleNamespace
from unittest.mock import patch

HERE = Path(__file__).resolve().parent; R6 = HERE.parents[1]
sys.path.insert(0, str(R6))
import cohort_ledger as ledger
import run as r6
import site_network

spec = importlib.util.spec_from_file_location('block2_runner', HERE/'run_block2.py'); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
BLOCK1 = R6/'cohort-live-v9'
J = lambda p: json.loads(Path(p).read_bytes()); W = lambda p, v: r6.write_json(p, v)
CASES = {  # name: (template site, expected decision)
    'proof_continues': ('l069', 'continued'),
    'closer_refusal_continues': ('l166', 'continued'),
    'negative_control_rejected_continues': ('l170', 'continued'),
    'invalid_response_continues': ('l170', 'continued'),
    'sealed_release_pauses': ('l069', 'paused'),
    'unknown_send_pauses': ('l069', 'paused'),
    'returned_binding_failure_pauses': ('l069', 'paused'),
    'provider_error_pauses': ('l069', 'paused'),
    'publication_failure_pauses': ('l069', 'paused'),
    'contradictory_proof_pauses': ('l069', 'paused'),
    'missing_evidence_pauses': ('l069', 'paused'),
    'broken_seal_pauses': ('l069', 'paused'),
    'unsealed_run_pauses': ('l069', 'paused'),
    'other_slot_pauses': ('l069', 'paused'),
    'ledger_row_mismatch_pauses': ('l069', 'paused'),
    'unreviewed_outcome_pauses': ('l069', 'paused'),
    'negative_control_certificate_accepted_stops': ('l170', 'integrity_stop'),
    'negative_control_verdict_stops': ('l170', 'integrity_stop'),
}
NEXT = {'l069': 'l070', 'l166': 'l175', 'l170': 'l175'}


def build(name, site, target):
    """The case's run directory at `target` and its live-ledger view (rows, state)."""
    shutil.copytree(BLOCK1/f'{site}-draw1', target)
    sp = J(target/'search-policy.json'); sp['draw'] = 2; W(target/'search-policy.json', sp)
    rows = ledger.parse((target/'ledger-after.ndjson').read_bytes()); consumed = True
    rec = J(target/'campaign-reconciliation.json')
    def ledger_row(change):
        change(rec); W(target/'campaign-reconciliation.json', rec)
        for i, r in enumerate(rows):
            if r['kind'] in ledger.TERMINAL and r['reservation_id'] == rec['reservation_id']: rows[i] = dict(rec)
    if name == 'invalid_response_continues':
        s = J(target/'credential-summary.json'); s['failure_category'] = 'response_schema'; W(target/'credential-summary.json', s)
        v = J(target/'transport-validation.json'); v.update(failure_category='response_schema', failure_phase='proposal'); W(target/'transport-validation.json', v)
        (target/'certificate-verdict.json').unlink()
    elif name == 'sealed_release_pauses': ledger_row(lambda r: r.update(kind='release', send_outcome=None)); consumed = False
    elif name == 'unknown_send_pauses': ledger_row(lambda r: r.update(kind='unknown', send_outcome='unknown'))
    elif name == 'returned_binding_failure_pauses':
        v = J(target/'transport-validation.json'); v['response_request_binding']['accepted'] = False
        v.update(failure_category='transport_capture_failure', failure_phase='https_transport'); W(target/'transport-validation.json', v)
    elif name == 'provider_error_pauses':
        h = J(target/'stages/proposal-1/output/http.json'); h['http_status'] = 401; W(target/'stages/proposal-1/output/http.json', h)
        s = J(target/'credential-summary.json'); s['credential_use_accepted'] = False; W(target/'credential-summary.json', s)
    elif name == 'publication_failure_pauses':
        p = J(target/'publication-final.json'); p['report_clean'] = False; W(target/'publication-final.json', p)
    elif name == 'contradictory_proof_pauses':
        c = J(target/'certificate-verdict.json'); c['accepted'] = False; W(target/'certificate-verdict.json', c)
    elif name == 'missing_evidence_pauses': (target/'transport-validation.json').unlink()
    elif name == 'other_slot_pauses': sp['draw'] = 3; W(target/'search-policy.json', sp)
    elif name == 'ledger_row_mismatch_pauses':
        for i, r in enumerate(rows):
            if r['kind'] in ledger.TERMINAL and r['reservation_id'] == rec['reservation_id']: rows[i] = {**r, 'reconciled_at_unix': r['reconciled_at_unix']+1}
    elif name == 'unreviewed_outcome_pauses':
        s = J(target/'credential-summary.json'); s['failure_category'] = 'mystery'; W(target/'credential-summary.json', s)
    elif name == 'negative_control_certificate_accepted_stops':
        c = J(target/'certificate-verdict.json'); c['accepted'] = True; W(target/'certificate-verdict.json', c)
    elif name == 'negative_control_verdict_stops': shutil.copyfile(BLOCK1/'l069-draw1/verdict.json', target/'verdict.json')
    site_network.seal(target, J(target/'seal.json')['accepted'])  # resealed as a coherent run would be
    if name == 'broken_seal_pauses': p = target/'input-ir.json'; p.write_text(p.read_text()+'\n')
    elif name == 'unsealed_run_pauses': (target/'seal.json').unlink()
    task = f'bracket-{site}'
    state = {'open_reservations': [], 'transmissions_consumed': 12, 'committed_micro_usd': 1228800, 'slots': {f'{task}/2': {'consumed': consumed}}}
    return rows, state


class NextLaunch(Exception): pass


def exercise(name, site, mode):
    with tempfile.TemporaryDirectory(prefix='block2-runner-') as temp:
        temp = Path(temp); runs = temp/'runs'; runs.mkdir(); staged = temp/'staged'
        view = build(name, site, staged); launches = []
        target = runs/f'{site}-draw2'
        if mode == 'restart': shutil.copytree(staged, target)
        def sender(argv, **kwargs):
            run = Path(argv[argv.index('--run-dir')+1]); launches.append(run.name)
            if mode == 'fresh' and run == target: shutil.copytree(staged, target); return SimpleNamespace(returncode=0)
            raise NextLaunch()
        stub = SimpleNamespace(run=sender)
        out = io.StringIO()
        with patch.object(m, 'RUNS', runs), patch.object(m, 'ORDER', (site, NEXT[site])), patch.object(m, 'DRAWS', (2,)), \
             patch.object(m, 'ledger_snapshot', lambda: view), patch.object(m, 'subprocess', stub), \
             patch.object(sys, 'argv', ['run_block2.py', '--credential-file', str(temp/'never-created')]), contextlib.redirect_stdout(out):
            try: m.main(); observed = 'completed'
            except NextLaunch: observed = 'continued'
            except SystemExit as e: observed = 'integrity_stop' if str(e).startswith('INTEGRITY STOP') else 'paused' if str(e).startswith('PAUSE') else str(e)
        line = next((json.loads(l) for l in out.getvalue().splitlines() if l.startswith('{')), {})
        return {'observed': observed, 'launches': launches, 'decision': line.get('decision'), 'outcome': line.get('outcome'), 'reasons': line.get('reasons')}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    results = {}
    for name, (site, expected) in CASES.items():
        for mode in ('fresh', 'restart'):
            got = exercise(name, site, mode)
            expected_launches = [f'{site}-draw2', f'{NEXT[site]}-draw2'] if (mode == 'fresh' and expected == 'continued') else \
                                [f'{NEXT[site]}-draw2'] if expected == 'continued' else [f'{site}-draw2'] if mode == 'fresh' else []
            assert got['observed'] == expected and got['launches'] == expected_launches, (name, mode, got)
            results[f'{name}:{mode}'] = got; print(name, mode, got['observed'], got['outcome'], got['reasons'], flush=True)
    r6.write_json(args.output, {'passed': True, 'cases': len(CASES), 'records': len(results), 'results': results, 'runner_sha256': r6.sha(HERE/'run_block2.py'),
                                'program_sha256': r6.sha(Path(__file__)), 'transmissions': 0, 'credentials_read': 0,
                                'scope': 'synthetic copies of audited block 1 runs; mocked sender and ledger; continuation decisions only'})
    print(json.dumps({'passed': True, 'cases': len(CASES), 'records': len(results)}))


if __name__ == '__main__':
    main()
