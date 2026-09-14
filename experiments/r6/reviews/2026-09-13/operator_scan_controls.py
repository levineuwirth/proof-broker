#!/usr/bin/env python3
"""Controls for the operator scan's run binding: one relationship per case, synthetic canary only."""
import argparse
import contextlib
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import campaign_episode as driver
import credential
import events
import run as r6

SCRIPT = Path(__file__).with_name('operator_disclosure_scan.py')
EXPECTED = {'baseline': (0, {'covered_by_scan': True, 'sealed_and_intact': True, 'commitment_record_sealed': True, 'commitment_bound': True}),
            'unscanned_run': (1, {'covered_by_scan': False}), 'missing_seal': (1, {'sealed_and_intact': False}),
            'http_changed_after_sealing': (1, {'sealed_and_intact': False, 'commitment_record_sealed': False}),
            'wrong_credential': (1, {'commitment_bound': False}), 'disclosure_in_bound_run': (1, {'covered_by_scan': True, 'sealed_and_intact': False}),
            'two_roots_colliding_names': (0, {'covered_by_scan': True, 'sealed_and_intact': True, 'commitment_record_sealed': True, 'commitment_bound': True}),
            'canary_bearing_root_name': (0, {'covered_by_scan': True, 'sealed_and_intact': True, 'commitment_record_sealed': True, 'commitment_bound': True}),
            'unreadable_bound_file_under_canary_root': (1, {'covered_by_scan': False, 'sealed_and_intact': False, 'commitment_record_sealed': False, 'commitment_bound': False})}


def sealed_run(run, header):
    out = run/'stages/proposal-1/output'; out.mkdir(parents=True); nonce = credential.nonce()
    commit = hashlib.sha256(('r6-campaign-credential-commitment-1:'+nonce+':'+header).encode()).hexdigest()
    (out/'http.json').write_bytes(events.canonical({'commitment_nonce': nonce, 'credential_commitment_sha256': commit})+b'\n')
    events.append(run, 'episode', 'episode_started', {}, task_id='verinf-d1-70'); events.append(run, 'episode', 'episode_rejected', {}, task_id='verinf-d1-70')
    driver.publication_driver.seal(run, False)


def two_roots():
    """Two valid sealed runs with identical relative file names and distinct contents: both must be covered."""
    with tempfile.TemporaryDirectory(prefix='r6-operator-scan-') as tmp:
        d = Path(tmp); canary = credential.derive(credential.nonce()); header = credential.header(canary)
        runs = [d/'first', d/'second']
        for run in runs: sealed_run(run, header)
        cred = d/'cred'; cred.write_text(header+'\n')
        p = subprocess.run([sys.executable, str(SCRIPT), '--credential-file', str(cred), '--report', str(d/'r.json'),
                            '--bind-runs', *map(str, runs), '--root', str(runs[0]), '--root', str(runs[1])], capture_output=True, text=True, timeout=120)
        lines = p.stdout.strip().splitlines(); summary = json.loads('\n'.join(lines[:-1])); receipts = summary['run_receipts']
        assert canary not in p.stdout and canary not in (d/'r.json').read_text()
        code, expected = EXPECTED['two_roots_colliding_names']
        assert p.returncode == code and len(receipts) == 2 and all(r[k] == v for r in receipts for k, v in expected.items()), (p.returncode, receipts)
        report = json.loads((d/'r.json').read_bytes())
        assert report['files_scanned'] == sum(1 for run in runs for q in run.rglob('*') if q.is_file()) and report['per_root_accepted'] == [True, True]
        return {'exit_code': p.returncode, 'scan_accepted': summary['accepted'], 'disclosures': summary['disclosures'],
                'receipt': [{k: r[k] for k in ('covered_by_scan', 'sealed_and_intact', 'commitment_record_sealed', 'commitment_bound')} for r in receipts]}


def canary_root(unreadable=False):
    """The scan root's own name carries the token: no copy may reach the report, stdout or stderr. With `unreadable`, the bound
    HTTP record is mode 000 first (precondition asserted): the run must be rejected without any traceback."""
    with tempfile.TemporaryDirectory(prefix='r6-operator-scan-') as tmp:
        d = Path(tmp); canary = credential.derive(credential.nonce()); header = credential.header(canary)
        root = d/canary; run = root/'episode'; sealed_run(run, header)
        cred = d/'cred'; cred.write_text(header+'\n')
        http = run/'stages/proposal-1/output/http.json'
        if unreadable:
            http.chmod(0)
            try: http.read_bytes(); raise AssertionError('precondition: file is readable')
            except PermissionError: pass
        try:
            p = subprocess.run([sys.executable, str(SCRIPT), '--credential-file', str(cred), '--report', str(d/'r.json'),
                                '--bind-runs', str(run), '--root', str(root)], capture_output=True, text=True, timeout=120)
        finally:
            if unreadable: http.chmod(0o600)
        report_text = (d/'r.json').read_text() if (d/'r.json').exists() else ''
        assert canary not in p.stdout and canary not in p.stderr and canary not in report_text and canary.lower() not in report_text.lower(), 'token in output'
        assert 'Traceback' not in p.stderr and p.stderr == '', 'stderr not empty: '+p.stderr[:200]
        if unreadable:
            lines = p.stdout.strip().splitlines(); summary = json.loads('\n'.join(lines[:-1])); receipt = summary['run_receipts'][0]
            code, expected = EXPECTED['unreadable_bound_file_under_canary_root']
            assert p.returncode == code and all(receipt[k] == v for k, v in expected.items()) and receipt['read_failures'] == 1, (p.returncode, receipt)
            return {'exit_code': p.returncode, 'stderr_empty': True, 'token_copies_in_report': report_text.count(canary), 'read_failures': receipt['read_failures'],
                    'receipt': {k: receipt[k] for k in ('covered_by_scan', 'sealed_and_intact', 'commitment_record_sealed', 'commitment_bound')}}
        import base64, binascii
        for form in (base64.b64encode(canary.encode()).decode(), binascii.hexlify(canary.encode()).decode()):
            assert form not in report_text, 'encoded token in report'
        lines = p.stdout.strip().splitlines(); summary = json.loads('\n'.join(lines[:-1])); receipt = summary['run_receipts'][0]
        code, expected = EXPECTED['canary_bearing_root_name']
        assert p.returncode == code and all(receipt[k] == v for k, v in expected.items()), (p.returncode, receipt)
        assert summary['roots'][0].startswith('sha256:'), summary['roots']
        return {'exit_code': p.returncode, 'scan_accepted': summary['accepted'], 'token_copies_in_report': report_text.count(canary),
                'root_label': summary['roots'][0][:14], 'receipt': {k: receipt[k] for k in ('covered_by_scan', 'sealed_and_intact', 'commitment_record_sealed', 'commitment_bound')}}


def case(name):
    if name == 'two_roots_colliding_names': return two_roots()
    if name == 'canary_bearing_root_name': return canary_root()
    if name == 'unreadable_bound_file_under_canary_root': return canary_root(unreadable=True)
    with tempfile.TemporaryDirectory(prefix='r6-operator-scan-') as tmp:
        d = Path(tmp); run = d/'run-x'; out = run/'stages/proposal-1/output'; out.mkdir(parents=True)
        nonce = credential.nonce(); canary = credential.derive(nonce); header = credential.header(canary)
        commit = hashlib.sha256(('r6-campaign-credential-commitment-1:'+nonce+':'+header).encode()).hexdigest()
        (out/'http.json').write_bytes(events.canonical({'commitment_nonce': nonce, 'credential_commitment_sha256': commit})+b'\n')
        events.append(run, 'episode', 'episode_started', {}, task_id='verinf-d1-70'); events.append(run, 'episode', 'episode_rejected', {}, task_id='verinf-d1-70')
        driver.publication_driver.seal(run, False)
        (d/'empty').mkdir(); cred = d/'cred'; cred.write_text(header+'\n'); root = run
        if name == 'unscanned_run': root = d/'empty'
        elif name == 'missing_seal': (run/'seal.json').unlink()
        elif name == 'http_changed_after_sealing':
            v = json.loads((out/'http.json').read_bytes()); v['extra'] = 'changed'; (out/'http.json').write_bytes(events.canonical(v)+b'\n')
        elif name == 'wrong_credential': cred.write_text('Bearer R6CANARYwrong0123456789abcdef\n')
        elif name == 'disclosure_in_bound_run':
            (run/'leak.txt').write_text(header)  # sealed run mutated after sealing: scan finds it and the seal breaks
        p = subprocess.run([sys.executable, str(SCRIPT), '--credential-file', str(cred), '--report', str(d/'r.json'),
                            '--bind-runs', str(run), '--root', str(root)], capture_output=True, text=True, timeout=120)
        lines = p.stdout.strip().splitlines(); summary = json.loads('\n'.join(lines[:-1])); receipt = summary['run_receipts'][0]
        assert canary not in p.stdout and canary not in (d/'r.json').read_text(), 'canary leaked into scanner output'
        code, expected = EXPECTED[name]
        assert p.returncode == code and all(receipt[k] == v for k, v in expected.items()), (name, p.returncode, receipt)
        if name == 'disclosure_in_bound_run': assert summary['accepted'] is False and summary['disclosures'] == 2  # token and header forms
        return {'exit_code': p.returncode, 'scan_accepted': summary['accepted'], 'disclosures': summary['disclosures'],
                'receipt': {k: receipt[k] for k in ('covered_by_scan', 'sealed_and_intact', 'commitment_record_sealed', 'commitment_bound')}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    results = {name: case(name) for name in EXPECTED}
    record = {'passed': True, 'controls': len(results), 'results': results, 'scanner_sha256': r6.sha(SCRIPT), 'program_sha256': r6.sha(Path(__file__)),
              'credentials_read': 0, 'scope': 'synthetic canary in temporary runs; one relationship per case'}
    r6.write_json(args.output, record)
    print(json.dumps({k: v['exit_code'] for k, v in results.items()}, indent=1))


if __name__ == '__main__':
    main()
