#!/usr/bin/env python3
"""Controls for the live-run audit: one relationship per mutation on copies of live-1, its ledger and the operator summary."""
import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import campaign_episode as driver
import credential
import events
import run as r6

spec = importlib.util.spec_from_file_location('r6_review_campaign_audit', ROOT/'reviews/2026-09-13/campaign_audit.py')
audit = importlib.util.module_from_spec(spec); spec.loader.exec_module(audit)
HERE = Path(__file__).resolve().parent
RUN = ROOT/'campaign-runs-v7/live-1'; SUMMARY = HERE/'R6-008-V7-LIVE1-OPERATOR-SCAN.summary.json'; CHECKPOINT = ROOT/'policies/responses-campaign-v7.checkpoint.json'
J = lambda p: json.loads(Path(p).read_bytes()); W = lambda p, v: Path(p).write_bytes(events.canonical(v)+b'\n')
EXPECTED = {
    'operator_commitment_unbound': 'live:operator_scan:bound_to_commitment_and_seal',
    'operator_seal_digest_stale': 'live:operator_scan:bound_to_commitment_and_seal',
    'operator_scan_rejected': 'live:operator_scan:bound_to_commitment_and_seal',
    'terminal_accepted_forged': 'live:terminal:pending_and_commitments_bound',
    'attribution_retrofitted': 'live:proof:attribution_live',
    'ledger_terminal_row_removed': 'live:ledger:permit_and_reconciliation_bound',
    'checkpoint_mismatch': 'live:versions:signed_policy_and_lock_bound',
    'outbound_altered': 'live:transport:local_send_checked_remote_unobservable',
    'summary_task_identity': 'live:summary:bound_to_audited_records',
}


def run_audit(run, ledgers, summary, checkpoint):
    try: result = audit.live_audit(run, ledgers, J(summary), checkpoint)
    except audit.Rejection as rejection:
        return {'accepted': False, 'rejected_case': rejection.case, 'detail': str(rejection)}
    return {'accepted': result['accepted_with_operator_scan'], 'case_count': result['case_count']}


def rechain(run, rows):
    previous = '0'*64
    for i, row in enumerate(rows):
        row.update(sequence=i, previous_hash=previous); row.pop('event_hash', None); row['event_hash'] = events.digest(row); previous = row['event_hash']
    (run/'events.ndjson').write_bytes(b''.join(events.canonical(r)+b'\n' for r in rows))


def refinalize(run, change):
    rows = events.read(run/'events.ndjson'); rows.pop(); change(run, rows); rechain(run, rows)
    for n in ('publication-scan.json', 'publication-final.json', 'seal.json'): (run/n).unlink()
    nonce = J(run/'credential-canary.json')['nonce']
    driver.finalize(run, credential.derive(nonce), nonce, J(run/'credential-summary.json'), True)


def mutate(name, run, ledgers, summary_path, checkpoint):
    summary = J(summary_path)
    if name == 'operator_commitment_unbound': summary['operator_scan']['run_receipts'][0]['commitment_bound'] = False; W(summary_path, summary)
    elif name == 'operator_seal_digest_stale': summary['operator_scan']['run_receipts'][0]['seal_sha256'] = '0'*64; W(summary_path, summary)
    elif name == 'operator_scan_rejected': summary['accepted'] = False; W(summary_path, summary)
    elif name == 'terminal_accepted_forged':
        rows = events.read(run/'events.ndjson'); rows[-1]['payload'].update(accepted=True, publication_pending=False, publication_accepted=True)
        rechain(run, rows); driver.publication_driver.seal(run, True)
    elif name == 'attribution_retrofitted':
        def change(run, rows): next(r for r in rows if r['event'] == 'recovery_finished')['payload']['proposer'] = 'canned_provider_response'
        refinalize(run, change)
    elif name == 'ledger_terminal_row_removed':
        digest = J(run/'search-policy.json')['config_sha256']; p = ledgers/'live'/(digest+'.ndjson'); lines = p.read_bytes().splitlines(True)
        p.write_bytes(b''.join(lines[:-1])); rows = [json.loads(l) for l in lines[:-1]]
        W(ledgers/'live'/(digest+'.head.json'), {'policy_sha256': digest, 'rows': len(rows), 'last_hash': rows[-1]['row_hash']})
    elif name == 'checkpoint_mismatch':
        v = J(checkpoint); v['scope'] = 'altered'; W(checkpoint, v)
    elif name == 'outbound_altered':
        def change(run, rows):
            p = run/'stages/proposal-1/output/outbound-body.json'; p.write_bytes(p.read_bytes()+b' ')
        refinalize(run, change)
    elif name == 'summary_task_identity':
        def change(run, rows):
            p = run/'credential-summary.json'; v = J(p); v['task_id'] = 'c1-c8-2p18'; W(p, v)
        refinalize(run, change)
    else: raise AssertionError(name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    results = {}
    for name in ('baseline', *EXPECTED):
        with tempfile.TemporaryDirectory(prefix='r6-live-audit-controls-') as temp:
            d = Path(temp); run = d/'live-1'; ledgers = d/'ledgers'; summary = d/'summary.json'; checkpoint = d/'checkpoint.json'
            shutil.copytree(RUN, run); shutil.copytree(ROOT/'ledgers', ledgers); shutil.copyfile(SUMMARY, summary); shutil.copyfile(CHECKPOINT, checkpoint)
            baseline = run_audit(run, ledgers, summary, checkpoint)
            assert baseline == {'accepted': True, 'case_count': len(audit.LIVE_CASES)}, baseline
            if name == 'baseline': results[name] = baseline; continue
            mutate(name, run, ledgers, summary, checkpoint)
            observed = run_audit(run, ledgers, summary, checkpoint)
            assert observed['accepted'] is False and observed['rejected_case'] == EXPECTED[name], (name, observed)
            results[name] = {'rejected': True, 'rejected_case': observed['rejected_case']}
    record = {'passed': True, 'controls': len(results), 'live_cases': len(audit.LIVE_CASES), 'results': results,
              'auditor_sha256': r6.sha(ROOT/'reviews/2026-09-13/campaign_audit.py'), 'program_sha256': r6.sha(Path(__file__)),
              'live_model_calls': 0, 'credentials_read': 0, 'scope': 'temporary copies of live-1, the ledgers, the operator summary and the checkpoint copy; one relationship per mutation'}
    r6.write_json(args.output, record)
    print(json.dumps({k: (v['rejected_case'] if 'rejected_case' in v else v) for k, v in results.items()}, indent=1))


if __name__ == '__main__':
    main()
