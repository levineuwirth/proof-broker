#!/usr/bin/env python3
"""Controls for the R6-007 historical auditor: single-relationship mutations.

Each control copies the six runs, changes exactly one relationship, and requires
the auditor to reject at a named case. Mutations are audited through the
summary-only scan route, so the operator inventory cannot mask a missing
semantic comparison; the two scan-status controls use the full-report route
with a rejected summary or report. The twelve mutations are the review's own
(imported from pilot_review_probes, including its normal-finalizer reseal); nine
more cover the sequence, receipt, process, ledger, attribution, retention,
version and challenge boundaries. Positive controls require acceptance of the
unmutated copy in both routes and of a retained-only copy. Temporary copies
only; nothing connects.
"""
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
import credential
import credential_episode
import events
import run as r6


def load_module(name):
    spec = importlib.util.spec_from_file_location('r6_review_'+name, Path(__file__).with_name(name+'.py'))
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


audit = load_module('pilot_audit')
probes = load_module('pilot_review_probes')
HERE = Path(__file__).resolve().parent
EXPECTED = {  # mutation -> cases at which rejection is acceptable (first failing relationship)
    'wrong_target': {'live-2:proof:shared_checker'},
    'wrong_type': {'live-2:proof:shared_checker'},
    'forbidden_axiom': {'live-2:proof:shared_checker'},
    'invalid_proof_export': {'live-2:proof:shared_checker'},
    'wrong_reconstruction_context': {'live-2:proof:shared_checker'},
    'substituted_certificate_witness': {'live-2:proof:certificate_bound'},
    'false_host_admission': {'live-2:pricing:host_admission_rederived'},
    'broken_reservation_ledger': {'live-2:ledger:consistent'},
    'altered_outbound_body': {'live-2:transport:local_send_equals_serialized'},
    'rehearsal_file_drift': {'rehearsal-4:seal:retained_hashes'},
    'unsealed_file_drift': {'live-1:request:regenerated', 'live-1:inventory_bound'},
    'extra_live_episode': {'population:exactly_six_runs'},
    'duplicate_receipt_dropped': {'live-2:chain:expected_sequence'},
    'provider_status_500': {'live-2:transport:remote_receipt'},
    'second_ledger_row': {'live-2:ledger:consistent'},
    'attribution_retrofitted': {'live-2:proof:attribution_audited'},
    'file_added_after_scan': {'operator_scan:consistent'},
    'retained_policy_altered': {'live-2:versions:policy_lock_sources_bound'},
    'unbound_rehearsal_source': {'rehearsal-1:versions:policy_lock_sources_bound'},
    'wrong_challenge': {'live-2:proof:shared_checker'},
    'failed_process': {'live-2:live:duplicate_receipts_audited'},
}
SCAN_STATUS = {'summary_rejected': 'summary', 'report_rejected': 'report'}


def run_audit(root, retained_only=False, full_report=False, summary=None, report=None):
    summary = summary or HERE/'operator-disclosure-scan.summary.json'
    report = report or (HERE/'operator-disclosure-scan.json' if full_report else None)
    if full_report and not Path(report).exists(): raise SystemExit('full-report controls need the local operator report')
    try:
        result = audit.audit(root, live1_baseline=json.loads((HERE/'R6-007-LIVE1-INVENTORY.json').read_bytes()),
                             summary=summary, report=report, retained_only=retained_only)
    except audit.Rejection as rejection:
        return {'accepted': False, 'rejected_case': rejection.case, 'detail': str(rejection)}
    return {'accepted': result['accepted'], 'case_count': result['case_count']}


def reclose(run):
    """Rejected-episode counterpart of the review's refinalize: regenerate scan, terminal event and seal."""
    rows = events.read(run/'events.ndjson'); assert rows[-1]['event'] == 'episode_rejected'; rows.pop(); probes.rechain(run, rows)
    for n in ('publication-scan.json', 'publication-final.json', 'seal.json'): (run/n).unlink()
    nonce = probes.load(run/'credential-canary.json')['nonce']
    accepted, _, _ = credential_episode.finalize(run, credential.derive(nonce), nonce, probes.load(run/'credential-summary.json'))
    assert not accepted


def mutate(root, name):
    live2 = root/'live-2'
    if name in probes.MUTATIONS:
        if name == 'rehearsal_file_drift': (root/'rehearsal-4/solution.ndjson.gz').write_bytes(b'not gzip')
        elif name == 'unsealed_file_drift':
            p = root/'live-1/prepared.json'; v = probes.load(p); v['fragment'] = 'wrong_fragment'; probes.write(p, v)
        elif name == 'extra_live_episode': shutil.copytree(live2, root/'live-3')
        else: probes.refinalize(live2, lambda run, rows: probes.alter(run, rows, name))
        return
    if name == 'duplicate_receipt_dropped':
        def change(run, rows):
            hits = [i for i, r in enumerate(rows) if r['stage'] == 'proposal-1' and r['event'] == 'stage_started']
            assert len(hits) == 2; rows.pop(hits[1])
        probes.refinalize(live2, change)
        # refinalize asserts 52 events; one fewer is the point of this control
    elif name == 'provider_status_500':
        def change(run, rows):
            p = run/'stages/proposal-1/output/http.json'; h = probes.load(p); h['http_status'] = 500; probes.write(p, h)
        probes.refinalize(live2, change)
    elif name == 'second_ledger_row':
        p = live2/'reservation-ledger.ndjson'; p.write_bytes(p.read_bytes()*2)
        probes.refinalize(live2, lambda run, rows: None)
    elif name == 'attribution_retrofitted':
        def change(run, rows):
            hit = next(r for r in rows if r['event'] == 'recovery_finished'); hit['payload']['proposer'] = 'live_model_response'
        probes.refinalize(live2, change)
    elif name == 'file_added_after_scan':
        (root/'rehearsal-1/added-later.json').write_bytes(b'{}\n')
    elif name == 'unbound_rehearsal_source':
        run = root/'rehearsal-1'; source = run/'provenance/pilot-harness/pilot_network.py'
        source.write_bytes(source.read_bytes()+b'\n# changed source, unchanged source lock\n'); reclose(run)
    elif name == 'wrong_challenge':
        def change(run, rows):
            p = run/'verdict.json'; v = probes.load(p); v['challenge_sha256'] = '0'*64; probes.write(p, v)
            for row in rows:
                if row['event'] == 'proof_validated': row['payload']['verdict_sha256'] = r6.sha(p)
        probes.refinalize(live2, change)
    elif name == 'failed_process':
        def change(run, rows):
            p = run/'stages/proposal-1/proposal-1.process.json'; v = probes.load(p); v['exit_code'] = 1; probes.write(p, v)
        probes.refinalize(live2, change)
    elif name == 'retained_policy_altered':
        def change(run, rows):
            p = run/'provenance/pilot-harness/policies/responses-live-pilot-v1.json'
            v = probes.load(p); v['live_enabled'] = False; p.write_bytes(events.canonical(v)+b'\n')
        probes.refinalize(live2, change)
    else:
        raise AssertionError(name)


def refinalize_tolerant(name, root):
    """duplicate_receipt_dropped leaves 51 events; the review's refinalize seals first, then asserts 52."""
    try: mutate(root, name)
    except AssertionError:
        if name != 'duplicate_receipt_dropped' or not (root/'live-2/seal.json').exists(): raise


def scan_status_control(kind, temp):
    """Reject when either the summary or the full report says the scan was not accepted, with digests kept consistent."""
    summary = probes.load(HERE/'operator-disclosure-scan.summary.json'); report = probes.load(HERE/'operator-disclosure-scan.json')
    assert summary['accepted'] is True and report['accepted'] is True
    if kind == 'report': report['accepted'] = False
    else: summary['accepted'] = False
    rp = Path(temp)/'report.json'; rp.write_text(json.dumps(report))
    summary['full_report_sha256'] = r6.sha(rp); summary['full_report_bytes'] = rp.stat().st_size
    sp = Path(temp)/'summary.json'; sp.write_text(json.dumps(summary))
    return run_audit(ROOT/'pilot-runs', full_report=True, summary=sp, report=rp)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runs', type=Path, default=ROOT/'pilot-runs')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    results = {}
    with tempfile.TemporaryDirectory(prefix='r6-007-audit-controls-') as temp:
        root = Path(temp)/'pilot-runs'; shutil.copytree(args.runs, root)
        for route, full in (('summary_only', False), ('full_report', True)):
            baseline = run_audit(root, full_report=full)
            assert baseline == {'accepted': True, 'case_count': len(audit.CASES)}, (route, baseline)
            results['unmutated_copy_accepted:'+route] = baseline
        for p in list((root/'live-1').rglob('*.olean')): p.unlink()
        retained = run_audit(root, retained_only=True, full_report=True)
        assert retained == {'accepted': True, 'case_count': len(audit.CASES)}, retained
        results['retained_only_copy_accepted'] = retained
        full_on_retained = run_audit(root, full_report=True)
        assert full_on_retained['accepted'] is False and full_on_retained['rejected_case'] == 'live-1:inventory_bound', full_on_retained
        results['full_mode_rejects_missing_historical_files'] = full_on_retained
        for kind in SCAN_STATUS:
            observed = scan_status_control(SCAN_STATUS[kind], temp)
            assert observed['accepted'] is False and observed['rejected_case'] == 'operator_scan:consistent', (kind, observed)
            results[kind] = {'rejected': True, 'rejected_case': observed['rejected_case'], 'route': 'full_report'}
    for name in EXPECTED:
        with tempfile.TemporaryDirectory(prefix='r6-007-audit-controls-') as temp:
            root = Path(temp)/'pilot-runs'; shutil.copytree(args.runs, root)
            assert run_audit(root)['accepted'] is True
            refinalize_tolerant(name, root)
            observed = run_audit(root)  # summary-only: the inventory cannot mask the semantic case
            assert observed['accepted'] is False, (name, observed)
            assert observed['rejected_case'] in EXPECTED[name], (name, observed)
            results[name] = {'rejected': True, 'rejected_case': observed['rejected_case'], 'allowed_cases': sorted(EXPECTED[name]), 'route': 'summary_only'}
    record = {'passed': True, 'controls': len(results), 'mutations': len(EXPECTED)+len(SCAN_STATUS), 'named_cases': len(audit.CASES), 'results': results,
              'auditor_sha256': r6.sha(HERE/'pilot_audit.py'), 'probes_sha256': r6.sha(HERE/'pilot_review_probes.py'),
              'program_sha256': r6.sha(Path(__file__)), 'live_model_calls': 0, 'credentials_read': 0,
              'scope': 'temporary copies; every mutation is one relationship; rejection case names are pinned; mutations audited summary-only'}
    r6.write_json(args.output, record)
    print(json.dumps({k: record[k] for k in ('passed', 'controls', 'mutations', 'named_cases')}, indent=1))
    print(json.dumps({k: v['rejected_case'] for k, v in results.items() if 'rejected_case' in v}, indent=1))


if __name__ == '__main__':
    main()
