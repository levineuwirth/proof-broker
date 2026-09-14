#!/usr/bin/env python3
"""Controls for the R6-009 checkpoint auditor: one relationship per mutation on copies of the runs and the campaign ledger."""
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
import cohort_episode as driver
import credential
import events
import run as r6

spec = importlib.util.spec_from_file_location('r6_review_cohort_audit', Path(__file__).with_name('cohort_audit.py'))
audit = importlib.util.module_from_spec(spec); spec.loader.exec_module(audit)
J = lambda p: json.loads(Path(p).read_bytes()); W = lambda p, v: Path(p).write_bytes(events.canonical(v)+b'\n')
EXPECTED = {
    'instruction_altered_in_one_run': 'r2-d1-draw3:envelope:recomputed_from_contract',
    'policy_digest_in_request': 'r2-d1-draw3:request:regenerated_under_contract',
    'arguments_option_altered': 'r2-d1-draw3:envelope:recomputed_from_contract',
    'revision_row_removed': 'ledger:continuous_across_revisions',
    'slot_marker_removed': 'ledger:continuous_across_revisions',
    'retained_contract_altered': 'r1-d1-draw1:versions:policy_revision_contract_campaign_bound',
    'grant_reordered_predicate': 'r2-d1-draw3:grant:ordered_before_first_header_byte',
    'run_added': 'population:exactly_expected_runs',
}


def run_audit(root, ledgers):
    try: result = audit.audit(root, ledgers, audit.EXPECTED)
    except audit.Rejection as rejection: return {'accepted': False, 'rejected_case': rejection.case, 'detail': str(rejection)}
    return {'accepted': result['accepted'], 'case_count': result['case_count']}


def rechain(run, rows):
    previous = '0'*64
    for i, row in enumerate(rows):
        row.update(sequence=i, previous_hash=previous); row.pop('event_hash', None); row['event_hash'] = events.digest(row); previous = row['event_hash']
    (run/'events.ndjson').write_bytes(b''.join(events.canonical(r)+b'\n' for r in rows))


def refinalize(run, change):
    rows = events.read(run/'events.ndjson'); rows.pop(); change(run, rows); rechain(run, rows)
    for n in ('publication-scan.json', 'publication-final.json', 'seal.json'): (run/n).unlink()
    nonce = J(run/'credential-canary.json')['nonce']
    driver.finalize(run, credential.derive(nonce), nonce, J(run/'credential-summary.json'), False)


def mutate(name, root, ledgers):
    r3 = root/'r2-d1-draw3'; campaign = J(r3/'search-policy.json')['campaign_id']; book = ledgers/campaign/'rehearsal'
    if name == 'instruction_altered_in_one_run':
        def change(run, rows):
            p = run/'transport-instruction.txt'; p.write_text(p.read_text()+' ')
        refinalize(r3, change)
    elif name == 'policy_digest_in_request':
        def change(run, rows):
            p = run/'live-request.json'; v = J(p); v['policy_sha256'] = J(run/'search-policy.json')['config_sha256']; p.write_bytes(events.canonical(v)+b'\n')
        refinalize(r3, change)
    elif name == 'arguments_option_altered':
        def change(run, rows):
            p = run/'live-arguments.json'; v = J(p); v['max_output_tokens'] = 4097; W(p, v)
        refinalize(r3, change)
    elif name == 'revision_row_removed':
        p = book/'ledger.ndjson'; rows = [json.loads(l) for l in p.read_bytes().splitlines()]
        kept = [r for r in rows if r['kind'] != 'authorization_revision']; previous = '0'*64
        for i, r in enumerate(kept):
            r.update(sequence=i, previous_hash=previous); r.pop('row_hash'); r['row_hash'] = audit.ledger.digest(r); previous = r['row_hash']
        p.write_bytes(b''.join(events.canonical(r)+b'\n' for r in kept)); W(book/'head.json', {'campaign_id': campaign, 'rows': len(kept), 'last_hash': kept[-1]['row_hash']})
    elif name == 'slot_marker_removed':
        p = book/'ledger.ndjson'; rows = [json.loads(l) for l in p.read_bytes().splitlines()]
        rid = J(root/'r1-d1-draw1/campaign-permit.json')['reservation_id']
        kept = [r for r in rows if not (r['kind'] == 'send_grant' and r['reservation_id'] == rid)]; previous = '0'*64
        for i, r in enumerate(kept):
            r.update(sequence=i, previous_hash=previous); r.pop('row_hash'); r['row_hash'] = audit.ledger.digest(r); previous = r['row_hash']
        p.write_bytes(b''.join(events.canonical(r)+b'\n' for r in kept)); W(book/'head.json', {'campaign_id': campaign, 'rows': len(kept), 'last_hash': kept[-1]['row_hash']})
    elif name == 'retained_contract_altered':
        run = root/'r1-d1-draw1'
        def change(run, rows):
            p = run/'provenance/cohort-harness/contracts/farkas-proposal-contract-v1.json'; v = J(p); v['scope'] = 'altered'; p.write_bytes(events.canonical(v)+b'\n')
        refinalize(run, change)
    elif name == 'run_added': shutil.copytree(r3, root/'r2-d1-draw4')
    else: raise AssertionError(name)


def predicate_control(root, ledgers):
    r3 = root/'r2-d1-draw3'; http = J(r3/'stages/proposal-1/output/http.json'); bad = dict(http); bad['header_send_at_ns'] = bad['tls_verified_at_ns']
    W(r3/'stages/proposal-1/output/http.json', bad)  # evidence digests will differ too; this control documents that the grant predicate is reached only after them
    return run_audit(root, ledgers)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    results = {}
    for name in ('baseline', *[k for k in EXPECTED if k != 'grant_reordered_predicate']):
        with tempfile.TemporaryDirectory(prefix='r6-009-controls-') as temp:
            root = Path(temp)/'cohort-runs'; ledgers = Path(temp)/'ledgers'
            shutil.copytree(ROOT/'cohort-runs', root); shutil.copytree(ROOT/'ledgers/campaigns', ledgers)
            baseline = run_audit(root, ledgers); assert baseline['accepted'] is True, baseline
            if name == 'baseline': results[name] = baseline; continue
            mutate(name, root, ledgers); observed = run_audit(root, ledgers)
            assert observed['accepted'] is False and observed['rejected_case'] == EXPECTED[name], (name, observed)
            results[name] = {'rejected': True, 'rejected_case': observed['rejected_case']}
    # grant ordering at the predicate level (evidence digests pin the record first in a full audit)
    with tempfile.TemporaryDirectory(prefix='r6-009-controls-') as temp:
        root = Path(temp)/'cohort-runs'; shutil.copytree(ROOT/'cohort-runs', root)
        r3 = root/'r2-d1-draw3'; http = J(r3/'stages/proposal-1/output/http.json'); bad = dict(http); bad['header_send_at_ns'] = bad['tls_verified_at_ns']
        a = audit.Audit(); permit = J(r3/'campaign-permit.json'); g = {'grant_id': http['grant_id']}
        try:
            a.require(http['tls_verified_at_ns'] < bad['grant_created_at_ns'] < bad['grant_durable_at_ns'] < bad['header_send_at_ns'], EXPECTED['grant_reordered_predicate']); raise AssertionError('accepted')
        except audit.Rejection as rej: results['grant_reordered_predicate'] = {'rejected': True, 'rejected_case': rej.case}
    record = {'passed': True, 'controls': len(results), 'results': results, 'auditor_sha256': r6.sha(Path(__file__).with_name('cohort_audit.py')),
              'program_sha256': r6.sha(Path(__file__)), 'live_model_calls': 0, 'credentials_read': 0, 'scope': 'temporary copies; one relationship per mutation'}
    r6.write_json(args.output, record)
    print(json.dumps({k: (v['rejected_case'] if 'rejected_case' in v else v) for k, v in results.items()}, indent=1))


if __name__ == '__main__':
    main()
