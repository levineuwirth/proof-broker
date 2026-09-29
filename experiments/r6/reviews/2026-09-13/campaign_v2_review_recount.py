#!/usr/bin/env python3
"""Independent byte/event recount for the R6-008 v2 review; no execution or key."""
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT.parents[1]
sys.path.insert(0, str(ROOT))
import campaign_contract as contract
import test_campaign


def module(name):
    spec = importlib.util.spec_from_file_location('v2_recount_'+name, HERE/(name+'.py'))
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


def sha(raw): return hashlib.sha256(raw).hexdigest()
def load(path): return json.loads(path.read_bytes())
def canonical(v): return json.dumps(v, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--before', type=Path, required=True)
    parser.add_argument('--evidence-dir', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing overwrite')
    before = json.loads(gzip.decompress(args.before.read_bytes()) if args.before.suffix == '.gz' else args.before.read_bytes())
    missing, changed = [], []
    for name, expected in before.items():
        p = REPO/name
        if not p.is_file(): missing.append(name); continue
        raw = p.read_bytes()
        if {'sha256': sha(raw), 'bytes': len(raw)} != expected: changed.append(name)
    assert not missing and not changed, (missing[:3], changed[:3])
    contract.verify_sources(); assert contract.config()['live_enabled'] is False
    assert not contract.campaign_ledger(True).path.exists()
    results = {}
    for name in ('rehearsal-1', 'rehearsal-2', 'rehearsal-3'):
        run = ROOT/'campaign-runs-v2'/name
        seal = load(run/'seal.json'); previous = '0'*64; rows = []
        for i, line in enumerate((run/'events.ndjson').read_bytes().splitlines()):
            row = json.loads(line); recorded = row.pop('event_hash')
            assert row['previous_hash'] == previous and row['sequence'] == i and sha(canonical(row)) == recorded
            previous = recorded; rows.append(row)
        assert seal['last_event_hash'] == previous and seal['event_count'] == len(rows)
        for path, digest in seal['retained_sha256'].items(): assert sha((run/path).read_bytes()) == digest
        rec = load(run/'campaign-reconciliation.json')
        results[name] = {'events': len(rows), 'retained_files': len(seal['retained_sha256']),
                         'accepted': seal['accepted'], 'ledger_kind': rec['kind'],
                         'termination_established': rec['termination_established'], 'seal_sha256': sha((run/'seal.json').read_bytes())}
        if (run/'verdict.json').exists():
            verdict = load(run/'verdict.json')
            export_sha = sha(gzip.decompress((run/'solution.ndjson.gz').read_bytes()))
            assert export_sha == verdict['solution_sha256']
            results[name].update(proof_export_sha256=export_sha,
                                 checked_declarations={k: v['checked_declarations'] for k, v in verdict['final_validation'].items()},
                                 axiom_delta=verdict['axiom_delta'])
            http = load(run/'stages/proposal-1/output/http.json')
            results[name]['grant_creation_to_durability_ns'] = http['grant_durable_at_ns']-http['grant_created_at_ns']
            results[name]['grant_durability_to_header_ns'] = http['header_send_at_ns']-http['grant_durable_at_ns']
    evidence = args.evidence_dir
    focused = load(evidence/'R6-008-V2-REVIEW-FOCUSED.json')
    assert focused['passed'] and focused['check_count'] == len(test_campaign.CASES) == 39
    names = [r['name'] for r in focused['checks']]
    assert len(names) == len(set(names)) and set(names) == set(test_campaign.CASES)
    assert all(r['passed'] is True for r in focused['checks'])
    auditor = module('campaign_audit'); audit_controls = module('campaign_audit_controls')
    audit = load(evidence/'R6-008-V2-REVIEW-AUDIT.json')
    assert audit['accepted'] is True and set(audit['cases']) == set(auditor.CASES) and all(audit['cases'].values())
    control = load(evidence/'R6-008-V2-REVIEW-AUDIT-CONTROLS.json')
    assert control['passed'] is True and control['controls'] == len(audit_controls.EXPECTED)+len(audit_controls.PREDICATE)+1 == 23
    assert set(control['results']) == set(audit_controls.EXPECTED)|{'predicate_controls', 'unmutated_copy_accepted'}
    assert control['results']['predicate_controls'] == audit_controls.PREDICATE
    for name, case in audit_controls.EXPECTED.items():
        assert control['results'][name] == {'rejected': True, 'rejected_case': case}
    op = load(evidence/'R6-008-V2-REVIEW-OPERATOR-CONTROLS.json')
    assert op['passed'] is True and set(op['results']) == set(module('operator_scan_controls').EXPECTED)
    pilot = load(evidence/'R6-008-V2-REVIEW-PILOT-AUDIT.json')
    assert pilot['accepted'] and pilot['case_count'] == 124 and all(pilot['cases'].values())
    probes = load(evidence/'R6-008-V2-REVIEW-PROBES.json')
    assert probes['completed'] is True and probes['case_count'] == len(probes['cases']) == 12
    assert probes['program_sha256'] == sha((HERE/'campaign_v2_review_probes.py').read_bytes())
    names = ('FOCUSED', 'AUDIT', 'AUDIT-CONTROLS', 'OPERATOR-CONTROLS', 'PILOT-AUDIT', 'PROBES')
    bound = {name: {'sha256': sha((evidence/f'R6-008-V2-REVIEW-{name}.json').read_bytes()),
                    'bytes': (evidence/f'R6-008-V2-REVIEW-{name}.json').stat().st_size} for name in names}
    record = {'accepted': True, 'scope': 'byte consistency, fresh controls and historical audits; no new native episode or Lean replay',
              'policy_sha256': contract.policy_sha256(), 'source_lock_sha256': sha(contract.LOCK.read_bytes()),
              'live_enabled': False, 'live_ledger_exists': False, 'real_credentials_read': 0, 'provider_calls': 0,
              'before_snapshot_sha256': sha(args.before.read_bytes()), 'preserved_files': len(before), 'missing': missing, 'changed': changed,
              'snapshot_scope': 'review-start working tree; experiments/r6 excluding .cache and __pycache__; not a committed baseline',
              'runs': results, 'total_events': sum(r['events'] for r in results.values()),
              'total_sealed_entries': sum(r['retained_files'] for r in results.values()),
              'focused_controls': 39, 'audit_cases': 63, 'audit_controls': {'baseline': 1, 'copy_mutations': 19, 'predicate_mutations': 3},
              'operator_controls': 6, 'pilot_audit_cases': 124, 'new_review_probes': 12, 'evidence': bound,
              'program_sha256': sha(Path(__file__).read_bytes())}
    args.output.write_bytes(json.dumps(record, indent=2, sort_keys=True).encode()+b'\n')
    print(json.dumps({k: record[k] for k in ('accepted', 'preserved_files', 'total_events', 'total_sealed_entries', 'runs')}, indent=1))


if __name__ == '__main__': main()
