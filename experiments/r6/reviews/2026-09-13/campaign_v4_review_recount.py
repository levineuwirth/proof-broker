#!/usr/bin/env python3
"""Byte, population and provenance recount for the independent R6-008 v4 review."""
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
    spec = importlib.util.spec_from_file_location('v4_recount_'+name, HERE/(name+'.py'))
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value); return value


def sha(raw): return hashlib.sha256(raw).hexdigest()
def load(path): return json.loads(path.read_bytes())
def canonical(value): return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()
def fingerprint(path):
    raw = path.read_bytes(); return {'sha256': sha(raw), 'bytes': len(raw)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--before', type=Path, required=True)
    parser.add_argument('--evidence-dir', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing overwrite')
    before = json.loads(gzip.decompress(args.before.read_bytes()) if args.before.suffix == '.gz' else args.before.read_bytes())
    missing = [p for p in before if not (REPO/p).is_file()]
    changed = [p for p, v in before.items() if (REPO/p).is_file() and fingerprint(REPO/p) != v]
    assert not missing and not changed, (missing[:3], changed[:3])
    contract.verify_sources(); assert contract.NAME == 'responses_campaign_v4' and contract.config()['live_enabled'] is False
    assert not contract.campaign_ledger(True).path.exists()

    old_path = HERE/'R6-008-V3-REVIEW-BEFORE.json.gz'
    old = json.loads(gzip.decompress(old_path.read_bytes()))
    restored = {}
    for name in ('responses-campaign-v3.json', 'campaign-harness-v3.sha256.json'):
        p = ROOT/'policies'/name; observed = fingerprint(p)
        assert observed == old[str(p.relative_to(REPO))]
        for run in ('rehearsal-1', 'rehearsal-2', 'rehearsal-3'):
            assert (ROOT/'campaign-runs-v3'/run/'provenance/campaign-harness/policies'/name).read_bytes() == p.read_bytes()
        restored[name] = {**observed, 'retained_copies_match': 3, 'matches_independent_v3_review_snapshot': True}
    prefixes = tuple('experiments/r6/'+p+'/' for p in ('campaign-runs', 'campaign-runs-v2', 'campaign-runs-v3'))
    archived = {p: v for p, v in old.items() if p.startswith(prefixes)}
    assert archived and all(fingerprint(REPO/p) == v for p, v in archived.items())

    runs = {}
    for name in ('rehearsal-1', 'rehearsal-2', 'rehearsal-3'):
        run = ROOT/'campaign-runs-v4'/name; seal = load(run/'seal.json'); previous = '0'*64; rows = []
        for i, line in enumerate((run/'events.ndjson').read_bytes().splitlines()):
            row = json.loads(line); recorded = row.pop('event_hash')
            assert row['previous_hash'] == previous and row['sequence'] == i and sha(canonical(row)) == recorded
            previous = recorded; rows.append(row)
        assert seal['event_count'] == len(rows) and seal['last_event_hash'] == previous
        for p, digest in seal['retained_sha256'].items(): assert sha((run/p).read_bytes()) == digest
        rec = load(run/'campaign-reconciliation.json')
        runs[name] = {'events': len(rows), 'retained_files': len(seal['retained_sha256']), 'accepted': seal['accepted'],
                      'ledger_kind': rec['kind'], 'termination_established': rec['termination_established'], 'seal': fingerprint(run/'seal.json')}
        if (run/'verdict.json').exists():
            verdict = load(run/'verdict.json'); export_sha = sha(gzip.decompress((run/'solution.ndjson.gz').read_bytes()))
            assert export_sha == verdict['solution_sha256']
            runs[name].update(proof_export_sha256=export_sha, axiom_delta=verdict['axiom_delta'],
                              checked_declarations={k: v['checked_declarations'] for k, v in verdict['final_validation'].items()})
            http = load(run/'stages/proposal-1/output/http.json')
            runs[name].update(grant_creation_to_durability_ns=http['grant_durable_at_ns']-http['grant_created_at_ns'],
                              grant_durability_to_header_ns=http['header_send_at_ns']-http['grant_durable_at_ns'])
    assert [runs[n]['events'] for n in runs] == [20, 18, 51]
    assert [runs[n]['retained_files'] for n in runs] == [215, 209, 281]

    evidence = args.evidence_dir
    def record(name): return load(evidence/f'R6-008-V4-REVIEW-{name}.json')
    focused = record('FOCUSED')
    names = [r['name'] for r in focused['checks']]
    assert focused['passed'] is True and focused['check_count'] == len(names) == len(test_campaign.CASES) == 47
    assert len(set(names)) == len(names) and set(names) == set(test_campaign.CASES)
    assert all(r['passed'] is True for r in focused['checks'])
    assert fingerprint(ROOT/'test_campaign.py') == before['experiments/r6/test_campaign.py']
    auditor = module('campaign_audit'); audit_controls = module('campaign_audit_controls')
    audit = record('AUDIT')
    assert audit['accepted'] is True and set(audit['cases']) == set(auditor.CASES) and all(audit['cases'].values()) and audit['case_count'] == 73
    assert audit['program_sha256'] == sha((HERE/'campaign_audit.py').read_bytes())
    control = record('AUDIT-CONTROLS')
    superseded = {'superseded_revision_audited:campaign-runs': 'responses_campaign_v1',
                  'superseded_revision_audited:campaign-runs-v2': 'responses_campaign_v2',
                  'superseded_revision_audited:campaign-runs-v3': 'responses_campaign_v3'}
    assert control['passed'] is True and control['controls'] == len(audit_controls.EXPECTED)+len(audit_controls.PREDICATE)+1 == 36
    assert set(control['results']) == set(audit_controls.EXPECTED)|{'predicate_controls', 'unmutated_copy_accepted'}|set(superseded)
    assert control['results']['unmutated_copy_accepted'] == {'accepted': True, 'case_count': 73}
    assert control['results']['predicate_controls'] == audit_controls.PREDICATE
    for name, case in audit_controls.EXPECTED.items(): assert control['results'][name] == {'rejected': True, 'rejected_case': case}
    for name, revision in superseded.items():
        historical = control['results'][name]
        assert historical['accepted'] is True and historical['case_count'] == 73
        assert historical['dispatch']['superseded'] is True and historical['dispatch']['revision'] == revision
    assert control['auditor_sha256'] == sha((HERE/'campaign_audit.py').read_bytes())
    assert control['program_sha256'] == sha((HERE/'campaign_audit_controls.py').read_bytes())
    op = record('OPERATOR-CONTROLS'); op_module = module('operator_scan_controls')
    assert op['passed'] is True and op['controls'] == 8 and set(op['results']) == set(op_module.EXPECTED)
    for name, (code, _) in op_module.EXPECTED.items(): assert op['results'][name]['exit_code'] == code
    assert op['scanner_sha256'] == sha((HERE/'operator_disclosure_scan.py').read_bytes())
    assert op['program_sha256'] == sha((HERE/'operator_scan_controls.py').read_bytes())
    pilot = record('PILOT-AUDIT')
    assert pilot['accepted'] is True and pilot['case_count'] == len(pilot['cases']) == 124 and all(pilot['cases'].values())
    assert pilot['program_sha256'] == sha((HERE/'pilot_audit.py').read_bytes())
    probes = record('PROBES'); probe_module = module('campaign_v4_review_probes')
    assert probes['completed'] is True and probes['case_count'] == len(probes['cases']) == len(probe_module.CASES) == 12
    assert set(probes['cases']) == set(probe_module.CASES) and tuple(probes['expected_cases']) == probe_module.CASES
    assert probes['program_sha256'] == sha((HERE/'campaign_v4_review_probes.py').read_bytes())
    for name in ('attempt_identity_removed', 'summary_evidence_contradiction'):
        assert probes['cases'][name]['unmutated_copy'] == probes['cases'][name]['mutated_copy'] == {'accepted': True, 'case_count': 73}
    names = ('FOCUSED', 'AUDIT', 'AUDIT-CONTROLS', 'OPERATOR-CONTROLS', 'PILOT-AUDIT', 'PROBES')
    result = {'accepted': True, 'acceptance_scope': 'recount completed; this is not approval of the disabled policy',
              'policy_sha256': contract.policy_sha256(), 'source_lock_sha256': sha(contract.LOCK.read_bytes()),
              'live_enabled': False, 'live_ledger_exists': False, 'real_credentials_read': 0, 'provider_calls': 0, 'new_native_episodes': 0,
              'before_snapshot': fingerprint(args.before), 'preserved_files': len(before), 'missing': missing, 'changed': changed,
              'snapshot_scope': 'review-start working tree; experiments/r6 excluding .cache and __pycache__; not a committed baseline',
              'restored_v3_files': restored, 'archived_run_files_matching_independent_v3_review': len(archived),
              'runs': runs, 'total_events': sum(r['events'] for r in runs.values()),
              'total_sealed_entries': sum(r['retained_files'] for r in runs.values()),
              'focused_controls': 47, 'audit_cases': 73, 'audit_controls': {'baseline': 1, 'copy_mutations': 31, 'predicate_mutations': 4},
              'superseded_positive_audits': 3, 'operator_controls': 8, 'pilot_audit_cases': 124, 'new_review_probes': 12,
              'evidence': {name: fingerprint(evidence/f'R6-008-V4-REVIEW-{name}.json') for name in names},
              'program_sha256': sha(Path(__file__).read_bytes()),
              'scope': 'byte consistency, fresh canned controls, historical audits and fault probes; no new native episode or Lean replay'}
    args.output.write_bytes(json.dumps(result, indent=2, sort_keys=True).encode()+b'\n')
    print(json.dumps({k: result[k] for k in ('accepted', 'preserved_files', 'total_events', 'total_sealed_entries', 'restored_v3_files', 'runs')}, indent=1))


if __name__ == '__main__': main()
