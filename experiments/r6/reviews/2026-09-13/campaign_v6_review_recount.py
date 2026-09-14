#!/usr/bin/env python3
"""Independent byte, population and preservation recount for the v6 review."""
import argparse
import ast
from datetime import datetime, timezone
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
import pricing_gate_v2 as pricing_gate


def module(name):
    spec = importlib.util.spec_from_file_location('v6_recount_'+name, HERE/(name+'.py'))
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value); return value


def sha(raw): return hashlib.sha256(raw).hexdigest()
def load(path): return json.loads(path.read_bytes())
def canonical(v): return json.dumps(v, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()
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
    assert len(before) == 37026 and not missing and not changed, (missing[:3], changed[:3])
    contract.verify_sources(); assert contract.NAME == 'responses_campaign_v6' and contract.config()['live_enabled'] is False
    assert not contract.campaign_ledger(True).path.exists()
    old_path = HERE/'R6-008-V5-REVIEW-BEFORE.json.gz'; old = json.loads(gzip.decompress(old_path.read_bytes()))
    older_policies = {}; prefixes = []
    for version in range(1, 6):
        folder = 'campaign-runs' if version == 1 else f'campaign-runs-v{version}'
        prefixes.append('experiments/r6/'+folder+'/')
        for name in (f'responses-campaign-v{version}.json', f'campaign-harness-v{version}.sha256.json'):
            p = ROOT/'policies'/name
            assert fingerprint(p) == old[str(p.relative_to(REPO))]
            assert all((ROOT/folder/run/'provenance/campaign-harness/policies'/name).read_bytes() == p.read_bytes()
                       for run in ('rehearsal-1', 'rehearsal-2', 'rehearsal-3'))
            older_policies[name] = {**fingerprint(p), 'retained_copies_match': 3, 'matches_independent_v5_review_snapshot': True}
    archived = {p: v for p, v in old.items() if p.startswith(tuple(prefixes))}
    assert archived and all(fingerprint(REPO/p) == v for p, v in archived.items())

    runs = {}
    for name in ('rehearsal-1', 'rehearsal-2', 'rehearsal-3'):
        run = ROOT/'campaign-runs-v6'/name; seal = load(run/'seal.json'); previous = '0'*64; rows = []
        for index, line in enumerate((run/'events.ndjson').read_bytes().splitlines()):
            row = json.loads(line); recorded = row.pop('event_hash')
            assert row['previous_hash'] == previous and row['sequence'] == index and sha(canonical(row)) == recorded
            previous = recorded; rows.append(row)
        assert seal['event_count'] == len(rows) and seal['last_event_hash'] == previous
        assert all(sha((run/p).read_bytes()) == digest for p, digest in seal['retained_sha256'].items())
        rec = load(run/'campaign-reconciliation.json'); summary = load(run/'credential-summary.json'); acct = load(run/'accounting.json')
        assert summary['accounting'] == acct and summary['task_id'] == 'verinf-d1-70'
        assert summary['evidence_complete'] is acct['evidence_complete'] is rows[-1]['payload']['evidence_complete'] is True
        runs[name] = {'events': len(rows), 'retained_files': len(seal['retained_sha256']), 'accepted': seal['accepted'],
                      'ledger_kind': rec['kind'], 'termination_established': rec['termination_established'], 'seal': fingerprint(run/'seal.json'),
                      'summary_accounting_matches_file': True, 'summary_task_id_matches_frozen_task': True, 'evidence_complete': True}
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

    def record(name): return load(args.evidence_dir/f'R6-008-V6-REVIEW-{name}.json')
    focused = record('FOCUSED'); names = [r['name'] for r in focused['checks']]
    assert focused['passed'] is True and focused['check_count'] == len(names) == len(test_campaign.CASES) == 49
    assert len(names) == len(set(names)) and set(names) == set(test_campaign.CASES) and all(r['passed'] is True for r in focused['checks'])
    assert fingerprint(ROOT/'test_campaign.py') == before['experiments/r6/test_campaign.py']
    tree = ast.parse((ROOT/'test_campaign.py').read_text())
    faults = next(node.value for node in ast.walk(tree) if isinstance(node, ast.Assign)
                  and any(isinstance(t, ast.Name) and t.id == 'FAULTS' for t in node.targets))
    frozen_faults = {ast.literal_eval(key) for key in faults.keys}
    sweep = next(r['detail'] for r in focused['checks'] if r['name'] == 'persistence_fault_sweep')
    assert set(sweep) == frozen_faults and len(sweep) == 17
    for name in ('reservation_uncertain_event_failure', 'reservation_recovered_event_failure'):
        assert sweep[name]['terminal'] == 'release' and sweep[name]['attempts'] == 1 and sweep[name]['reconciled'] is True and sweep[name]['sealed'] is True
    assert sweep['reservation_reconciled_event_failure']['terminal'] == 'send_grant'
    assert sweep['reservation_reconciled_event_failure']['evidence_complete'] is False
    recovered = sweep['reconcile_recovery_snapshot_failure']
    assert all(recovered[k] == v for k, v in {
        'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant',
        'attempts': 1, 'reconciled': True, 'allowance': 1, 'evidence_complete': False,
        'sealed': True, 'terminal_event': 'episode_rejected'}.items())
    auditor, audit_controls = module('campaign_audit'), module('campaign_audit_controls')
    audit = record('AUDIT'); control = record('AUDIT-CONTROLS')
    assert audit['accepted'] is True and audit['case_count'] == len(audit['cases']) == 76 and set(audit['cases']) == set(auditor.CASES) and all(audit['cases'].values())
    assert audit['program_sha256'] == sha((HERE/'campaign_audit.py').read_bytes())
    superseded = {'superseded_revision_audited:'+('campaign-runs' if v == 1 else f'campaign-runs-v{v}'): f'responses_campaign_v{v}' for v in range(1, 6)}
    assert len(audit_controls.EXPECTED) == 40 and len(audit_controls.PREDICATE) == 4
    assert control['passed'] is True and control['controls'] == len(audit_controls.EXPECTED)+len(audit_controls.PREDICATE)+1 == 45
    assert set(control['results']) == set(audit_controls.EXPECTED)|{'predicate_controls', 'unmutated_copy_accepted'}|set(superseded)
    assert control['results']['unmutated_copy_accepted'] == {'accepted': True, 'case_count': 76}
    assert control['results']['predicate_controls'] == {**audit_controls.PREDICATE, audit_controls.LAYOUT_POSITIVE: 'accepted'}
    for name, case in audit_controls.EXPECTED.items(): assert control['results'][name] == {'rejected': True, 'rejected_case': case}
    for name, revision in superseded.items():
        historical = control['results'][name]
        assert historical['accepted'] is True and historical['case_count'] == 76 and historical['dispatch']['superseded'] is True
        assert historical['dispatch']['revision'] == revision
    assert control['auditor_sha256'] == sha((HERE/'campaign_audit.py').read_bytes())
    assert control['program_sha256'] == sha((HERE/'campaign_audit_controls.py').read_bytes())
    op = record('OPERATOR-CONTROLS'); expected = module('operator_scan_controls').EXPECTED
    assert op['passed'] is True and op['controls'] == 9 and set(op['results']) == set(expected)
    for name, (code, _) in expected.items(): assert op['results'][name]['exit_code'] == code
    assert op['scanner_sha256'] == sha((HERE/'operator_disclosure_scan.py').read_bytes())
    assert op['program_sha256'] == sha((HERE/'operator_scan_controls.py').read_bytes())
    pilot = record('PILOT-AUDIT')
    assert pilot['accepted'] is True and pilot['case_count'] == len(pilot['cases']) == 124 and all(pilot['cases'].values())
    assert pilot['program_sha256'] == sha((HERE/'pilot_audit.py').read_bytes())
    probes = record('PROBES'); probe_module = module('campaign_v6_review_probes')
    assert probes['completed'] is True and probes['case_count'] == len(probes['cases']) == len(probe_module.CASES) == 11
    assert set(probes['cases']) == set(probe_module.CASES) and tuple(probes['expected_cases']) == probe_module.CASES
    assert probes['program_sha256'] == sha((HERE/'campaign_v6_review_probes.py').read_bytes())
    for name in ('summary_nested_evidence', 'summary_nested_allowance', 'summary_task_identity'):
        assert probes['cases'][name]['unmutated_copy'] == {'accepted': True, 'case_count': 76}
        assert probes['cases'][name]['mutated_copy']['accepted'] is False
        assert probes['cases'][name]['mutated_copy']['rejected_case'] == 'rehearsal-3:summary:bound_to_audited_records'
    probe = probes['cases']['reconciliation_recovery_snapshot_failure']
    assert probe['calls'] == {'head_failure': 1, 'terminal_row_found': 1, 'snapshot_failure': 1}
    assert probe['raised'] is None and probe['retained_lifecycle_kind'] == 'send_grant'
    assert probe['ledger_reconciled'] is True and probe['allowance_consumed'] == 1 and probe['evidence_complete'] is False
    assert probe['evidence_write_failures'] == [{'artifact': 'ledger-after', 'error': 'OSError'}]
    probe = probes['cases']['marker_release_repair_interrupted']
    assert probe['faults'] == 2 and probe['reason'] == 'completed_from_marker' and probe['torn_marker'] == 'release.json'
    assert probe['slot_predicate'] == {'accepted': True} and probe['open_reservations'] == 0 and probe['consumed'] == 1
    probe = probes['cases']['marker_unknown_torn']
    assert probe['recovery_code'] == 'campaign_marker_torn_unrecoverable' and probe['open_reservations'] == 1
    assert probe['next_reservation_rejected'] == 'campaign_reservation_open'

    # Re-derive freshness at the recorded historical time and just beyond the
    # earliest deadline. This is a local gate check, not a new source fetch.
    run = ROOT/'campaign-runs-v6/rehearsal-3'
    retained_policy = run/'provenance/campaign-harness/policies/responses-campaign-v6.json'
    assert retained_policy.read_bytes() == contract.CONFIG.read_bytes()
    policy = load(retained_policy)
    arguments = load(run/'live-arguments.json'); request = (run/'live-request.json').read_bytes()
    host = load(run/'host-pricing-admission.json')
    assert pricing_gate.admission(policy, contract.SOURCES, arguments, request, host['evaluated_at_unix']) == host
    sources = pricing_gate.source_evidence(contract.SOURCES)
    deadlines = {k: v['finished_unix']+policy['pricing_admission']['maximum_source_age_seconds'] for k, v in sources.items()}
    stale_at = min(deadlines.values())+1
    try: pricing_gate.admission(policy, contract.SOURCES, arguments, request, stale_at)
    except pricing_gate.Failure as failure:
        assert failure.code == 'pricing_capture_stale'
    else: raise AssertionError('Stale source was admitted')
    freshness = {
        'source_directory': str(contract.SOURCES.relative_to(REPO)),
        'source_files': {p.name: fingerprint(p) for p in sorted(contract.SOURCES.iterdir())},
        'maximum_source_age_seconds': policy['pricing_admission']['maximum_source_age_seconds'],
        'last_accepted_unix_by_role': deadlines,
        'last_accepted_utc_by_role': {k: datetime.fromtimestamp(v, timezone.utc).isoformat() for k, v in deadlines.items()},
        'historical_admission_rederived_exactly': True,
        'historical_evaluated_at_unix': host['evaluated_at_unix'],
        'after_deadline_test_unix': stale_at, 'after_deadline_failure_code': 'pricing_capture_stale',
        'new_fetch': False, 'billing_guarantee': False,
        'scope': 'retained-source freshness gate at two supplied times; no current provider pricing or availability claim'}
    suffixes = ('FOCUSED', 'AUDIT', 'AUDIT-CONTROLS', 'OPERATOR-CONTROLS', 'PILOT-AUDIT', 'PROBES')
    result = {'accepted': True, 'acceptance_scope': 'review recount completed; no authorization to sign or spend',
              'policy_sha256': contract.policy_sha256(), 'source_lock_sha256': sha(contract.LOCK.read_bytes()), 'live_enabled': False,
              'live_ledger_exists': False, 'real_credentials_read': 0, 'provider_calls': 0, 'new_native_episodes': 0, 'new_lean_replays': 0,
              'before_snapshot': fingerprint(args.before), 'preserved_files': len(before), 'missing': missing, 'changed': changed,
              'snapshot_scope': 'review-start working tree; experiments/r6 excluding .cache and __pycache__; not a committed baseline',
              'older_policy_files': older_policies, 'archived_run_files_matching_independent_v5_review': len(archived),
              'runs': runs, 'total_events': sum(r['events'] for r in runs.values()), 'total_sealed_entries': sum(r['retained_files'] for r in runs.values()),
              'focused_controls': 49, 'fault_sweep_cases': 17, 'audit_cases': 76,
              'audit_controls': {'baseline': 1, 'copy_mutations': 40, 'predicate_mutations': 4, 'layout_positive': 1},
              'directed_audit_controls': 45, 'superseded_positive_audits': 5,
              'operator_controls': 9, 'pilot_audit_cases': 124, 'new_review_probes': 11,
              'pricing_freshness': freshness,
              'evidence': {name: fingerprint(args.evidence_dir/f'R6-008-V6-REVIEW-{name}.json') for name in suffixes},
              'program_sha256': sha(Path(__file__).read_bytes()),
              'verification_run_notes': ['Fresh focused suite completed with approved local socket access.',
                                         'Focused tests exercise synthetic signing in temporary state; the actual disabled policy was not signed.',
                                         'Initial recount selected the compact search-policy receipt for pricing and stopped on its missing pricing field; corrected to the retained full policy before writing any result.'],
              'scope': 'byte consistency, fresh canned controls, historical audits and fault probes; no new native episode or Lean replay'}
    args.output.write_bytes(json.dumps(result, indent=2, sort_keys=True).encode()+b'\n')
    print(json.dumps({k: result[k] for k in ('accepted', 'preserved_files', 'total_events', 'total_sealed_entries', 'runs')}, indent=1))


if __name__ == '__main__': main()
