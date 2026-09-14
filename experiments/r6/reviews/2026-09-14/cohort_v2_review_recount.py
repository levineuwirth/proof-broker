#!/usr/bin/env python3
"""Independent byte and count recount of R6-009 v2 at eb8bf13. No native replay."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]; REPO = ROOT.parents[1]
sys.path.insert(0, str(ROOT))
import cohort_contract as contract
import run as r6
import test_cohort

spec = importlib.util.spec_from_file_location('cohort_v2_recount_audit', Path(__file__).with_name('cohort_audit.py'))
audit = importlib.util.module_from_spec(spec); spec.loader.exec_module(audit)
control_spec = importlib.util.spec_from_file_location('cohort_v2_recount_controls', Path(__file__).with_name('cohort_audit_controls.py'))
control_module = importlib.util.module_from_spec(control_spec); control_spec.loader.exec_module(control_module)
J = lambda p: json.loads(Path(p).read_bytes())
SHA = lambda b: hashlib.sha256(b).hexdigest()
CANON = lambda v: json.dumps(v, ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode()
RUNS = ('r1-d1-draw1', 'r1-d1-draw2-format', 'r1-c8-draw1', 'r2-d1-draw1-refused', 'r2-d1-draw2', 'r2-c8-draw2')
BODY_NAMES = ('serialized-body.json', 'outbound-body.json', 'received-body.json')


def chained(path, field):
    rows = []; previous = '0'*64
    for line in path.read_bytes().splitlines():
        row = json.loads(line); h = row.pop(field)
        assert row['sequence'] == len(rows) and row['previous_hash'] == previous and SHA(CANON(row)) == h
        row[field] = h; rows.append(row); previous = h
    return rows


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--before', type=Path, required=True); p.add_argument('--evidence', type=Path, required=True); p.add_argument('--output', type=Path, required=True)
    args = p.parse_args(); assert not args.output.exists()
    contract.verify_sources(); policy = contract.config(); assert policy['live_enabled'] is False
    assert not contract.campaign_ledger(True).path.exists()
    assert set(p.name for p in (ROOT/'cohort-runs-v2').iterdir()) == set(RUNS)
    group = {}; runs = {}; event_count = sealed_count = 0
    reservation_ids, grant_ids, nonces = [], [], []
    for name in RUNS:
        run = ROOT/'cohort-runs-v2'/name; task_id = J(run/'search-policy.json')['task_id']
        rows = chained(run/'events.ndjson', 'event_hash'); seal = J(run/'seal.json')
        assert seal['last_event_hash'] == rows[-1]['event_hash'] and seal['event_count'] == len(rows)
        for inventory in ('retained_sha256', 'ephemeral_sha256'):
            for path, h in seal[inventory].items(): assert r6.sha(run/path) == h, (name, inventory, path)
        entries = len(seal['retained_sha256'])+len(seal['ephemeral_sha256'])
        event_count += len(rows); sealed_count += entries
        out = run/'stages/proposal-1/output'; bodies = {}
        for filename in BODY_NAMES:
            path = out/filename; body = path.read_bytes() if path.exists() else None
            bodies[filename] = {'bytes': len(body), 'sha256': SHA(body)} if body is not None else None
            if body is not None: group.setdefault(task_id, {}).setdefault(filename, []).append(SHA(body))
        if (run/'campaign-permit.json').exists():
            permit = J(run/'campaign-permit.json'); http = J(out/'http.json')
            reservation_ids.append(permit['reservation_id']); nonces.append(http['commitment_nonce'])
            if http['grant_id']: grant_ids.append(http['grant_id'])
            run_policy = J(run/'transport-policy.json'); limits = run_policy['limits']; rates = run_policy['pricing']['nano_usd_per_token']
            expected_cost = (limits['input_tokens_reserved']*max(rates['input'], rates['cache_write'])+limits['output_tokens']*rates['output']+999)//1000
            assert expected_cost == permit['reserved_micro_usd'] == permit['reservation']['reserved_micro_usd'] == 102400
        verdict = J(run/'verdict.json') if (run/'verdict.json').exists() else None
        if verdict: assert all(v == {'added': [], 'removed': []} for v in verdict['axiom_delta'].values())
        runs[name] = {'task_id': task_id, 'event_count': len(rows), 'sealed_entries': entries,
                      'retained_entries': len(seal['retained_sha256']), 'ephemeral_entries': len(seal['ephemeral_sha256']), 'bodies': bodies,
                      'solution_sha256': verdict['solution_sha256'] if verdict else None,
                      'declarations': {k: v['checked_declarations'] for k, v in verdict['final_validation'].items()} if verdict else None,
                      'axiom_delta': verdict['axiom_delta'] if verdict else None}
    assert event_count == 238 and sealed_count == 1632
    for task, counts in [('verinf-d1-70', (3, 2, 2)), ('c1-c8-2p18', (2, 2, 2))]:
        assert [len(group[task][n]) for n in BODY_NAMES] == list(counts)
        assert len({h for bodies in group[task].values() for h in bodies}) == 1
    assert len(reservation_ids) == len(set(reservation_ids)) == 5
    assert len(grant_ids) == len(set(grant_ids)) == 4 and len(nonces) == len(set(nonces)) == 5
    ledger_rows = chained(contract.campaign_ledger(False).path, 'row_hash')
    permits = {r['reservation_id']: r for r in ledger_rows if r['kind'] == 'reservation'}
    terminal = {r['reservation_id']: r for r in ledger_rows if r['kind'] in ('send_grant', 'release', 'unknown')}
    committed = sum(r['reserved_micro_usd'] for rid, r in permits.items() if terminal[rid]['kind'] != 'release')
    consumed = sorted((permits[rid]['task_id'], permits[rid]['draw']) for rid, row in terminal.items() if row['kind'] in ('send_grant', 'unknown'))
    assert len(ledger_rows) == 12 and committed == 409600 and len(consumed) == 4 and set(terminal) == set(permits)
    focused = J(args.evidence/'R6-009-V2-REVIEW-FOCUSED.json'); names = [v['name'] for v in focused['checks']]
    assert focused['passed'] is True and all(v['passed'] is True for v in focused['checks'])
    assert len(names) == len(set(names)) == focused['check_count'] == 27 and set(names) == set(test_cohort.CASES)
    for record_name, revision, count in [('AUDIT', 'farkas_cohort_v2', 181), ('SUPERSEDED', 'farkas_cohort_v1', 147)]:
        record = J(args.evidence/f'R6-009-V2-REVIEW-{record_name}.json')
        assert record['accepted'] is True and record['case_count'] == count and len(record['cases']) == count
        assert set(record['cases']) == set(audit.expected_cases(audit.POPULATIONS[revision])) and all(record['cases'].values())
    controls = J(args.evidence/'R6-009-V2-REVIEW-CONTROLS.json')
    assert controls['passed'] is True and controls['controls'] == len(controls['results']) == 29
    assert set(controls['results']) == set(control_module.CONTROLS) and controls['expected_controls'] == list(control_module.CONTROLS)
    assert controls['program_sha256'] == r6.sha(Path(__file__).with_name('cohort_audit_controls.py'))
    before = J(args.before); changed = []; missing = []
    for name, value in before.items():
        path = REPO/name
        if not path.is_file(): missing.append(name)
        elif path.stat().st_size != value['bytes'] or r6.sha(path) != value['sha256']: changed.append(name)
    assert not changed and not missing
    result = {'complete': True, 'reviewed_commit': 'eb8bf13', 'source_lock_verified': True, 'live_enabled': False,
              'scope': 'independent byte/count and retained-report checks; no native Lean replay or inference attestation',
              'live_model_calls': 0, 'real_credentials_read': 0, 'runs': runs, 'event_hashes': event_count, 'sealed_entries': sealed_count,
              'retained_entries': sum(v['retained_entries'] for v in runs.values()), 'ephemeral_entries': sum(v['ephemeral_entries'] for v in runs.values()),
              'per_task_bodies': group, 'ledger': {'rows': len(ledger_rows), 'kinds': [r['kind'] for r in ledger_rows],
                  'committed_micro_usd': committed, 'consumed_slots': consumed, 'open_reservations': []},
              'checked_populations': {'focused': 27, 'v2_audit': 181, 'v1_audit': 147, 'audit_controls': 29},
              'preservation': {'inventory_path': str(args.before), 'inventory_sha256': r6.sha(args.before), 'checked_files': len(before),
                               'changed': changed, 'missing': missing, 'scope': 'review-start r6 files, excluding .cache and __pycache__'},
              'program_sha256': r6.sha(Path(__file__)),
              'evidence': {p.name: {'bytes': p.stat().st_size, 'sha256': r6.sha(p)} for p in sorted(args.evidence.glob('R6-009-V2-REVIEW-*.json'))}}
    r6.write_json(args.output, result)
    print(json.dumps({k: result[k] for k in ('event_hashes', 'sealed_entries', 'ledger', 'checked_populations', 'preservation')}, indent=1))


if __name__ == '__main__': main()
