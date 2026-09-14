#!/usr/bin/env python3
"""Independent closeout checks for d3a22f7, without rerunning native episodes."""
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


def module(name, file):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(file))
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value); return value


audit = module('cohort_audit2_closeout_audit', 'cohort_audit.py')
controls = module('cohort_audit2_closeout_controls', 'cohort_audit_controls.py')
J = lambda p: json.loads(Path(p).read_bytes())
SHA = lambda b: hashlib.sha256(b).hexdigest()
CANON = lambda v: json.dumps(v, ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode()
RECORDS = (('audit', 'R6-009-V3-AUDIT-2.json', 'farkas_cohort_v3', 208),
           ('superseded-v2', 'R6-009-V3-AUDIT-2-SUPERSEDED-V2.json', 'farkas_cohort_v2', 208),
           ('superseded-v1', 'R6-009-V3-AUDIT-2-SUPERSEDED-V1.json', 'farkas_cohort_v1', 169))


def chain(path, key):
    rows = []; prev = '0'*64
    for line in path.read_bytes().splitlines():
        row = json.loads(line); h = row.pop(key)
        assert row['sequence'] == len(rows) and row['previous_hash'] == prev and SHA(CANON(row)) == h
        row[key] = h; rows.append(row); prev = h
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence', type=Path, required=True)
    parser.add_argument('--before', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(); assert not args.output.exists()
    contract.verify_sources(); policy = contract.config()
    assert policy['live_enabled'] is False and not contract.campaign_ledger(True).path.exists()
    records = {}
    for fresh_name, stored_name, revision, count in RECORDS:
        fresh = args.evidence/(fresh_name+'.json'); stored = Path(__file__).with_name(stored_name)
        value = J(fresh); assert value == J(stored)
        assert value['accepted'] is True and value['revision'] == revision
        assert value['case_count'] == len(value['cases']) == count and all(value['cases'].values())
        assert set(value['cases']) == set(audit.expected_cases(audit.POPULATIONS[revision]))
        assert value['program_sha256'] == r6.sha(Path(audit.__file__))
        records[fresh_name] = {'fresh_sha256': r6.sha(fresh), 'recorded_sha256': r6.sha(stored), 'cases': count,
                               'values_identical': True, 'superseded': value['modules']['superseded']}
    fresh = args.evidence/'controls.json'; stored = Path(__file__).with_name('R6-009-V3-AUDIT-CONTROLS-2.json')
    value = J(fresh); assert value == J(stored)
    assert value['passed'] is True and value['controls'] == len(value['results']) == 44
    assert set(value['results']) == set(controls.CONTROLS) and value['expected_controls'] == list(controls.CONTROLS)
    assert len(set(value['expected_controls'])) == 44
    assert value['program_sha256'] == r6.sha(Path(controls.__file__)) and value['auditor_sha256'] == r6.sha(Path(audit.__file__))
    assert value['results']['baseline'] == {'accepted': True, 'case_count': 208}
    for name, case in controls.EXPECTED.items():
        assert value['results'][name] == {'rejected': True, 'rejected_case': case}
    records['controls'] = {'fresh_sha256': r6.sha(fresh), 'recorded_sha256': r6.sha(stored), 'controls': 44,
                            'values_identical': True, 'accepted_baselines': 1, 'rejected_mutations': 43}
    current = audit.POPULATIONS[contract.NAME]; expected = current['expected']; runs = ROOT/current['runs']
    assert set(p.name for p in runs.iterdir()) == set(expected)
    event_count = retained_count = ephemeral_count = 0; run_results = {}; checked_prices = {}
    for name, (kind, task, draw, revision) in expected.items():
        run = runs/name; events = chain(run/'events.ndjson', 'event_hash'); seal = J(run/'seal.json')
        assert seal['last_event_hash'] == events[-1]['event_hash'] and seal['event_count'] == len(events)
        for section in ('retained_sha256', 'ephemeral_sha256'):
            for file, h in seal[section].items(): assert r6.sha(run/file) == h, (name, section, file)
        event_count += len(events); retained_count += len(seal['retained_sha256']); ephemeral_count += len(seal['ephemeral_sha256'])
        present = sorted(p.name for p in (run/'stages').iterdir() if p.is_dir())
        assert present == sorted(audit.STAGES[kind])
        for stage in present:
            process = J(run/'stages'/stage/(stage+'.process.json'))
            assert process['exit_code'] == 0 and process['resource_exhausted'] is None and process['resource_violations'] == []
            assert process['monitor_error'] is None and process['observation_error'] is None and process['workload_empty_after_cleanup'] is True
        run_results[name] = {'kind': kind, 'stages': present, 'events': len(events), 'retained': len(seal['retained_sha256']), 'ephemeral': len(seal['ephemeral_sha256'])}
        if kind != 'refused':
            permit = J(run/'campaign-permit.json'); p = J(run/'transport-policy.json'); limits = p['limits']; rates = p['pricing']['nano_usd_per_token']
            priced = (limits['input_tokens_reserved']*max(rates['input'], rates['cache_write'])+limits['output_tokens']*rates['output']+999)//1000
            assert priced == permit['reserved_micro_usd'] == 102400
            checked_prices[permit['reservation_id']] = priced
    assert (event_count, retained_count, ephemeral_count) == (238, 1596, 36)
    ledger = contract.campaign_ledger(False); rows = chain(ledger.path, 'row_hash'); head = J(ledger.head)
    assert head['rows'] == len(rows) == 12 and head['last_hash'] == rows[-1]['row_hash']
    reservations = {r['reservation_id']: r for r in rows if r['kind'] == 'reservation'}
    terminal = {r['reservation_id']: r for r in rows if r['kind'] in ('send_grant','release','unknown')}
    assert set(reservations) == set(terminal) == set(checked_prices)
    consumed = [rid for rid, row in terminal.items() if row['kind'] != 'release']
    committed = sum(checked_prices[rid] for rid in consumed)
    assert len(consumed) == 4 and committed == 409600
    before = J(args.before); changed = []; missing = []
    for name, value in before.items():
        p = REPO/name
        if not p.is_file(): missing.append(name)
        elif p.stat().st_size != value['bytes'] or r6.sha(p) != value['sha256']: changed.append(name)
    assert not changed and not missing
    result = {'complete': True, 'reviewed_commit': 'd3a22f7', 'records': records, 'runs': run_results,
              'source_lock_sha256': r6.sha(contract.LOCK), 'source_lock_verified': True, 'live_enabled': False,
              'event_hashes': event_count, 'retained_entries': retained_count, 'ephemeral_entries': ephemeral_count,
              'ledger': {'rows': len(rows), 'consumed_slots': len(consumed), 'committed_micro_usd': committed, 'open_reservations': []},
              'preservation': {'checked_files': len(before), 'changed': changed, 'missing': missing, 'inventory_sha256': r6.sha(args.before),
                  'inventory_path': str(args.before), 'scope': 'review-start r6 files, excluding .cache and __pycache__'},
              'native_episodes_rerun': 0, 'focused_native_controls_rerun': False, 'real_credentials_read': 0, 'live_model_calls': 0,
              'scope': 'historical audit and copied-artifact controls plus independent hashes/counts; no build or kernel replay',
              'program_sha256': r6.sha(Path(__file__))}
    r6.write_json(args.output, result)
    print(json.dumps({k:result[k] for k in ('complete','source_lock_sha256','event_hashes','retained_entries','ephemeral_entries','ledger','preservation')},indent=2))


if __name__ == '__main__': main()
