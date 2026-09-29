#!/usr/bin/env python3
"""Recount R6-009 from actual body, ledger, event and seal bytes; no execution."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
REPO = ROOT.parents[1]
sys.path.insert(0, str(ROOT))
import cohort_contract as contract
import cohort_ledger as ledger
import run as r6
import test_cohort

EXPECTED = ('r1-d1-draw1', 'r1-d1-draw2-format', 'r2-d1-draw1-refused', 'r2-d1-draw2', 'r2-d1-draw3')
BODY_NAMES = ('serialized-body.json', 'outbound-body.json', 'received-body.json')
J = lambda p: json.loads(Path(p).read_bytes())
SHA = lambda b: hashlib.sha256(b).hexdigest()
CANON = lambda v: json.dumps(v, ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--before', type=Path, required=True)
    p.add_argument('--evidence', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args(); assert not args.output.exists()
    contract.verify_sources()
    c = contract.config(); assert c['live_enabled'] is False
    assert not contract.campaign_ledger(True).path.exists()
    assert sorted(x.name for x in (ROOT/'cohort-runs').iterdir() if x.is_dir()) == sorted(EXPECTED)
    runs = {}; totals = {'event_hashes': 0, 'sealed_entries': 0}
    reservations, grants, nonces = [], [], []
    raw_body_digests = {n: [] for n in BODY_NAMES}
    for name in EXPECTED:
        run = ROOT/'cohort-runs'/name; seal = J(run/'seal.json')
        previous = '0'*64; event_rows = []
        for line in (run/'events.ndjson').read_bytes().splitlines():
            row = json.loads(line); h = row.pop('event_hash')
            assert row['previous_hash'] == previous and row['sequence'] == len(event_rows) and SHA(CANON(row)) == h
            previous = h; event_rows.append(row)
        assert seal['event_count'] == len(event_rows) and seal['last_event_hash'] == previous
        for path, h in seal['retained_sha256'].items(): assert r6.sha(run/path) == h, (name, path)
        out = run/'stages/proposal-1/output'
        body_record = {}
        for body_name in BODY_NAMES:
            path = out/body_name
            if path.exists():
                b = path.read_bytes(); h = SHA(b); raw_body_digests[body_name].append(h)
                body_record[body_name] = {'bytes': len(b), 'sha256': h}
            else: body_record[body_name] = None
        http = J(out/'http.json') if (out/'http.json').exists() else None
        if http:
            reservations.append(http['reservation_id']); nonces.append(http['commitment_nonce'])
            if http['grant_id']: grants.append(http['grant_id'])
        verdict = J(run/'verdict.json') if (run/'verdict.json').exists() else None
        if verdict: assert all(v == {'added': [], 'removed': []} for v in verdict['axiom_delta'].values())
        runs[name] = {'events': len(event_rows), 'sealed_entries': len(seal['retained_sha256']),
                      'bodies': body_record, 'body_sends_started': http['body_sends_started'] if http else None,
                      'proof_export_sha256': verdict['solution_sha256'] if verdict else None,
                      'declarations': {k: v['checked_declarations'] for k, v in verdict['final_validation'].items()} if verdict else None,
                      'axiom_delta': verdict['axiom_delta'] if verdict else None}
        totals['event_hashes'] += len(event_rows); totals['sealed_entries'] += len(seal['retained_sha256'])
    assert len(reservations) == len(set(reservations)) == 4 and len(grants) == len(set(grants)) == 3 and len(nonces) == len(set(nonces)) == 4
    assert len(raw_body_digests['serialized-body.json']) == 4 and all(len(raw_body_digests[n]) == 3 for n in BODY_NAMES[1:])
    assert len({v for group in raw_body_digests.values() for v in group}) == 1
    book = contract.campaign_ledger(False); raw = book.path.read_bytes(); rows = []
    previous = '0'*64
    for line in raw.splitlines():
        row = json.loads(line); h = row.pop('row_hash')
        assert row['sequence'] == len(rows) and row['previous_hash'] == previous and SHA(CANON(row)) == h
        row['row_hash'] = h; rows.append(row); previous = h
    terminal = {r['reservation_id']: r for r in rows if r['kind'] in ('send_grant', 'release', 'unknown')}
    reserved = {r['reservation_id']: r for r in rows if r['kind'] == 'reservation'}
    committed = sum(r['reserved_micro_usd'] for rid, r in reserved.items() if terminal.get(rid, {}).get('kind') != 'release')
    consumed = {(reserved[rid]['task_id'], reserved[rid]['draw']) for rid, r in terminal.items() if r['kind'] in ('send_grant', 'unknown')}
    assert committed == 307200 and len(consumed) == 3 and set(reserved) == set(terminal)
    focused = J(args.evidence/'R6-009-REVIEW-FOCUSED.json')
    fnames = [v['name'] for v in focused['checks']]
    assert focused['passed'] is True and all(v['passed'] is True for v in focused['checks'])
    assert len(fnames) == len(set(fnames)) == focused['check_count'] == 23 and set(fnames) == set(test_cohort.CASES)
    baseline = J(args.before); changed, missing = [], []
    for name, original in baseline.items():
        path = REPO/name
        if not path.is_file(): missing.append(name)
        elif path.stat().st_size != original['bytes'] or r6.sha(path) != original['sha256']: changed.append(name)
    assert not changed and not missing, (changed, missing)
    result = {'complete': True, 'reviewed_commit': '34eae76', 'program_sha256': r6.sha(Path(__file__)),
              'scope': 'byte recount and retained-report consistency; no Lean rerun or remote attestation',
              'live_model_calls': 0, 'real_credentials_read': 0, 'live_enabled': False, 'live_ledger_absent': True,
              'source_lock_verified': True, 'runs': runs, 'totals': totals,
              'distinct_receipts': {'reservations': len(set(reservations)), 'grants': len(set(grants)), 'nonces': len(set(nonces))},
              'ledger': {'rows': len(rows), 'sequence': [r['kind'] for r in rows], 'sha256': SHA(raw),
                         'committed_micro_usd': committed, 'consumed_slots': [list(v) for v in sorted(consumed)], 'open_reservations': []},
              'preservation': {'inventory_sha256': r6.sha(args.before), 'inventory_path': str(args.before), 'checked_files': len(baseline),
                               'missing': missing, 'changed': changed, 'scope': 'review-start r6 files, excluding .cache and __pycache__'},
              'evidence_files': {p.name: {'sha256': r6.sha(p), 'bytes': p.stat().st_size}
                                 for p in sorted(args.evidence.glob('R6-009-REVIEW-*.json'))}}
    r6.write_json(args.output, result)
    print(json.dumps({k: result[k] for k in ('totals', 'distinct_receipts', 'ledger', 'preservation')}, indent=1))


if __name__ == '__main__': main()
