#!/usr/bin/env python3
"""R6-008 v2 review probes. Temporary ledgers/copies; no provider or real key.

The setup, preparation and sender doubles below are the frozen focused suite's
construction. execute/invoke/reconcile/finalize are production code. These are
fault-injection observations, not additional native episodes or Lean replays.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import time
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT))
import campaign_budget as budget
import campaign_contract as contract
import campaign_episode as driver
import campaign_ledger as ledger
import credential
import episode
import events
import publication
import run as r6
import test_campaign as frozen_tests


def module(name):
    spec = importlib.util.spec_from_file_location('review_v2_'+name, HERE/(name+'.py'))
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value)
    return value


controls = module('campaign_audit_controls')
operator = module('operator_disclosure_scan')
J = r6.read_json
W = r6.write_json
TASK = r6.get_task('verinf-d1-70')


def production(name, http_bytes=b'{', process_value=None, committed=True, preparation_failure=False):
    with tempfile.TemporaryDirectory(prefix='r6-008-v2-record-probe-') as temp:
        d = Path(temp); run = d/'run'; run.mkdir()
        book = ledger.Ledger(d/'ledgers/rehearsal', contract.policy_sha256())
        book.activate(contract.REHEARSAL_AUTHORIZATION, 'rehearsal')
        expected = r6.frozen_task(TASK)[1]
        tools = {'expected': expected, 'runtime': {'stdlib': '/probe', 'extension_binaries': []},
                 'runtime_path': d, 'python': Path(sys.executable)}
        def prepare(run, task, tools):
            request = budget.request(task, J(frozen_tests.PREPARED))
            (run/'live-request.json').write_bytes(request)
            W(run/'live-arguments.json', budget.arguments(request)); return request
        def stopped(run, name, binary, argv, mounts, grant, **kwargs):
            out = run/'stages/proposal-1/output'; out.mkdir(parents=True)
            permit = J(run/'campaign-permit.json')
            if committed:
                ledger.commit_grant(grant, ledger.grant_record(permit, time.monotonic_ns()))
            W(out.parent/'proposal-1.process.json',
              {**frozen_tests.TERMINATED, 'exit_code': 137} if process_value is None else process_value)
            (out/'http.json').write_bytes(http_bytes)
            raise episode.StageFailure('proposal-1', 'resource_exhaustion', 'synthetic interruption')
        real_copy = shutil.copytree
        def copy(source, destination, *args, **kwargs):
            if preparation_failure and Path(destination) == run/'transport-pricing-sources':
                raise PermissionError('synthetic failure copying transport sources after reservation')
            return real_copy(source, destination, *args, **kwargs)
        with patch.object(contract, 'campaign_ledger', lambda live: book), \
             patch.object(driver, 'setup', lambda *args: tools), \
             patch.object(driver, 'prepare', prepare), patch.object(driver.network, 'stage', stopped), \
             patch.object(shutil, 'copytree', copy):
            result = driver.execute(run, TASK, 'rehearsal', d, None)
        raw, state = book.snapshot(); rows = ledger.parse(raw)
        permit = J(run/'campaign-permit.json')
        assert permit == next(row for row in rows if row['kind'] == 'reservation')
        sealed = J(run/'seal.json')
        assert all(r6.sha(run/p) == digest for p, digest in sealed['retained_sha256'].items())
        rec = J(run/'campaign-reconciliation.json') if (run/'campaign-reconciliation.json').exists() else None
        return {'result': result, 'reservation_exists': True,
                'authoritative_grant_exists': (book.slot(permit['reservation_id'])/ledger.GRANT_FILE).is_file(),
                'actual_open_reservations': len(state['open_reservations']),
                'actual_consumed': state['transmissions_consumed'],
                'reconciliation': None if rec is None else {k: rec.get(k) for k in ('kind', 'send_outcome', 'termination_established')},
                'terminal_event': events.read(run/'events.ndjson')[-1]['event'],
                'sealed': True, 'process_termination_predicate': ledger.termination_established(
                    J(run/'stages/proposal-1/proposal-1.process.json')
                    if (run/'stages/proposal-1/proposal-1.process.json').exists() else None)}


def fresh_copy(name, change):
    with tempfile.TemporaryDirectory(prefix='r6-008-v2-audit-probe-') as temp:
        d = Path(temp); root, books = d/'runs', d/'ledgers'
        shutil.copytree(ROOT/'campaign-runs-v2', root); shutil.copytree(ROOT/'ledgers', books)
        baseline = controls.run_audit(root, books)
        assert baseline == {'accepted': True, 'case_count': 63}, baseline
        details = change(root, books)
        observed = controls.run_audit(root, books)
        return {'unmutated_copy': baseline, 'mutated_copy': observed, 'mutation': details}


def authority_slot(root, books):
    run = root/'rehearsal-3'; permit = J(run/'campaign-permit.json')
    book = ledger.Ledger(books/'rehearsal', permit['policy_sha256'])
    p = book.slot(permit['reservation_id'])/ledger.GRANT_FILE
    assert p.read_bytes() == (run/'stages/proposal-1/grant/send-grant.json').read_bytes()
    W(p, {'wrong_reservation': True})
    try:
        ledger.read_grant(p.parent, permit)
    except ledger.Failure as error:
        return {'only_authoritative_slot_changed': True, 'production_reader_rejects': error.code}
    raise AssertionError('corrupted grant unexpectedly parsed')


def mount_change(root, books, guest):
    def change(run, rows):
        p = run/'stages/proposal-1/command.json'; command = J(p); argv = command['argv']
        matches = [i for i, a in enumerate(argv) if a == guest and i >= 2 and argv[i-2] in ('--bind', '--ro-bind')]
        assert len(matches) == 1, matches
        index = matches[0]-1
        assert argv[index] != '/tmp/unrelated-review-slot'
        argv[index] = '/tmp/unrelated-review-slot'; W(p, command)
    controls.refinalize(root/'rehearsal-3', change)
    return {'guest_mount': guest, 'host_mount_changed': True, 'normal_finalizer': True}


def scan_metadata(root, books, field):
    run = root/'rehearsal-3'; path = run/'publication-scan.json'; report = J(path)
    entries = [e for e in report['inventory'] if e['path'] == 'events.ndjson']
    assert len(entries) == 1
    value = '0'*64 if field == 'sha256' else 0
    assert entries[0][field] != value
    entries[0][field] = value; W(path, report)
    nonce = J(run/'credential-canary.json')['nonce']
    W(run/'publication-final.json', publication.final_record(path, credential.derive(nonce), nonce))
    rows = events.read(run/'events.ndjson')
    rows[-1]['payload'].update(publication_scan_sha256=r6.sha(path),
                               publication_final_sha256=r6.sha(run/'publication-final.json'))
    controls.rechain(run, rows); driver.publication_driver.seal(run, True)
    return {'one_inventory_field_changed': field, 'terminal_and_seal_rebound': True}


def false_termination(root, books):
    """Coherently bind a non-terminated supervisor record to an asserted release."""
    run = root/'rehearsal-1'; path = run/'stages/proposal-1/proposal-1.process.json'
    process = J(path); assert ledger.termination_established(process)
    process['workload_empty_after_cleanup'] = False; W(path, process)
    assert not ledger.termination_established(process)
    permit = J(run/'campaign-permit.json')
    book = ledger.Ledger(books/'rehearsal', permit['policy_sha256'])
    all_rows = ledger.parse(book.path.read_bytes()); replacements = {}; previous = '0'*64
    for row in all_rows:
        old = row['row_hash']
        if row['kind'] == 'release' and row['reservation_id'] == permit['reservation_id']:
            row['evidence']['process_sha256'] = r6.sha(path)
        row['previous_hash'] = previous; row.pop('row_hash')
        row['row_hash'] = ledger.digest(row); previous = row['row_hash']; replacements[old] = row
    def new_raw(rows):
        return b''.join(events.canonical(replacements[r['row_hash']])+b'\n' for r in rows)
    book.path.write_bytes(b''.join(events.canonical(r)+b'\n' for r in all_rows))
    W(book.head, {'policy_sha256': permit['policy_sha256'], 'rows': len(all_rows), 'last_hash': all_rows[-1]['row_hash']})
    for item in root.iterdir():
        for name in ('campaign-permit.json', 'campaign-reconciliation.json'):
            p = item/name; W(p, replacements[J(p)['row_hash']])
        for name in ('transport-ledger.ndjson', 'ledger-after.ndjson'):
            p = item/name; p.write_bytes(new_raw([json.loads(line) for line in p.read_bytes().splitlines()]))
        p = item/'reservation.json'; reservation = J(p)
        reservation.update(ledger_row_hash=J(item/'campaign-permit.json')['row_hash'],
                           ledger_sha256=r6.sha(item/'transport-ledger.ndjson')); W(p, reservation)
        for base in (item/'stages/proposal-1/grant', book.slot(J(item/'campaign-permit.json')['reservation_id'])):
            for marker in ('release.json', 'unknown.json'):
                p = base/marker
                if p.exists():
                    v = J(p); v['row_hash'] = J(item/'campaign-reconciliation.json')['row_hash']; W(p, v)
        def change(current, rows):
            for row in rows:
                if row['event'] == 'request_reserved': row['payload'] = J(current/'reservation.json')
                elif row['event'] == 'reservation_reconciled':
                    row['payload'].update(row_hash=J(current/'campaign-reconciliation.json')['row_hash'],
                                          ledger_sha256=r6.sha(current/'ledger-after.ndjson'))
                elif current.name == 'rehearsal-1' and row['stage'] == 'proposal-1' and row['event'] == 'stage_finished':
                    row['payload'] = process
            for name in ('accounting.json', 'credential-summary.json'):
                p = current/name; v = J(p)
                record = v if name == 'accounting.json' else v['accounting']
                record['reservation'] = J(current/'reservation.json'); W(p, v)
        controls.refinalize(item, change)
    return {'recorded_termination_established': True, 'recomputed_termination_established': False,
            'retained_release': True, 'ledger_and_all_mirrors_rehashed': True}


def io_probes():
    with tempfile.TemporaryDirectory(prefix='r6-008-v2-io-probe-') as temp:
        d = Path(temp); p = d/'unreadable.json'; p.write_text('{}'); p.chmod(0)
        try:
            try: p.read_bytes(); raise AssertionError('precondition: file is readable')
            except PermissionError: pass
            try: value = driver.read_record(p); read_result = {'returned': value}
            except OSError as e: read_result = {'raised': type(e).__name__}
        finally: p.chmod(0o600)
        book = ledger.Ledger(d/'book', contract.policy_sha256()); book.activate(contract.REHEARSAL_AUTHORIZATION, 'rehearsal')
        permit = frozen_tests.reserve(book, 'io-probe'); slot = book.slot(permit['reservation_id'])
        grant = ledger.grant_record(permit, time.monotonic_ns())
        real_write = os.write
        with patch.object(os, 'write', lambda fd, data: real_write(fd, data[:7])):
            durable = ledger.commit_grant(slot, grant)
        raw = (slot/ledger.GRANT_FILE).read_bytes()
        assert raw == (ledger.canonical(grant)+b'\n')[:7]
        try: ledger.read_grant(slot, permit); raise AssertionError('partial grant parsed')
        except ledger.Failure as e: short_read = e.code
        row, _ = book.reconcile(permit, frozen_tests.TERMINATED, None, {})
        permit2 = frozen_tests.reserve(book, 'io-probe-2'); slot2 = book.slot(permit2['reservation_id'])
        ledger.commit_grant(slot2, ledger.grant_record(permit2, time.monotonic_ns()))
        final2 = slot2/ledger.GRANT_FILE; final2.chmod(0)
        try:
            try: book.reconcile(permit2, frozen_tests.TERMINATED, None, {}); unreadable_grant = 'returned'
            except OSError as e: unreadable_grant = type(e).__name__
        finally: final2.chmod(0o600)
        return {'unreadable_record_precondition': True, 'read_record': read_result,
                'unreadable_grant_reconciliation': unreadable_grant,
                'short_write': {'bytes_durable': len(raw), 'expected_bytes': len(ledger.canonical(grant)+b'\n'),
                                'commit_reported_durable': isinstance(durable, int), 'reader_rejects': short_read,
                                'reconciled_conservatively_as': row['kind']}}


def multi_root():
    with tempfile.TemporaryDirectory(prefix='r6-008-v2-roots-probe-') as temp:
        d = Path(temp); token = credential.derive(credential.nonce()); header = credential.header(token)
        roots = [d/'first', d/'second']
        for run in roots:
            out = run/'stages/proposal-1/output'; out.mkdir(parents=True)
            nonce = credential.nonce()
            W(out/'http.json', {'commitment_nonce': nonce, 'credential_commitment_sha256':
                hashlib.sha256((operator.COMMITMENT_DOMAIN+':'+nonce+':'+header).encode()).hexdigest()})
            events.append(run, 'episode', 'episode_started', {}, task_id=TASK.id)
            events.append(run, 'episode', 'episode_rejected', {}, task_id=TASK.id)
            driver.publication_driver.seal(run, False)
        individual = []
        for root in roots:
            report = publication.scan([root], token, 'synthetic')
            receipt = operator.bind_runs([root], header, report, [root], publication, publication.patterns(token))[0]
            assert receipt['covered_by_scan'] and receipt['sealed_and_intact'] and receipt['commitment_bound']
            individual.append(True)
        report = publication.scan(roots, token, 'synthetic')
        receipts = operator.bind_runs(roots, header, report, roots, publication, publication.patterns(token))
        return {'each_root_alone_accepted': individual, 'combined_scan_accepted': report['accepted'],
                'combined_coverage': [r['covered_by_scan'] for r in receipts],
                'combined_sealed': [r['sealed_and_intact'] for r in receipts],
                'combined_commitment_bound': [r['commitment_bound'] for r in receipts]}


def main():
    parser = argparse.ArgumentParser(); parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing overwrite')
    contract.verify_sources(); assert contract.config()['live_enabled'] is False
    result = {'policy_sha256': contract.policy_sha256(), 'source_lock_sha256': r6.sha(contract.LOCK),
              'program_sha256': r6.sha(Path(__file__)), 'live_model_calls': 0, 'real_credentials_read': 0,
              'new_native_episodes': 0, 'cases': {}}
    jobs = {
        'truncated_http_after_grant': lambda: production('truncated'),
        'http_nonempty_list_after_grant': lambda: production('http_list', http_bytes=b'[1]'),
        'process_list_after_grant': lambda: production('process_list', process_value=[]),
        'copy_failure_after_reservation': lambda: production('copy_failure', preparation_failure=True),
        'io_partial_write_and_unreadable': io_probes,
        'authoritative_grant_altered': lambda: fresh_copy('slot', authority_slot),
        'ledger_mount_altered': lambda: fresh_copy('ledger_mount', lambda r, b: mount_change(r, b, '/ledger.ndjson')),
        'grant_mount_altered': lambda: fresh_copy('grant_mount', lambda r, b: mount_change(r, b, '/grant')),
        'scan_event_hash_forged': lambda: fresh_copy('event_hash', lambda r, b: scan_metadata(r, b, 'sha256')),
        'scan_event_length_forged': lambda: fresh_copy('event_bytes', lambda r, b: scan_metadata(r, b, 'bytes')),
        'release_despite_live_workload': lambda: fresh_copy('termination', false_termination),
        'operator_multi_root_collision': multi_root,
    }
    for name, fn in jobs.items():
        result['cases'][name] = fn()
        W(args.output, result)
        print(name, json.dumps(result['cases'][name], sort_keys=True), flush=True)
    assert set(result['cases']) == set(jobs)
    cases = result['cases']
    for name in ('http_nonempty_list_after_grant', 'process_list_after_grant', 'copy_failure_after_reservation'):
        observed = cases[name]
        assert observed['reservation_exists'] and observed['actual_open_reservations'] == 1
        assert observed['reconciliation'] is None and observed['result']['ledger_reconciled'] is True
        assert observed['result']['accounting']['attempts_reserved'] == 0 and observed['sealed']
    observed = cases['truncated_http_after_grant']
    assert observed['actual_open_reservations'] == 0 and observed['actual_consumed'] == 1
    assert observed['reconciliation']['send_outcome'] == 'unknown'
    assert observed['result']['accounting']['grant_committed'] is False
    assert observed['result']['accounting']['send_outcome'] == 'not_started'
    for name in ('authoritative_grant_altered', 'ledger_mount_altered', 'grant_mount_altered',
                 'scan_event_hash_forged', 'scan_event_length_forged', 'release_despite_live_workload'):
        assert cases[name]['mutated_copy'] == {'accepted': True, 'case_count': 63}
    assert cases['operator_multi_root_collision']['combined_coverage'] == [False, True]
    assert cases['io_partial_write_and_unreadable']['read_record'] == {'raised': 'PermissionError'}
    assert cases['io_partial_write_and_unreadable']['unreadable_grant_reconciliation'] == 'PermissionError'
    assert cases['io_partial_write_and_unreadable']['short_write']['commit_reported_durable'] is True
    result['case_count'] = len(jobs); result['completed'] = True; W(args.output, result)


if __name__ == '__main__': main()
