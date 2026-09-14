#!/usr/bin/env python3
"""Review probes for the disabled R6-008 v4; temporary state and synthetic credentials only.

Production probes replace setup, preparation and the launcher, as in the frozen
fault sweep. They are not native episodes, TLS measurements or Lean replays.
Mutation probes regenerate ledger mirrors and use the production finalizer.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
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
import run as r6
import test_campaign as tests


def module(name):
    spec = importlib.util.spec_from_file_location('v4_review_'+name, HERE/(name+'.py'))
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value); return value


controls = module('campaign_audit_controls')
operator_controls = module('operator_scan_controls')
TASK = r6.get_task('verinf-d1-70')
J, W = r6.read_json, r6.write_json
CASES = ('interrupted_control', 'recovery_control', 'reservation_uncertain_event_failure',
         'reservation_recovered_event_failure', 'reservation_reconciled_event_failure',
         'attempt_identity_removed', 'summary_evidence_contradiction',
         'marker_recovery_control', 'partial_release_marker_recovery',
         'operator_readable_control', 'operator_unreadable_bound_file', 'finalize_incomplete_evidence')


def production(kind):
    with tempfile.TemporaryDirectory(prefix='r6-v4-lifecycle-probe-') as temp:
        d = Path(temp); run = d/'episode'; run.mkdir()
        book = ledger.Ledger(d/'ledgers/rehearsal', contract.policy_sha256())
        book.activate(contract.REHEARSAL_AUTHORIZATION, 'rehearsal')
        tools = {'expected': r6.frozen_task(TASK)[1], 'runtime': {'stdlib': '/probe', 'extension_binaries': []},
                 'runtime_path': d, 'python': Path(sys.executable)}
        calls = {'launched': 0, 'head_fault': 0, 'event_fault': 0, 'find_open': 0, 'reconcile': 0}
        real_head, real_append, real_find, real_reconcile = book._write_head, events.append, book.find_open, book.reconcile
        def prepare(run, task, tools):
            request = budget.request(task, J(tests.PREPARED))
            (run/'live-request.json').write_bytes(request); W(run/'live-arguments.json', budget.arguments(request)); return request
        def stage(run, name, binary, argv, mounts, grant, **kwargs):
            calls['launched'] += 1
            out = run/'stages/proposal-1/output'; out.mkdir(parents=True)
            W(out.parent/'command.json', {'synthetic': True})
            permit = J(run/'campaign-permit.json')
            ledger.commit_grant(grant, ledger.grant_record(permit, time.monotonic_ns()))
            W(out.parent/'proposal-1.process.json', {**tests.TERMINATED, 'exit_code': 137})
            (out/'http.json').write_bytes(b'{')
            raise episode.StageFailure('proposal-1', 'resource_exhaustion', 'synthetic interruption')
        def head(rows, last_hash):
            if kind in ('recovery_control', 'reservation_uncertain_event_failure', 'reservation_recovered_event_failure') and rows == 2:
                calls['head_fault'] += 1; raise OSError(5, 'synthetic head failure after reservation append')
            return real_head(rows, last_hash)
        def append(run, phase, event, payload, *a, **kw):
            if kind == event+'_event_failure' and not calls['event_fault']:
                calls['event_fault'] += 1; raise OSError(5, 'synthetic recovery receipt failure')
            return real_append(run, phase, event, payload, *a, **kw)
        def find_open(*a, **kw):
            calls['find_open'] += 1; return real_find(*a, **kw)
        def reconcile(*a, **kw):
            calls['reconcile'] += 1; return real_reconcile(*a, **kw)
        result, raised = None, None
        with patch.object(contract, 'campaign_ledger', lambda live: book), patch.object(driver, 'setup', lambda *a: tools), \
             patch.object(driver, 'prepare', prepare), patch.object(driver.network, 'stage', stage), \
             patch.object(book, '_write_head', head), patch.object(book, 'find_open', find_open), \
             patch.object(book, 'reconcile', reconcile), patch.object(events, 'append', append):
            try: result = driver.execute(run, TASK, 'rehearsal', d, None)
            except Exception as error: raised = {'type': type(error).__name__, 'message': str(error)}
        raw, state = book.snapshot(); ledger_rows = ledger.parse(raw)
        terminal = next((r for r in ledger_rows if r['kind'] in ledger.TERMINAL), None)
        event_rows = events.read(run/'events.ndjson'); summary = J(run/'credential-summary.json')
        seal = J(run/'seal.json') if (run/'seal.json').exists() else None
        if seal:
            assert seal['last_event_hash'] == event_rows[-1]['event_hash']
            assert all(r6.sha(run/p) == digest for p, digest in seal['retained_sha256'].items())
        assert state['reservations'] == 1 and raised is None
        if kind in ('reservation_uncertain_event_failure', 'reservation_recovered_event_failure'):
            assert calls['head_fault'] == calls['event_fault'] == 1 and calls['reconcile'] == 0
            assert len(state['open_reservations']) == 1 and summary['accounting']['attempts_reserved'] == 0
            assert summary['ledger_reconciled'] is True and summary['evidence_complete'] is True
        elif kind == 'reservation_reconciled_event_failure':
            assert calls['event_fault'] == 1 and not state['open_reservations'] and state['transmissions_consumed'] == 1
            assert summary['ledger_reconciled'] is True and summary['evidence_complete'] is True
            assert 'Reservation left open' in summary['error']
        elif kind == 'recovery_control':
            assert not state['open_reservations'] and terminal['kind'] == 'release' and calls['launched'] == 0
        else:
            assert not state['open_reservations'] and terminal['kind'] == 'send_grant'
        return {'calls': calls, 'raised': raised, 'sealed': seal is not None, 'terminal_event': event_rows[-1]['event'],
                'events': [r['event'] for r in event_rows], 'actual_reservations': state['reservations'],
                'actual_open': len(state['open_reservations']), 'actual_consumed': state['transmissions_consumed'],
                'actual_terminal_kind': None if terminal is None else terminal['kind'],
                'summary_error': summary['error'], 'accounting': summary['accounting'],
                'summary': {k: summary[k] for k in ('ledger_reconciled', 'reservation_state', 'evidence_complete', 'failure_category')},
                'fault_scope': 'head-write failure followed by one recovery-event write failure' if calls['head_fault'] and calls['event_fault'] else 'single fault or interruption control'}


def rewrite_attempt(root, books):
    """Remove the v4 attempt field and event, with all ledger mirrors coherently rebound."""
    run = root/'rehearsal-3'; permit = J(run/'campaign-permit.json')
    assert isinstance(permit['attempt_id'], str) and permit['attempt_id']
    book = ledger.Ledger(books/'rehearsal', permit['policy_sha256'])
    all_rows = ledger.parse(book.path.read_bytes()); replacements = {}; previous = '0'*64
    for row in all_rows:
        old = row.pop('row_hash')
        if row['kind'] == 'reservation' and row['reservation_id'] == permit['reservation_id']: del row['attempt_id']
        row['previous_hash'] = previous; row['row_hash'] = ledger.digest(row); previous = row['row_hash']; replacements[old] = row
    book.path.write_bytes(b''.join(events.canonical(row)+b'\n' for row in all_rows))
    W(book.head, {'policy_sha256': permit['policy_sha256'], 'rows': len(all_rows), 'last_hash': all_rows[-1]['row_hash']})
    for item in root.iterdir():
        for name in ('campaign-permit.json', 'campaign-reconciliation.json'):
            p = item/name; W(p, replacements[J(p)['row_hash']])
        for name in ('transport-ledger.ndjson', 'ledger-after.ndjson'):
            p = item/name; rows = ledger.parse(p.read_bytes())
            p.write_bytes(b''.join(events.canonical(replacements[r['row_hash']])+b'\n' for r in rows))
        p = item/'reservation.json'; reservation = J(p)
        reservation.update(ledger_row_hash=J(item/'campaign-permit.json')['row_hash'], ledger_sha256=r6.sha(item/'transport-ledger.ndjson')); W(p, reservation)
        def change(current, rows):
            if current.name == 'rehearsal-3':
                assert sum(r['event'] == 'reservation_attempted' for r in rows) == 1
                rows[:] = [r for r in rows if r['event'] != 'reservation_attempted']
            for row in rows:
                if row['event'] == 'reservation_reconciled':
                    row['payload'].update(reconciliation_row_hash=J(current/'campaign-reconciliation.json')['row_hash'], ledger_sha256=r6.sha(current/'ledger-after.ndjson'))
                elif row['event'] == 'request_reserved': row['payload'] = J(current/'reservation.json')
            for name in ('accounting.json', 'credential-summary.json'):
                p = current/name; value = J(p); record = value if name == 'accounting.json' else value['accounting']
                record['reservation'] = J(current/'reservation.json'); W(p, value)
        controls.refinalize(item, change)


def audit_mutation(kind):
    with tempfile.TemporaryDirectory(prefix='r6-v4-audit-probe-') as temp:
        d = Path(temp); root, books = d/'runs', d/'ledgers'
        shutil.copytree(ROOT/'campaign-runs-v4', root); shutil.copytree(ROOT/'ledgers', books)
        baseline = controls.run_audit(root, books); assert baseline == {'accepted': True, 'case_count': 73}
        if kind == 'attempt_identity_removed': rewrite_attempt(root, books)
        else:
            def change(run, rows):
                p = run/'credential-summary.json'; value = J(p)
                assert value['evidence_complete'] is value['accounting']['evidence_complete'] is True
                value['evidence_complete'] = False; W(p, value)
            controls.refinalize(root/'rehearsal-3', change)
        observed = controls.run_audit(root, books)
        return {'unmutated_copy': baseline, 'mutated_copy': observed,
                'ledger_and_mirrors_rebound': kind == 'attempt_identity_removed', 'normal_finalizer': True}


def marker_recovery(partial):
    with tempfile.TemporaryDirectory(prefix='r6-v4-marker-probe-') as temp:
        book = ledger.Ledger(Path(temp), contract.policy_sha256()); book.activate(contract.REHEARSAL_AUTHORIZATION, 'rehearsal')
        permit = tests.reserve(book, 'marker-probe'); real_append, real_write = book._append, os.write; calls = []
        def append(rows, row):
            if row['kind'] in ledger.TERMINAL: raise OSError(5, 'synthetic terminal-append failure')
            return real_append(rows, row)
        def short_marker(fd, data):
            if calls: raise OSError(5, 'synthetic failure during marker write')
            calls.append(1); return real_write(fd, bytes(data[:7]))
        with (patch.object(os, 'write', short_marker) if partial else patch.object(book, '_append', append)):
            try: book.reconcile(permit, tests.TERMINATED, None, {'probe': 'first'}, launched=True); raise AssertionError('fault not injected')
            except OSError: pass
        marker = book.slot(permit['reservation_id'])/'release.json'; raw = marker.read_bytes()
        try: json.loads(raw); valid = True
        except ValueError: valid = False
        assert valid is (not partial) and book.snapshot()[1]['open_reservations'] == [permit['reservation_id']]
        row, _ = book.reconcile(permit, tests.TERMINATED, None, {'probe': 'retry'}, launched=True)
        assert row['kind'] == 'release' and row['reason'] == 'completed_from_marker' and marker.read_bytes() == raw
        assert not book.snapshot()[1]['open_reservations']
        return {'marker_complete_json': valid, 'marker_bytes': len(raw), 'recovered_kind': row['kind'],
                'recovery_reason': row['reason'], 'marker_still_original_bytes': True,
                'marker_digest_bound': row['marker_sha256'] == hashlib.sha256(raw).hexdigest(), 'actual_open_after': 0}


def operator_unreadable(unreadable):
    with tempfile.TemporaryDirectory(prefix='r6-v4-scanner-probe-') as temp:
        d = Path(temp); canary = credential.derive(credential.nonce()); header = credential.header(canary)
        root = d/canary; run = root/'episode'; operator_controls.sealed_run(run, header)
        cred = d/'synthetic-credential'; cred.write_text(header+'\n'); cred.chmod(0o600)
        target = run/'stages/proposal-1/output/http.json'
        if unreadable:
            target.chmod(0)
            try: target.read_bytes(); raise AssertionError('unreadability precondition failed')
            except PermissionError: pass
        try:
            p = subprocess.run([sys.executable, '-B', str(HERE/'operator_disclosure_scan.py'), '--credential-file', str(cred),
                                '--report', str(d/'report.json'), '--bind-runs', str(run), '--root', str(root)], capture_output=True, timeout=60)
        finally: target.chmod(0o600)
        report_path = d/'report.json'; report_bytes = report_path.read_bytes() if report_path.exists() else b''
        result = {'unreadability_established': unreadable, 'exit_code': p.returncode, 'report_exists': report_path.exists(),
                  'stdout_token_occurrences': p.stdout.count(canary.encode()), 'stderr_token_occurrences': p.stderr.count(canary.encode()),
                  'report_token_occurrences': report_bytes.count(canary.encode()),
                  'stderr_mentions_permission_error': b'PermissionError' in p.stderr,
                  'stderr_sha256': hashlib.sha256(p.stderr).hexdigest(), 'synthetic_only': True}
        assert p.returncode == (1 if unreadable else 0)
        assert (result['stderr_token_occurrences'] > 0) is unreadable
        assert result['stdout_token_occurrences'] == result['report_token_occurrences'] == 0
        return result


def incomplete_finalization():
    with tempfile.TemporaryDirectory(prefix='r6-v4-finalize-probe-') as temp:
        run = Path(temp); nonce = credential.nonce()
        events.append(run, 'episode', 'episode_started', {}, task_id=TASK.id)
        summary = {'proof_accepted': True, 'credential_use_accepted': True, 'ledger_reconciled': True,
                   'evidence_complete': False, 'failure_category': None}
        W(run/'credential-summary.json', summary)
        accepted, _, _ = driver.finalize(run, credential.derive(nonce), nonce, summary, False)
        assert accepted is True and events.read(run/'events.ndjson')[-1]['event'] == 'episode_finished'
        return {'scope': 'finalization predicate only; positive proof flags supplied, no proof or full-audit claim',
                'input_evidence_complete': False, 'seal_accepted': J(run/'seal.json')['accepted'], 'terminal_event': 'episode_finished'}


def main():
    parser = argparse.ArgumentParser(); parser.add_argument('--output', type=Path, required=True); args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing overwrite')
    contract.verify_sources(); assert contract.NAME == 'responses_campaign_v4' and contract.config()['live_enabled'] is False
    result = {'completed': False, 'policy_sha256': contract.policy_sha256(), 'source_lock_sha256': r6.sha(contract.LOCK),
              'program_sha256': r6.sha(Path(__file__)), 'real_credentials_read': 0, 'provider_calls': 0, 'new_native_episodes': 0,
              'expected_cases': CASES, 'cases': {}}
    for name in CASES:
        if name in CASES[:5]: observed = production(name)
        elif name in CASES[5:7]: observed = audit_mutation(name)
        elif name in CASES[7:9]: observed = marker_recovery(name == 'partial_release_marker_recovery')
        elif name in CASES[9:11]: observed = operator_unreadable(name == 'operator_unreadable_bound_file')
        else: observed = incomplete_finalization()
        result['cases'][name] = observed; W(args.output, result)
        print(name, json.dumps(observed, sort_keys=True), flush=True)
    assert tuple(result['cases']) == CASES and len(set(CASES)) == len(CASES)
    result['completed'] = True; result['case_count'] = len(CASES); W(args.output, result)


if __name__ == '__main__': main()
