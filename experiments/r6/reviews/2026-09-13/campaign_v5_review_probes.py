#!/usr/bin/env python3
"""Supplementary v5 review probes: copies, ledger faults and synthetic scanner inputs.

No policy signing, provider requests, real credentials, native episodes or Lean
replay. Successful mutation audits are observations of review gaps, not desired
acceptance criteria for a repaired auditor.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT))
import campaign_contract as contract
import campaign_episode as driver
import campaign_ledger as ledger
import credential
import events
import run as r6
import test_campaign as tests


def module(name):
    spec = importlib.util.spec_from_file_location('v5_review_'+name, HERE/(name+'.py'))
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value); return value


controls = module('campaign_audit_controls')
operator_controls = module('operator_scan_controls')
J, W = r6.read_json, r6.write_json
CASES = ('summary_top_level_control', 'summary_nested_evidence', 'summary_nested_allowance', 'summary_task_identity',
         'reconciliation_head_failure_control', 'reconciliation_recovery_snapshot_failure',
         'marker_release_repair_control', 'marker_release_repair_interrupted', 'marker_unknown_torn',
         'operator_malformed_nonce', 'operator_report_write_failure')


def summary_mutation(name):
    with tempfile.TemporaryDirectory(prefix='r6-v5-summary-probe-') as temp:
        d = Path(temp); root, books = d/'runs', d/'ledgers'
        shutil.copytree(ROOT/'campaign-runs-v5', root); shutil.copytree(ROOT/'ledgers', books)
        baseline = controls.run_audit(root, books); assert baseline == {'accepted': True, 'case_count': 73}
        def change(run, rows):
            path = run/'credential-summary.json'; value = J(path); acct = J(run/'accounting.json')
            assert value['accounting'] == acct and value['task_id'] == 'verinf-d1-70'
            if name == 'summary_top_level_control':
                assert value['evidence_complete'] is True; value['evidence_complete'] = False
            elif name == 'summary_nested_evidence':
                assert value['accounting']['evidence_complete'] is True; value['accounting']['evidence_complete'] = False
            elif name == 'summary_nested_allowance':
                assert value['accounting']['allowance_consumed'] == 1; value['accounting']['allowance_consumed'] = 0
            else: value['task_id'] = r6.C8.id
            W(path, value)
        controls.refinalize(root/'rehearsal-3', change)
        observed = controls.run_audit(root, books)
        if name == 'summary_top_level_control':
            assert observed['accepted'] is False and observed['rejected_case'] == 'rehearsal-3:chain:expected_sequence'
        else: assert observed == {'accepted': True, 'case_count': 73}
        return {'unmutated_copy': baseline, 'mutated_copy': observed, 'normal_finalizer': True,
                'source_of_change': 'credential-summary.json only; publication records, event chain and seal regenerated'}


def reconciliation_probe(name):
    with tempfile.TemporaryDirectory(prefix='r6-v5-reconciliation-probe-') as temp:
        d = Path(temp); run = d/'run'; run.mkdir()
        book = tests.temp_ledger(d/'ledger'); permit = tests.reserve(book, run.name)
        slot = book.slot(permit['reservation_id']); ledger.commit_grant(slot, ledger.grant_record(permit, 1))
        stage = run/'stages/proposal-1'; out = stage/'output'; out.mkdir(parents=True)
        W(stage/'command.json', {}); W(stage/'proposal-1.process.json', tests.TERMINATED); (out/'http.json').write_bytes(b'{')
        events.append(run, 'episode', 'episode_started', {}, task_id='verinf-d1-70')
        lifecycle = {'permit': permit, 'reservation_state': 'reserved', 'reconciliation': None, 'evidence_write_failures': []}
        real_head, real_snapshot, real_find = book._write_head, book.snapshot, book.find_terminal
        calls = {'head_failure': 0, 'terminal_row_found': 0, 'snapshot_failure': 0}
        def head(rows, last_hash):
            if rows == 3: calls['head_failure'] += 1; raise OSError(5, 'synthetic terminal head-write failure')
            return real_head(rows, last_hash)
        def snapshot():
            if name == 'reconciliation_recovery_snapshot_failure':
                calls['snapshot_failure'] += 1; raise OSError(5, 'synthetic evidence snapshot read failure')
            return real_snapshot()
        def find(reservation_id):
            row = real_find(reservation_id)
            if row is not None: calls['terminal_row_found'] += 1
            return row
        raised = None
        with patch.object(contract, 'campaign_ledger', lambda live: book), patch.object(book, '_write_head', head), \
             patch.object(book, 'snapshot', snapshot), patch.object(book, 'find_terminal', find):
            try: driver.reconcile(run, permit, False, lifecycle)
            except OSError as error: raised = type(error).__name__
        _, state = book.snapshot(); acct = driver.accounting_for(run, contract.config(), False, None, None, lifecycle)
        assert calls['head_failure'] == calls['terminal_row_found'] == 1 and not state['open_reservations'] and state['transmissions_consumed'] == 1
        if name == 'reconciliation_head_failure_control':
            assert raised is None and lifecycle['reconciliation']['kind'] == 'send_grant' and acct['ledger_reconciled'] is True
        else:
            assert raised == 'OSError' and lifecycle['reconciliation'] is None and acct['ledger_reconciled'] is False
        return {'calls': calls, 'raised': raised, 'actual_open': 0, 'actual_consumed': 1,
                'retained_lifecycle_kind': (lifecycle['reconciliation'] or {}).get('kind'),
                'ledger_reconciled': acct['ledger_reconciled'], 'allowance_consumed': acct['allowance_consumed'],
                'scope': 'production reconciliation helper and accounting; no launcher, finalization, native episode or full audit',
                'fault_scope': 'terminal head-write failure followed by snapshot-read failure' if raised else 'terminal head-write failure control'}


def marker_probe(name):
    with tempfile.TemporaryDirectory(prefix='r6-v5-marker-probe-') as temp:
        d = Path(temp); book = tests.temp_ledger(d/'ledger'); permit = tests.reserve(book, 'marker-probe')
        slot = book.slot(permit['reservation_id']); real_write = os.write; writes = []
        unknown = name == 'marker_unknown_torn'
        process = None if unknown else tests.TERMINATED
        http = None if unknown else tests.UNSENT
        def torn(fd, data):
            if writes: raise OSError(5, 'synthetic interruption during marker write')
            writes.append(1); return real_write(fd, bytes(data[:7]))
        with patch.object(os, 'write', torn):
            try: book.reconcile(permit, process, http, {}); raise AssertionError('injection did not fire')
            except OSError: pass
        initial_marker = slot/('unknown.json' if unknown else 'release.json')
        assert initial_marker.stat().st_size == 7 and book.snapshot()[1]['open_reservations'] == [permit['reservation_id']]
        if unknown:
            try: book.reconcile(permit, process, http, {}); raise AssertionError('torn unknown marker accepted')
            except ledger.Failure as error: code = error.code
            assert code == 'campaign_marker_torn_unrecoverable'
            state = book.snapshot()[1]
            try: tests.reserve(book, 'next'); raise AssertionError('open reservation did not block another')
            except ledger.Failure as error: next_code = error.code
            assert next_code == 'campaign_reservation_open'
            return {'faults': 1, 'recovery_code': code, 'open_reservations': len(state['open_reservations']),
                    'consumed': state['transmissions_consumed'], 'next_reservation_rejected': next_code,
                    'qualification': 'held open, fails closed; not automatically converted to a terminal unknown row'}
        if name == 'marker_release_repair_interrupted':
            real_append = book._append
            def failing(rows, row):
                if row['kind'] in ledger.TERMINAL: raise OSError(5, 'synthetic append failure after recovery marker')
                return real_append(rows, row)
            with patch.object(book, '_append', failing):
                try: book.reconcile(permit, process, http, {}); raise AssertionError('second fault did not fire')
                except OSError: pass
            assert sorted(p.name for p in slot.iterdir()) == ['release.json', 'unknown.json']
        row, _ = book.reconcile(permit, process, http, {})
        state = book.snapshot()[1]; assert row['kind'] == 'unknown' and state['transmissions_consumed'] == 1 and not state['open_reservations']
        run = d/'run'; target = run/'stages/proposal-1/grant'; target.parent.mkdir(parents=True)
        shutil.copytree(slot, target)
        auditor = controls.audit; a = auditor.Audit()
        try:
            auditor.slot_contents(a, run, 'probe', auditor.RULES[contract.NAME], permit, row, book)
            slot_verdict = {'accepted': True}
        except auditor.Rejection as error: slot_verdict = {'accepted': False, 'case': error.case}
        if name == 'marker_release_repair_control':
            assert row['torn_marker'] == 'release.json' and slot_verdict['accepted'] is True
        else:
            assert 'torn_marker' not in row and slot_verdict == {'accepted': False, 'case': 'probe:slot:authoritative_matches_retained'}
        return {'faults': 1 if name == 'marker_release_repair_control' else 2, 'ledger_kind': row['kind'], 'reason': row['reason'],
                'torn_marker': row.get('torn_marker'), 'files': sorted(p.name for p in slot.iterdir()),
                'open_reservations': 0, 'consumed': 1, 'slot_predicate': slot_verdict,
                'scope': 'ledger recovery and slot predicate only; not a full episode or full-audit claim'}


def scanner_probe(name):
    with tempfile.TemporaryDirectory(prefix='r6-v5-scanner-probe-') as temp:
        d = Path(temp); token = credential.derive(credential.nonce()); header = credential.header(token)
        root = d/token; run = root/'episode'; operator_controls.sealed_run(run, header)
        cred = d/'synthetic-credential'; cred.write_text(header+'\n'); cred.chmod(0o600)
        path = d/'report.json'
        if name == 'operator_malformed_nonce':
            p = run/'stages/proposal-1/output/http.json'; value = J(p); value['commitment_nonce'] = 42; W(p, value)
        else: path = root  # writing a report to this directory fails with a canary-bearing path
        proc = subprocess.run([sys.executable, '-B', str(HERE/'operator_disclosure_scan.py'), '--credential-file', str(cred),
                               '--report', str(path), '--bind-runs', str(run), '--root', str(root)], capture_output=True, timeout=60)
        value = json.loads(proc.stdout)
        assert proc.returncode == 2 and value['accepted'] is False and value['bound_runs_accepted'] is False
        assert not proc.stderr and token.encode() not in proc.stdout
        return {'exit_code': proc.returncode, 'safe_refusal': value, 'stderr_bytes': 0, 'stdout_token_occurrences': 0,
                'report_created': path.is_file(), 'synthetic_only': True}


def main():
    parser = argparse.ArgumentParser(); parser.add_argument('--output', type=Path, required=True); args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing overwrite')
    contract.verify_sources(); assert contract.NAME == 'responses_campaign_v5' and contract.config()['live_enabled'] is False
    result = {'completed': False, 'policy_sha256': contract.policy_sha256(), 'source_lock_sha256': r6.sha(contract.LOCK),
              'program_sha256': r6.sha(Path(__file__)), 'expected_cases': CASES, 'cases': {},
              'real_credentials_read': 0, 'provider_calls': 0, 'new_native_episodes': 0, 'new_lean_replays': 0}
    for name in CASES:
        if name.startswith('summary_'): observed = summary_mutation(name)
        elif name.startswith('reconciliation_'): observed = reconciliation_probe(name)
        elif name.startswith('marker_'): observed = marker_probe(name)
        else: observed = scanner_probe(name)
        result['cases'][name] = observed; W(args.output, result); print(name, json.dumps(observed, sort_keys=True), flush=True)
    assert tuple(result['cases']) == CASES and len(set(CASES)) == len(CASES)
    result['completed'] = True; result['case_count'] = len(CASES); W(args.output, result)


if __name__ == '__main__': main()
