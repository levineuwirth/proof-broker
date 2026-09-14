#!/usr/bin/env python3
"""Independent v3 fault probes, with synthetic credentials and temporary state.

The production probes use the checkpoint's setup/preparation/launcher double
construction. They execute real lifecycle, ledger and finalization code, but
are not native episodes, TLS measurements or Lean replays.
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
import publication
import run as r6
import test_campaign as tests


def module(name):
    spec = importlib.util.spec_from_file_location('v3_review_'+name, HERE/(name+'.py'))
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value); return value


controls = module('campaign_audit_controls')
audit = controls.audit
operator = module('operator_disclosure_scan')
J, W = r6.read_json, r6.write_json
TASK = r6.get_task('verinf-d1-70')


def production(kind):
    with tempfile.TemporaryDirectory(prefix='r6-v3-lifecycle-probe-') as temp:
        d = Path(temp); run = d/'episode'; run.mkdir()
        book = ledger.Ledger(d/'ledgers/rehearsal', contract.policy_sha256())
        book.activate(contract.REHEARSAL_AUTHORIZATION, 'rehearsal')
        tools = {'expected': r6.frozen_task(TASK)[1], 'runtime': {'stdlib': '/probe', 'extension_binaries': []},
                 'runtime_path': d, 'python': Path(sys.executable)}
        calls = {'launched': 0, 'injected': 0, 'reconcile_called': 0}
        real_head, real_json, real_reconcile = book._write_head, r6.write_json, book.reconcile
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
            (out/'http.json').write_bytes(b'{}' if kind == 'http_empty_object' else b'{')
            raise episode.StageFailure('proposal-1', 'resource_exhaustion', 'synthetic interruption')
        def head(rows, last_hash):
            if kind == 'reserve_head_failure' and rows == 2:
                calls['injected'] += 1
                raise OSError(5, 'synthetic head failure after reservation append')
            return real_head(rows, last_hash)
        def write_json(path, value):
            target = 'campaign-permit.json' if kind == 'reservation_receipt_failure' else 'campaign-reconciliation.json'
            if kind in ('reservation_receipt_failure', 'reconciliation_receipt_failure') and Path(path) == run/target:
                calls['injected'] += 1
                raise OSError(5, 'synthetic evidence-write failure')
            return real_json(path, value)
        def reconcile(*args, **kwargs):
            calls['reconcile_called'] += 1; return real_reconcile(*args, **kwargs)
        result, raised = None, None
        with patch.object(contract, 'campaign_ledger', lambda live: book), patch.object(driver, 'setup', lambda *a: tools), \
             patch.object(driver, 'prepare', prepare), patch.object(driver.network, 'stage', stage), \
             patch.object(book, '_write_head', head), patch.object(book, 'reconcile', reconcile), patch.object(r6, 'write_json', write_json):
            try: result = driver.execute(run, TASK, 'rehearsal', d, None)
            except Exception as error: raised = {'type': type(error).__name__, 'message': str(error)}
        raw, state = book.snapshot(); rows = ledger.parse(raw)
        permit = next(r for r in rows if r['kind'] == 'reservation')
        terminal = next((r for r in rows if r['kind'] in ('release', 'unknown', 'send_grant')), None)
        event_rows = events.read(run/'events.ndjson')
        seal = J(run/'seal.json') if (run/'seal.json').exists() else None
        if seal:
            assert seal['last_event_hash'] == event_rows[-1]['event_hash']
            assert all(r6.sha(run/p) == digest for p, digest in seal['retained_sha256'].items())
        summary = J(run/'credential-summary.json') if (run/'credential-summary.json').exists() else None
        return {'fault': kind, 'calls': calls, 'result': result, 'raised': raised,
                'sealed': seal is not None, 'terminal_event': event_rows[-1]['event'],
                'summary_error': None if summary is None else summary.get('error'),
                'actual_reservations': state['reservations'], 'actual_open': len(state['open_reservations']),
                'actual_consumed': state['transmissions_consumed'], 'actual_terminal_kind': None if terminal is None else terminal['kind'],
                'authoritative_grant_exists': (book.slot(permit['reservation_id'])/ledger.GRANT_FILE).is_file(),
                'http_object_accepted_by_reader': None if not (run/'stages/proposal-1/output/http.json').exists() else
                    driver.read_record(run/'stages/proposal-1/output/http.json')[1] is None}


def ledger_short_append():
    with tempfile.TemporaryDirectory(prefix='r6-v3-append-probe-') as temp:
        book = ledger.Ledger(Path(temp), contract.policy_sha256()); book.activate(contract.REHEARSAL_AUTHORIZATION, 'rehearsal')
        real_write = os.write; hits = []
        inode = book.path.stat().st_ino
        def short(fd, data):
            if os.fstat(fd).st_ino == inode:
                hits.append(len(data)); return real_write(fd, bytes(data[:7]))
            return real_write(fd, data)
        with patch.object(os, 'write', short): permit = tests.reserve(book, 'append-probe')
        assert len(hits) == 1 and permit['kind'] == 'reservation'
        try: book.snapshot(); raise AssertionError('partial ledger parsed')
        except json.JSONDecodeError as error: failure = type(error).__name__
        return {'reserve_returned_success': True, 'append_bytes_requested': hits[0], 'append_bytes_written': 7,
                'head_rows': J(book.head)['rows'], 'next_snapshot_raises': failure}


def scan_root_canary():
    observations = {}
    for secret_name in (False, True):
        with tempfile.TemporaryDirectory(prefix='r6-v3-root-probe-') as temp:
            d = Path(temp); token = credential.derive(credential.nonce()); header = credential.header(token)
            scan_root = d/(token if secret_name else 'safe-root'); run = scan_root/'episode'
            out = run/'stages/proposal-1/output'; out.mkdir(parents=True)
            nonce = credential.nonce()
            W(out/'http.json', {'commitment_nonce': nonce, 'credential_commitment_sha256':
                hashlib.sha256((operator.COMMITMENT_DOMAIN+':'+nonce+':'+header).encode()).hexdigest()})
            events.append(run, 'episode', 'episode_started', {}, task_id=TASK.id)
            events.append(run, 'episode', 'episode_rejected', {}, task_id=TASK.id)
            driver.publication_driver.seal(run, False)
            cred = d/'synthetic-credential'; cred.write_text(header+'\n'); cred.chmod(0o600)
            report_path = d/'report.json'
            proc = subprocess.run([sys.executable, '-B', str(HERE/'operator_disclosure_scan.py'),
                '--credential-file', str(cred), '--root', str(scan_root), '--bind-runs', str(run), '--report', str(report_path)],
                capture_output=True, timeout=60)
            report = J(report_path); raw = report_path.read_bytes()
            assert token.encode() not in proc.stdout and token.encode() not in proc.stderr
            receipt = report['operator_scan']['run_receipts'][0]
            assert report['accepted'] and all(receipt[k] for k in ('covered_by_scan', 'sealed_and_intact', 'commitment_record_sealed', 'commitment_bound'))
            assert all(token not in str(e['path']) for e in report['inventory'])
            observations['canary_root' if secret_name else 'safe_root'] = {
                'return_code': proc.returncode, 'scan_accepted': report['accepted'],
                'all_four_binding_predicates': True, 'reported_disclosures': len(report['disclosures']),
                'report_token_occurrences': raw.count(token.encode()), 'stdout_token_occurrences': 0,
                'root_label_redacted': report['roots'][0]['name'] is None,
                'unrestricted_entry_roots': sum(token in e['root'] for e in report['inventory'])}
    return observations


def scan_stream_mutation():
    with tempfile.TemporaryDirectory(prefix='r6-v3-scan-audit-probe-') as temp:
        d = Path(temp); root, books = d/'runs', d/'ledgers'
        shutil.copytree(ROOT/'campaign-runs-v3', root); shutil.copytree(ROOT/'ledgers', books)
        baseline = controls.run_audit(root, books); assert baseline == {'accepted': True, 'case_count': 73}
        run = root/'rehearsal-3'; p = run/'publication-scan.json'; report = J(p)
        entry = next(e for e in report['inventory'] if e['path'] == 'solution.ndjson.gz')
        assert entry['streams'] == ['raw', 'gzip'] and report['gzip_streams_scanned'] > 0
        entry['streams'] = ['raw']; report['gzip_streams_scanned'] -= 1; W(p, report)
        nonce = J(run/'credential-canary.json')['nonce']
        W(run/'publication-final.json', publication.final_record(p, credential.derive(nonce), nonce))
        rows = events.read(run/'events.ndjson')
        rows[-1]['payload'].update(publication_scan_sha256=r6.sha(p), publication_final_sha256=r6.sha(run/'publication-final.json'))
        controls.rechain(run, rows); driver.publication_driver.seal(run, True)
        result = controls.run_audit(root, books)
        actual = publication.scan_file(run/'solution.ndjson.gz', publication.patterns(credential.derive(nonce)), run)
        assert actual['streams'] == ['raw', 'gzip']
        return {'unmutated_copy': baseline, 'mutated_copy': result, 'retained_streams': entry['streams'],
                'recomputed_streams': actual['streams'], 'count_updated_consistently': True, 'terminal_and_seal_rebound': True}


def missing_durability():
    run = ROOT/'campaign-runs-v3/rehearsal-3'; permit = J(run/'campaign-permit.json')
    http = J(run/'stages/proposal-1/output/http.json'); rules = audit.RULES['responses_campaign_v3']
    a = audit.Audit(); audit.grant(a, run, 'rehearsal-3', 'proof', permit, http, rules)
    assert 'grant_durable_at_ns' in http; del http['grant_durable_at_ns']
    b = audit.Audit(); audit.grant(b, run, 'rehearsal-3', 'proof', permit, http, rules)
    return {'predicate_only': True, 'unmutated_passed': all(a.cases.values()), 'missing_durability_passed': all(b.cases.values()),
            'scope': 'grant predicate only; no rewritten HTTP digest or full-audit claim'}


def live_unknown_accounting():
    with tempfile.TemporaryDirectory(prefix='r6-v3-live-accounting-probe-') as temp:
        lifecycle = {'permit': {'reservation_id': 'synthetic'}, 'reservation': None, 'reconciliation': None,
                     'reconcile_error': 'synthetic unavailable disposition'}
        value = driver.accounting_for(Path(temp), contract.config(), True, None, None, lifecycle)
        assert value['allowance_consumed'] is None and value['live_transmissions_consumed'] == 0
        return {**{k: value[k] for k in ('allowance_consumed', 'live_transmissions_consumed', 'ledger_reconciled')},
                'scope': 'pure accounting function with live flag; policy remains disabled, no signing or transport'}


def imported_driver_source():
    with tempfile.TemporaryDirectory(prefix='r6-v3-import-probe-') as temp:
        path = Path(temp)/'campaign_episode.py'
        path.write_bytes(Path(driver.__file__).read_bytes()+b'\n# Review-only foreign source copy.\n')
        retained = ROOT/'campaign-runs-v3/rehearsal-3/provenance/campaign-harness/campaign_episode.py'
        assert r6.sha(path) != r6.sha(retained)
        spec = importlib.util.spec_from_file_location('foreign_review_driver', path)
        foreign = importlib.util.module_from_spec(spec); spec.loader.exec_module(foreign)
        assert Path(foreign.accounting_for.__code__.co_filename) == path
        baseline = audit.audit(ROOT/'campaign-runs-v3', ROOT/'ledgers'); assert baseline['accepted']
        with patch.object(audit, 'driver', foreign):
            observed = audit.audit(ROOT/'campaign-runs-v3', ROOT/'ledgers')
        return {'unmutated_audit_accepted': baseline['accepted'], 'foreign_source_audit_accepted': observed['accepted'],
                'audit_cases': observed['case_count'], 'retained_source_sha256': r6.sha(retained),
                'imported_source_sha256': r6.sha(path), 'retained_artifacts_modified': False,
                'scope': 'actual accounting function loaded from a different temporary source copy; harmless comment change'}


CASES = ('interrupted_control', 'http_empty_object', 'reserve_head_failure', 'reservation_receipt_failure',
         'reconciliation_receipt_failure', 'ledger_short_append', 'scan_root_canary', 'scan_stream_mutation', 'missing_durability',
         'live_unknown_accounting', 'imported_driver_source')


def main():
    parser = argparse.ArgumentParser(); parser.add_argument('--output', type=Path, required=True); args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing overwrite')
    contract.verify_sources(); assert contract.NAME == 'responses_campaign_v3' and contract.config()['live_enabled'] is False
    result = {'completed': False, 'policy_sha256': contract.policy_sha256(), 'source_lock_sha256': r6.sha(contract.LOCK),
              'program_sha256': r6.sha(Path(__file__)), 'real_credentials_read': 0, 'provider_calls': 0, 'new_native_episodes': 0,
              'expected_cases': CASES, 'cases': {}}
    for name in CASES:
        observed = production(name) if name in CASES[:5] else globals()[name]()
        result['cases'][name] = observed; W(args.output, result)
        print(name, json.dumps(observed, sort_keys=True), flush=True)
    c = result['cases']
    assert c['interrupted_control']['sealed'] and c['interrupted_control']['actual_consumed'] == 1
    assert c['interrupted_control']['result']['accounting']['grant_committed'] is True
    assert c['http_empty_object']['raised']['type'] == 'KeyError' and not c['http_empty_object']['sealed']
    assert c['http_empty_object']['actual_consumed'] == 1 and c['http_empty_object']['http_object_accepted_by_reader']
    assert c['reserve_head_failure']['calls']['injected'] == 1 and c['reserve_head_failure']['actual_open'] == 1
    assert c['reserve_head_failure']['result']['accounting']['attempts_reserved'] == 0 and c['reserve_head_failure']['result']['ledger_reconciled'] is True
    assert c['reservation_receipt_failure']['actual_open'] == 1 and c['reservation_receipt_failure']['calls']['reconcile_called'] == 0
    assert c['reservation_receipt_failure']['result']['ledger_reconciled'] is False
    assert c['reconciliation_receipt_failure']['actual_open'] == 0 and c['reconciliation_receipt_failure']['actual_consumed'] == 1
    assert 'Reservation left open' in c['reconciliation_receipt_failure']['summary_error']
    assert c['scan_root_canary']['safe_root']['report_token_occurrences'] == 0
    assert c['scan_root_canary']['canary_root']['report_token_occurrences'] > 0
    assert c['scan_root_canary']['canary_root']['return_code'] == 0
    assert c['scan_stream_mutation']['mutated_copy'] == {'accepted': True, 'case_count': 73}
    assert c['missing_durability']['missing_durability_passed']
    assert tuple(result['cases']) == CASES
    result.update(completed=True, case_count=len(CASES)); W(args.output, result)


if __name__ == '__main__': main()
