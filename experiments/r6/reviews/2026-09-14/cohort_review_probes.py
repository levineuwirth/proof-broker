#!/usr/bin/env python3
"""Independent R6-009 review probes. Copies and synthetic loopback only; never live.

An accepted corrupted copy is a review finding, not a passing conformance test.
Each audit mutation first requires the unmutated copy to pass. Source, policies,
original runs and authoritative campaign ledgers are never edited.
"""
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import cohort_budget as budget
import cohort_contract as contract
import cohort_episode as driver
import cohort_ledger as ledger
import credential
import events
import live_tls_fixture
import pricing_gate_v3 as gate
import run as r6

spec = importlib.util.spec_from_file_location('cohort_review_control_helpers', Path(__file__).with_name('cohort_audit_controls.py'))
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
auditor = helpers.audit
J = lambda p: json.loads(Path(p).read_bytes())
W = lambda p, v: Path(p).write_bytes(events.canonical(v)+b'\n')
SHA = lambda b: hashlib.sha256(b).hexdigest()
D1, C8 = 'verinf-d1-70', 'c1-c8-2p18'


def actor_case(directory, name, funded_task, mutation=None):
    """Production host reserve and actor, redirected only to a temporary ledger."""
    d = directory/name; d.mkdir()
    c = contract.config(); assert c['live_enabled'] is False
    task = r6.get_task(D1)
    prepared = J(ROOT/'runs/provider-checkpoint-v1/d1_valid/prepared.json')
    request = budget.request(task, prepared)
    if mutation:
        value = J_bytes(request); mutation(value)
        request = events.canonical(value)+b'\n'
    arguments = budget.arguments(request)
    book = ledger.Ledger(d/'ledger', c['campaign']['id'])
    book.activate(c, False)
    with patch.object(contract, 'campaign_ledger', lambda live, config=None: book):
        permit, raw, admission = budget.reserve('probe', funded_task, 1, arguments, request, ROOT/c['pricing_sources'], False)
    assert admission['accepted'] is True
    assert permit['task_id'] == funded_task and permit['request_sha256'] == SHA(request)
    W(d/'policy.json', c); W(d/'permit.json', permit); W(d/'arguments.json', arguments)
    (d/'request.json').write_bytes(request)
    nonce = credential.nonce(); canary = credential.derive(nonce)
    (d/'credential').write_text(credential.header(canary)+'\n')
    (d/'credential').chmod(0o600)
    W(d/'fixture.json', driver.canned(task, request))
    out = d/'out'; out.mkdir()
    fixture_run = d/'fixture-run'; fixture_run.mkdir()
    with live_tls_fixture.materialize(fixture_run, 'valid') as (ca, cert, key):
        argv = [sys.executable, '-I', '-S', '-B', str(ROOT/'cohort_https.py'),
                '--mode', 'rehearsal', '--policy', str(d/'policy.json'), '--contract', str(contract.CONTRACT),
                '--instruction', str(contract.PROMPT), '--arguments', str(d/'arguments.json'),
                '--credential-file', str(d/'credential'), '--out', str(out), '--sources', str(ROOT/c['pricing_sources']),
                '--permit', str(d/'permit.json'), '--ledger', str(book.path), '--request', str(d/'request.json'),
                '--episode', 'probe', '--task', funded_task, '--draw', '1', '--grant', str(book.grant_slot(permit)),
                '--commitment-nonce', nonce, '--ca', str(ca), '--fixture', str(d/'fixture.json'),
                '--server-cert', str(cert), '--server-key', str(key)]
        proc = subprocess.run(argv, capture_output=True, timeout=120)
    assert proc.returncode == 0, ('actor crashed', proc.returncode)
    http = J(out/'http.json'); server = J(out/'server.json') if (out/'server.json').exists() else {'requests': []}
    request_value = J_bytes(request)
    if http['body_sends_started']:
        received = (out/'received-body.json').read_bytes()
        assert received == (out/'serialized-body.json').read_bytes() == (out/'outbound-body.json').read_bytes()
        assert J_bytes(received) == arguments
    # An exit code alone is deliberately insufficient for release in production.
    # These cases sent, so the grant itself establishes consumption here.
    disposition, _ = book.reconcile(permit, {'exit_code': proc.returncode}, http, {})
    return {'host_admitted': True, 'request_task_id': request_value['binding'].get('task_id'),
            'funded_task_id': permit['task_id'], 'task_ids_differ': request_value['binding'].get('task_id') != permit['task_id'],
            'request_has_policy_sha256': 'policy_sha256' in request_value,
            'request_sha256': SHA(request), 'http_status': http['http_status'],
            'failure_category': http['failure_category'], 'body_sends_started': http['body_sends_started'],
            'receiver_requests': len(server['requests']), 'actor_pricing_accepted': J(out/'pricing-check.json')['accepted'],
            'ledger_disposition': disposition['kind'], 'ledger_state': book.snapshot()[1]}


def J_bytes(b): return json.loads(b)


def actor_probes(scratch):
    records = {}
    cases = [('unaltered_d1', D1, None), ('d1_request_funded_as_c8', C8, None),
             ('request_policy_digest_injected', D1, lambda v: v.__setitem__('policy_sha256', contract.policy_sha256())),
             ('request_task_binding_deleted', D1, lambda v: v['binding'].pop('task_id'))]
    for name, task, mutation in cases:
        records[name] = actor_case(scratch, name, task, mutation)
        print(name, {k: records[name][k] for k in ('http_status', 'body_sends_started', 'task_ids_differ')}, flush=True)
    assert set(records) == {c[0] for c in cases}
    assert records['unaltered_d1']['http_status'] == 200
    assert records['d1_request_funded_as_c8']['task_ids_differ']
    return records


def change_json(run, relative, change):
    p = run/relative; value = J(p); old = events.canonical(value)
    change(value); assert events.canonical(value) != old, 'vacuous mutation'
    W(p, value)


def mutate_artifact(name, run, rows):
    out = 'stages/proposal-1/output/'
    if name in ('serialized_body_altered', 'outbound_body_altered', 'received_body_altered'):
        base = name.removesuffix('_altered').replace('_', '-')+'.json'
        change_json(run, out+base, lambda v: v['input'][0].__setitem__('content', v['input'][0]['content']+' ALTERED'))
    elif name == 'raw_provider_response_altered':
        change_json(run, out+'provider-response.json', lambda v: v.__setitem__('status', 'failed'))
    elif name == 'reconstruction_context_false':
        change_json(run, 'stages/reconstruct/output/context.json', lambda v: v.__setitem__('target', 'False'))
        matches = [r for r in rows if r['event'] == 'context_validated' and r['stage'] == 'reconstruct']
        assert len(matches) == 1
        matches[0]['payload']['captured_context_sha256'] = r6.sha(run/'stages/reconstruct/output/context.json')
    elif name == 'summary_wrong_task':
        change_json(run, 'credential-summary.json', lambda v: v.__setitem__('task_id', C8))
    elif name == 'summary_nested_allowance_zero':
        change_json(run, 'credential-summary.json', lambda v: v['accounting'].__setitem__('allowance_consumed', 0))
    elif name == 'accounting_allowance_zero':
        change_json(run, 'accounting.json', lambda v: v.__setitem__('allowance_consumed', 0))
    elif name == 'credential_receipt_false':
        change_json(run, 'credential-receipt.json', lambda v: v.__setitem__('exact_receipt', False))
    elif name == 'proposer_attribution_altered':
        matches = [r for r in rows if r['event'] == 'recovery_started']
        assert len(matches) == 1 and matches[0]['payload']['proposer'] == 'canned_provider_response'
        matches[0]['payload']['proposer'] = 'live_model_response'
    elif name == 'authoritative_ledger_mount_changed':
        def alter(v):
            argv = v['argv']; hits = [i for i, x in enumerate(argv) if x == '/ledger.ndjson']
            # One mount destination and one CLI argument.
            hits = [i for i in hits if i >= 2 and argv[i-2] == '--ro-bind']
            assert len(hits) == 1
            argv[hits[0]-1] = '/tmp/non-authoritative-ledger.ndjson'
        change_json(run, 'stages/proposal-1/command.json', alter)
    elif name == 'retained_imported_module_changed':
        p = run/'provenance/campaign-harness/campaign_ledger.py'
        assert p.exists()
        p.write_bytes(p.read_bytes()+b'\n# altered retained imported module\n')
    else: raise AssertionError(name)


AUDIT_MUTATIONS = ('serialized_body_altered', 'outbound_body_altered', 'received_body_altered',
                   'raw_provider_response_altered', 'reconstruction_context_false', 'summary_wrong_task',
                   'summary_nested_allowance_zero', 'accounting_allowance_zero', 'credential_receipt_false',
                   'proposer_attribution_altered', 'authoritative_ledger_mount_changed', 'retained_imported_module_changed',
                   'unlisted_file_after_seal', 'publication_report_rejected', 'audit_case_removed')


def audit_probes(scratch):
    results = {}
    for name in AUDIT_MUTATIONS:
        with tempfile.TemporaryDirectory(prefix='audit-copy-', dir=scratch) as temp:
            d = Path(temp); root = d/'runs'; books = d/'ledgers'
            shutil.copytree(ROOT/'cohort-runs', root)
            shutil.copytree(ROOT/'ledgers/campaigns', books)
            baseline = helpers.run_audit(root, books); assert baseline['accepted'], baseline
            run = root/'r2-d1-draw3'
            if name == 'audit_case_removed':
                original = auditor.Audit.require
                def omit(self, ok, case, detail=''):
                    if case == 'r2-d1-draw3:proof:shared_checker': return
                    return original(self, ok, case, detail)
                with patch.object(auditor.Audit, 'require', omit):
                    observed = helpers.run_audit(root, books)
            elif name == 'unlisted_file_after_seal':
                (run/'unlisted-evidence.txt').write_text('added after scan and seal\n')
                observed = helpers.run_audit(root, books)
            elif name == 'publication_report_rejected':
                # Coherent report/terminal/seal hashes; one false publication
                # result alongside an unchanged terminal acceptance must reject.
                change_json(run, 'publication-scan.json', lambda v: v.__setitem__('accepted', False))
                event_rows = events.read(run/'events.ndjson')
                event_rows[-1]['payload']['publication_scan_sha256'] = r6.sha(run/'publication-scan.json')
                helpers.rechain(run, event_rows)
                driver.publication_driver.seal(run, True)
                observed = helpers.run_audit(root, books)
            else:
                helpers.refinalize(run, lambda r, rows: mutate_artifact(name, r, rows))
                observed = helpers.run_audit(root, books)
            results[name] = {'unmutated_copy': baseline, 'mutated_copy': observed}
            print(name, observed, flush=True)
    assert set(results) == set(AUDIT_MUTATIONS)
    return results


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode', choices=['actor', 'audit'])
    p.add_argument('--scratch', required=True, type=Path)
    p.add_argument('--output', required=True, type=Path)
    args = p.parse_args()
    assert not args.output.exists(), 'refusing to overwrite output'
    args.scratch.mkdir(parents=True, exist_ok=False)
    record = {'scope': 'independent review probes; synthetic loopback or copied artifacts; no native Lean replay',
              'live_model_calls': 0, 'real_credentials_read': 0,
              'program_sha256': r6.sha(Path(__file__)), 'mode': args.mode, 'complete': False}
    W(args.output, record)
    results = actor_probes(args.scratch) if args.mode == 'actor' else audit_probes(args.scratch)
    record.update(complete=True, results=results)
    W(args.output, record)


if __name__ == '__main__': main()
