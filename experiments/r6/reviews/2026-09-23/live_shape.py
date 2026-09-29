#!/usr/bin/env python3
"""R6-014 live-shaped canned evidence for reviewing the live auditor before any signature. SYNTHETIC: no provider was contacted, no real
credential exists here, and nothing below authorizes or funds a transmission.

Source: the v7 canned rehearsal runs of the eleven posed sites, draw 1 (loopback-only transport, synthetic canaries). Each is copied into
`fixtures/r6-014-live-shaped/runs/` and rebound to an **isolated test policy** — frozen and signed in the fixture tree by the production
`cohort_contract.freeze`/`sign` (approver `synthetic-operator`, scope = block 1) — and to that policy's own ledgers under the fixture tree,
through the production functions:

* host and actor pricing admissions recomputed under the signed test policy (`pricing_gate_v4.admission`, at each record's own time);
* the slot reserved, granted and reconciled on the fixture's live ledger (`cohort_ledger.reserve`, `commit_grant`, `reconcile`);
* the sender command rebuilt in its live form (`campaign_network.command`, shared network, the pinned public CA, the operator credential
  file outside the tree), exactly as `cohort_episode.invoke` builds it in live mode;
* the transport record and receipts in their live form: `mode: live`, `provider_request`, no local receiver, a use receipt instead of an
  exact receipt, the commitment recomputed for one synthetic operator credential (`credential.derive(OPERATOR_NONCE)`);
* attribution as a live witness; accounting recomputed live; scan, terminal event and seal by the production `finalize(..., live=True)`.

The proof, reconstruction and replay records are the rehearsal's own, unchanged. The operator scan is the frozen
`reviews/2026-09-13/operator_disclosure_scan.py`, run with the synthetic credential over the fixture tree, binding every run.
"""
import argparse
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
import campaign_network
import cohort_budget as budget
import cohort_contract as contract
import cohort_episode as driver
import cohort_ledger as ledger
import credential
import events
import pricing_gate_v2 as v2
import pricing_gate_v4 as gate
import run as r6
import site_task

FIXTURE = ROOT/'fixtures/r6-014-live-shaped'
SOURCE_RUNS = ROOT/'cohort-runs-v7'
CAPTURE = ROOT/'sources/pricing-approved-campaign-3'
APPROVED = '2026-09-22T21:00:00Z'
SCOPE = 'SYNTHETIC live-shaped fixture for auditor review; isolated test policy and ledgers; no transmission'
OPERATOR_NONCE = 'f'*62+'14'  # the one synthetic operator credential every fixture run commits to
SITES = contract.POSABLE


def rel(path): return str(Path(path).relative_to(ROOT))


def write(path, value): r6.write_json(path, value)


def sign_test_policy():
    """The isolated test policy, frozen and signed by the production functions inside the fixture tree."""
    now = max(v['finished_unix'] for v in v2.source_evidence(CAPTURE).values()) + 3600
    contract.freeze(CAPTURE)
    contract.sign('synthetic-operator', APPROVED, {s: 1 for s in SITES}, CAPTURE, SCOPE, now=now)
    return contract.config()


def transform(name, policy, credential_file):
    src, dst = SOURCE_RUNS/name, FIXTURE/'runs'/name
    shutil.copytree(src, dst)
    for command in list(dst.glob('stages/*/command.json')) + list(dst.glob('stages/*/scope-command.json')):
        command.write_text(command.read_text().replace(str(src), str(dst)))
    policy_bytes = contract.CONFIG.read_bytes(); book = contract.campaign_ledger(True, policy)
    sp = r6.read_json(dst/'search-policy.json'); task_id, draw = sp['task_id'], sp['draw']
    site_task.get(task_id)  # registered in process, as the driver registers it, before any event is written
    sp.update(mode='live', config_sha256=r6.hashlib.sha256(policy_bytes).hexdigest(), campaign_id=policy['campaign']['id'], revision=policy['revision'],
              ledger_path=rel(book.path), ledger_slots=rel(book.slots), ledger_scope='live authorization ledger')
    write(dst/'search-policy.json', sp)
    (dst/'provenance/cohort-harness/policies'/contract.CONFIG.name).write_bytes(policy_bytes)
    roles = r6.read_json(dst/'provenance/roles.json'); roles['ledger_directory'] = str(contract.LEDGERS); write(dst/'provenance/roles.json', roles)
    (dst/'transport-policy.json').write_bytes(policy_bytes)
    live_payload = r6.read_json(dst/'live-payload.json'); live_payload['policy_sha256'] = r6.hashlib.sha256(policy_bytes).hexdigest(); write(dst/'live-payload.json', live_payload)
    request = (dst/'live-request.json').read_bytes(); arguments = r6.read_json(dst/'live-arguments.json'); instruction = contract.PROMPT.read_text()
    host = r6.read_json(dst/'host-pricing-admission.json')
    admitted = gate.admission(policy, contract.contract(), instruction, dst/'pricing-sources', arguments, request, host['evaluated_at_unix'])
    write(dst/'host-pricing-admission.json', admitted)
    old = r6.read_json(dst/'campaign-permit.json')
    bindings = {k: old[k] for k in ('request_sha256', 'arguments_sha256', 'contract_sha256', 'task_manifest_sha256', 'challenge_sha256')}
    row, raw = book.reserve(name, policy, task_id, draw, budget.reservation(arguments), bindings, admitted, old['attempt_id'])
    write(dst/'campaign-permit.json', row); (dst/'transport-ledger.ndjson').write_bytes(raw)
    reservation = {**row['reservation'], 'reservation_id': row['reservation_id'], 'request_sha256': row['request_sha256'], 'arguments_sha256': row['arguments_sha256'],
                   'policy_sha256': row['policy_sha256'], 'pricing_admission_sha256': r6.sha(dst/'host-pricing-admission.json'),
                   'ledger_row_hash': row['row_hash'], 'ledger_sha256': r6.sha(dst/'transport-ledger.ndjson')}
    write(dst/'reservation.json', reservation)
    out = dst/'stages/proposal-1/output'
    check = r6.read_json(out/'pricing-check.json')
    write(out/'pricing-check.json', {**gate.admission(policy, contract.contract(), instruction, dst/'transport-pricing-sources', arguments, request, check['evaluated_at_unix']),
                                     'admitted_at_ns': check['admitted_at_ns']})
    http = r6.read_json(out/'http.json'); slot = book.grant_slot(row)
    if http['grant_committed']:
        grant = ledger.grant_record(row, http['grant_created_at_ns']); ledger.commit_grant(slot, grant); http['grant_id'] = grant['grant_id']
    header = credential.header(credential.derive(OPERATOR_NONCE))
    http.update(policy_sha256=r6.sha(dst/'transport-policy.json'), mode='live', transport_scope='provider_request', authorization_present_in_policy=True,
                fixture_tcp_port=None, reservation_id=row['reservation_id'], ca_bundle_sha256=policy['tls']['public_ca_bundle']['sha256'],
                credential_commitment_sha256=r6.hashlib.sha256((contract.COMMITMENT_DOMAIN+':'+http['commitment_nonce']+':'+header).encode()).hexdigest())
    write(out/'http.json', http)
    write(out/'server.json', {'requests': [], 'server_names': [], 'scope': 'no local receiver in live mode'})
    (out/'received-body.json').unlink(missing_ok=True)
    runtime_path, runtime = contract.materialize_runtime(); ca_path, _ = contract.bundle(); limits = policy['limits']
    common = [(runtime_path, runtime['stdlib']), (ROOT/'cohort_https.py', '/adapter.py'), (ROOT/'live_https.py', '/live_https.py'), (ROOT/'pricing_gate_v2.py', '/pricing_gate_v2.py'),
              (ROOT/'pricing_gate_v4.py', '/pricing_gate_v4.py'), (ROOT/'campaign_ledger.py', '/campaign_ledger.py'), (ROOT/'cohort_ledger.py', '/cohort_ledger.py'),
              (dst/'transport-policy.json', '/policy.json'), (dst/'transport-contract.json', '/contract.json'), (dst/'transport-instruction.txt', '/instruction.txt'),
              (dst/'transport-arguments.json', '/arguments.json'), (dst/'transport-request.json', '/request.json'), (dst/'transport-pricing-sources', '/pricing-sources'),
              (dst/'campaign-permit.json', '/permit.json'), (book.path, '/ledger.ndjson')]
    argv = ['-I', '-S', '-B', '/adapter.py', '--mode', 'live', '--policy', '/policy.json', '--contract', '/contract.json', '--instruction', '/instruction.txt',
            '--arguments', '/arguments.json', '--credential-file', '/credential', '--ca', '/ca.pem', '--out', '/out', '--request', '/request.json',
            '--sources', '/pricing-sources', '--permit', '/permit.json', '--ledger', '/ledger.ndjson', '--episode', name,
            '--task', task_id, '--draw', str(draw), '--grant', '/grant', '--commitment-nonce', http['commitment_nonce']]
    _, spec = campaign_network.command(dst, 'proposal-1', Path(runtime['python']), argv, [*common, (credential_file, '/credential'), (ca_path, '/ca.pem')], slot,
                                       shared_network=True, extra_binaries=[Path(p) for p in runtime['extension_binaries']], wall=limits['request_wall_seconds'],
                                       cpu=limits['request_cpu_seconds'], memory=limits['request_memory_bytes'], output_limit=limits['request_output_bytes'])
    write(dst/'stages/proposal-1/command.json', spec)
    stage = dst/'stages/proposal-1'; process = r6.read_json(stage/'proposal-1.process.json')
    evidence = {'process_sha256': r6.sha(stage/'proposal-1.process.json'), 'http_sha256': r6.sha(out/'http.json'),
                'grant_file_sha256': r6.sha(slot/ledger.GRANT_FILE) if (slot/ledger.GRANT_FILE).exists() else None, 'launched': True,
                'process_exit_code': process.get('exit_code'), 'record_read_failures': []}
    terminal, after = book.reconcile(row, process, http, evidence, True)
    shutil.rmtree(stage/'grant'); (stage/'grant').mkdir()
    for item in sorted(slot.iterdir()): shutil.copyfile(item, stage/'grant'/item.name)
    (dst/'ledger-after.ndjson').write_bytes(after); write(dst/'campaign-reconciliation.json', terminal)
    proposed, text, metadata, validation, error = budget.interpret(out, request, True)
    write(dst/'transport-validation.json', validation); write(dst/'provider-metadata.json', metadata)
    receipt = {'schema_version': 'r6-campaign-credential-use-1', 'channel': 'operator_credential_file', 'http_status': http['http_status'],
               'credential_use_accepted': http['http_status'] is not None and 200 <= http['http_status'] < 300, 'exact_receipt': None,
               'credential_commitment_sha256': http['credential_commitment_sha256'], 'commitment_nonce': http['commitment_nonce'],
               'evidence_scope': 'a 2xx provider status is evidence that the request was authenticated and processed; it is not a '
                                 'digest-matched receipt of a particular credential, and 4xx/5xx statuses other than 401 are not receipts either'}
    write(dst/'credential-receipt.json', receipt)
    live_proposer = policy['attribution']['witness_proposer']
    if (dst/'verdict.json').exists():
        verdict = r6.read_json(dst/'verdict.json'); verdict['witness_proposer'] = live_proposer; verdict['mode'] = 'live'; write(dst/'verdict.json', verdict)
    lifecycle = {'permit': row, 'reservation': reservation, 'reconciliation': terminal, 'reconcile_error': None, 'reservation_state': 'reserved', 'evidence_write_failures': []}
    accounting = driver.accounting_for(dst, policy, True, http, r6.read_json(out/'server.json'), lifecycle); write(dst/'accounting.json', accounting)
    summary = r6.read_json(dst/'credential-summary.json')
    summary.update(mode='live', campaign_id=policy['campaign']['id'], revision=policy['revision'], contract_sha256=contract.contract_sha256(),
                   credential_use_accepted=receipt['credential_use_accepted'], ledger_reconciled=accounting['ledger_reconciled'],
                   reservation_state=accounting['reservation_state'], reconciliation_evidence_complete=accounting['reconciliation_evidence_complete'],
                   evidence_complete=accounting['evidence_complete'], accounting=accounting, scope=policy['scope'])
    write(dst/'credential-summary.json', summary)
    rows = events.read(dst/'events.ndjson'); rows.pop()
    rewritten = []
    for r in rows:
        key = (r['stage'], r['event']); p = r['payload']
        if key == ('episode', 'episode_started'): p.update(policy_sha256=r6.sha(dst/'search-policy.json'), mode='live')
        elif key == ('pricing-admission', 'pricing_admitted'): p['admission_sha256'] = r6.sha(dst/'host-pricing-admission.json')
        elif key == ('live-payload', 'payload_validated'): r['payload'] = live_payload
        elif key == ('campaign-ledger', 'request_reserved'): r['payload'] = reservation
        elif key == ('campaign-ledger', 'reservation_reconciled'):
            r['payload'] = {'kind': terminal['kind'], 'reservation_id': terminal['reservation_id'], 'row_hash': terminal['row_hash'], 'send_outcome': terminal.get('send_outcome'),
                            'termination_established': terminal['termination_established'], 'record_read_failures': 0, 'evidence_write_failures': [],
                            'ledger_sha256': r6.sha(dst/'ledger-after.ndjson'), 'recovered': None}
        elif key == ('proposal', 'https_observed'):
            r['payload'] = {'http_sha256': r6.sha(out/'http.json'), 'server_sha256': r6.sha(out/'server.json'), 'pricing_check_sha256': r6.sha(out/'pricing-check.json')}
        elif key == ('proposal', 'transport_validated'): r['payload'] = validation
        elif key == ('credential-receipt', 'credential_receipt_checked'): r['event'] = 'credential_use_checked'; r['payload'] = receipt
        elif r['event'] in ('recovery_started', 'recovery_finished'): p['proposer'] = live_proposer
        elif r['event'] == 'certificate_assembled': p['witness_proposer'] = live_proposer
        elif r['event'] == 'proof_validated': p['verdict_sha256'] = r6.sha(dst/'verdict.json')
        rewritten.append(r)
        if key == ('campaign-ledger', 'request_reserved'):
            rewritten.append({**r, 'stage': 'proposal', 'event': 'live_transport_authorized', 'payload': {
                'approved_by': policy['authorization']['approved_by'], 'approved_utc': policy['authorization']['approved_utc'],
                'ca_bundle_sha256': policy['tls']['public_ca_bundle']['sha256'], 'network_namespace': 'shared_with_host', 'reservation_id': row['reservation_id'],
                'slot': {'task_id': task_id, 'draw': draw}, 'commitment_nonce': http['commitment_nonce'], 'credential_source': 'operator file; value never copied'}})
    previous = '0'*64
    for i, r in enumerate(rewritten):
        r.update(sequence=i, previous_hash=previous); r.pop('event_hash', None); r['event_hash'] = events.digest(r); previous = r['event_hash']
    (dst/'events.ndjson').write_bytes(b''.join(events.canonical(r)+b'\n' for r in rewritten))
    for n in ('publication-scan.json', 'publication-final.json', 'seal.json'): (dst/n).unlink()
    nonce = r6.read_json(dst/'credential-canary.json')['nonce']
    driver.finalize(dst, credential.derive(nonce), nonce, summary, True)
    return {'run': name, 'kind': terminal['kind'], 'reservation_id': row['reservation_id']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    if FIXTURE.exists(): raise SystemExit('fixture exists: '+str(FIXTURE))
    for n in [f'{s.removeprefix("bracket-")}-draw1' for s in SITES]:
        if not (SOURCE_RUNS/n/'seal.json').exists(): raise SystemExit('source run missing: '+n)
    (FIXTURE/'policies').mkdir(parents=True); (FIXTURE/'runs').mkdir()
    with tempfile.TemporaryDirectory(prefix='r6-014-operator-') as temp:
        secret = Path(temp)/'operator-credential'; secret.write_text(credential.header(credential.derive(OPERATOR_NONCE))+'\n'); secret.chmod(0o600)
        with patch.object(contract, 'CONFIG', FIXTURE/'policies'/contract.CONFIG.name), patch.object(contract, 'LOCK', FIXTURE/'policies'/contract.LOCK.name), \
             patch.object(contract, 'CHECKPOINT', FIXTURE/'policies'/contract.CHECKPOINT.name), patch.object(contract, 'LEDGERS', FIXTURE/'ledgers/campaigns'):
            policy = sign_test_policy()
            order = sorted((r6.read_json(SOURCE_RUNS/f'{s.removeprefix("bracket-")}-draw1/campaign-permit.json')['sequence'], f'{s.removeprefix("bracket-")}-draw1') for s in SITES)
            results = [transform(name, policy, secret) for _, name in order]
        report = FIXTURE/'operator-disclosure-scan.json'
        scan = subprocess.run([sys.executable, str(ROOT/'reviews/2026-09-13/operator_disclosure_scan.py'), '--credential-file', str(secret), '--report', str(report),
                               '--root', str(FIXTURE), '--bind-runs', *[str(FIXTURE/'runs'/r['run']) for r in results]], capture_output=True, text=True)
        summary = json.loads(scan.stdout[:scan.stdout.rstrip().rfind('\n')]) if scan.stdout.strip() else None
    r6.write_json(FIXTURE/'operator-scan-summary.json', {'exit_code': scan.returncode, 'summary': summary})
    r6.write_json(FIXTURE/'FIXTURE.json', {'schema_version': 'r6-live-shaped-fixture-1', 'synthetic': True, 'source_runs': rel(SOURCE_RUNS), 'runs': results,
        'test_policy_sha256': r6.sha(FIXTURE/'policies'/contract.CONFIG.name), 'operator_credential': 'credential.derive(OPERATOR_NONCE); synthetic, never a real credential',
        'program_sha256': r6.sha(Path(__file__)), 'scope': 'no provider was contacted; no real credential; nothing here authorizes or funds a transmission'})
    print(json.dumps({'runs': len(results), 'scan_exit': scan.returncode, 'bound': (summary or {}).get('bound_runs_accepted')}, indent=1))


if __name__ == '__main__':
    main()
