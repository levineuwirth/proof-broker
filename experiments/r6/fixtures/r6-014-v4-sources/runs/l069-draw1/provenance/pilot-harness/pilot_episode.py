#!/usr/bin/env python3
"""R6-007 driver: one rehearsed path to the provider.

`--mode rehearsal` runs the complete episode against a canned TLS receiver on
loopback with a synthetic canary, through `episode.stage` and `--unshare-all`.
`--mode live` runs the same preparation, the same pilot-bound admission and
ledger, the same actor and the same downstream consumption, with three audited
differences: the network-sharing stage, the pinned public bundle and the
operator's credential file. The actor decides which destination it is allowed
to reach from the mounted policy, not from this driver.
"""
import argparse
import json
from pathlib import Path
import shutil
import time

import admission
import credential
import credential_episode as publication_driver
import episode
import events
import live_tls_fixture
import pilot_budget as budget
import pilot_contract as contract
import pilot_network
import priced_episode_v2 as previous
import provider_episode as consumer
import provider_payload
import pricing_gate_v2 as gate
import run as r6

MODES = ('rehearsal', 'live')


def setup(run, task, packages):
    """R6-003's setup, replicated against the pilot's own runtime pin.

    The frozen `provider_episode.setup` materializes R6-003's runtime record,
    which names a host library that no longer exists. The Lean tools, binaries
    and provenance copies are unchanged; only the Python runtime pin is the
    pilot's, and its divergence from R6-003's is recorded in the policy.
    """
    contract.verify_sources()
    runtime_path, runtime = contract.materialize_runtime()
    tools = consumer.downstream.setup(run, task, packages)
    tools.update(python=Path(runtime['python']), runtime=runtime, runtime_path=runtime_path)
    binaries = r6.read_json(run/'provenance/binaries.json')
    binaries[runtime['python']] = runtime['python_sha256']
    r6.write_json(run/'provenance/binaries.json', binaries)
    r6.write_json(run/'provenance/python-runtime.json', runtime)
    r6.write_json(run/'provenance/roles.json', {'python': runtime['python'], 'runtime_path': str(runtime_path),
        'actor_source': str(r6.ROOT/'pilot_https.py'), 'network_stage': str(r6.ROOT/'pilot_network.py'),
        'unused_legacy_responder': str(tools['fixture']), 'assembler': str(tools['driver']),
        'verifier': str(tools['verifier']), 'checker': str(tools['checker']),
        'runtime_pin': 'pilot-runtime-v1; diverges from provider-runtime-v1 as recorded in the policy',
        'downstream_setup': 'frozen proposal_episode.setup; earlier request policies not executed'})
    chain = [('pilot-harness', contract, [contract.RUNTIME])]
    module = contract.previous
    while module is not None:
        name = module.__name__.replace('_contract', '').replace('_', '-')
        extra = [module.RUNTIME] if getattr(module, 'RUNTIME', None) and Path(module.RUNTIME).exists() else []
        chain.append((name+'-harness', module, extra))
        module = getattr(module, 'previous', None)
    for section, module, extra in chain:
        for source in [r6.ROOT/name for name in module.FILES]+[module.CONFIG, module.LOCK]+extra:
            target = run/'provenance'/section/source.relative_to(r6.ROOT)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
    return tools


def prepare(run, task, tools):
    prepared = consumer.prepare(run, task, tools)
    request = budget.request(task, prepared)
    (run/'live-request.json').write_bytes(request)
    args = budget.arguments(request)
    r6.write_json(run/'live-arguments.json', args)
    r6.write_json(run/'live-messages.json', args['input'])
    record = {'request_sha256': gate.sha(request), 'policy_sha256': r6.sha(contract.CONFIG),
              'prompt_sha256': r6.sha(contract.PROMPT), 'arguments_sha256': r6.sha(run/'live-arguments.json'),
              'messages_sha256': r6.sha(run/'live-messages.json'), 'prepared_sha256': r6.sha(run/'prepared.json'),
              'preparation_request_sha256': r6.sha(run/'request.json'),
              'inner_binding': 'request policy_sha256 is this pilot policy; the preparation component request is retained separately'}
    r6.write_json(run/'live-payload.json', record)
    events.append(run, 'live-payload', 'payload_validated', record)
    return request


def canned(task, request):
    fixture = consumer.canned_provider(task, request, 'valid')
    obj = json.loads(fixture['body'])
    obj['model'] = contract.MODEL
    obj['service_tier'] = 'default'
    fixture['body'] = (events.canonical(obj)+b'\n').decode()
    return fixture


def invoke(run, tools, mode, nonce, credential_file):
    c = contract.config(); runtime = tools['runtime']; limits = c['limits']
    live = mode == 'live'
    request = (run/'live-request.json').read_bytes()
    shutil.copytree(contract.SOURCES, run/'pricing-sources')
    try:
        row = budget.reserve(run/'reservation-ledger.ndjson', run.name,
                             r6.read_json(run/'live-arguments.json'), request, run/'pricing-sources')
    except gate.Failure as failure:
        denied = {'accepted': False, 'failure_code': failure.code, 'evaluated_at_unix': time.time()}
        r6.write_json(run/'host-pricing-admission.json', denied)
        events.append(run, 'pricing-admission', 'pricing_rejected', denied)
        receipt = publication_driver.receipt(run, {'requests': []}, credential.derive(nonce), mode)
        accounting = {'attempts_reserved': 0, 'reservation': None, 'connection_attempts': 0, 'headers_started': 0,
                      'bodies_started': 0, 'bodies_returned': 0, 'endpoint_receipts': 0,
                      'usage': provider_payload.usage({}), 'usage_status': 'unreported',
                      'priced_usage_ceiling_micro_usd': None, 'live_model_calls': 0, 'live_model_cost_usd': None,
                      'scope': 'host pricing rejection before ledger or transport'}
        r6.write_json(run/'accounting.json', accounting)
        return None, budget.previous.Failure('pricing_admission', 'pricing_admission', 'Pricing admission: '+failure.code), receipt, accounting
    r6.write_json(run/'host-pricing-admission.json', row['pricing_admission'])
    events.append(run, 'pricing-admission', 'pricing_admitted', {'admission_sha256': r6.sha(run/'host-pricing-admission.json')})
    reservation = {**row['reservation'], 'request_sha256': gate.sha(request),
                   'arguments_sha256': r6.sha(run/'live-arguments.json'), 'policy_sha256': r6.sha(contract.CONFIG),
                   'pricing_admission_sha256': r6.sha(run/'host-pricing-admission.json')}
    r6.write_json(run/'reservation.json', reservation)
    events.append(run, 'proposal', 'request_reserved', reservation)

    # Immutable transport inputs: what the actor is given is exactly what was admitted.
    shutil.copytree(run/'pricing-sources', run/'transport-pricing-sources')
    shutil.copyfile(run/'live-arguments.json', run/'transport-arguments.json')
    (run/'transport-request.json').write_bytes(request)
    r6.write_json(run/'pricing-permit.json', row)
    (run/'transport-ledger.ndjson').write_bytes(gate.canonical(row)+b'\n')
    r6.write_json(run/'transport-policy.json', c)

    common = [(tools['runtime_path'], runtime['stdlib']), (r6.ROOT/'pilot_https.py', '/adapter.py'),
              (r6.ROOT/'live_https.py', '/live_https.py'), (r6.ROOT/'pricing_gate_v2.py', '/pricing_gate_v2.py'),
              (run/'transport-policy.json', '/policy.json'), (run/'transport-arguments.json', '/arguments.json'),
              (run/'transport-request.json', '/request.json'), (run/'transport-pricing-sources', '/pricing-sources'),
              (run/'pricing-permit.json', '/permit.json'), (run/'transport-ledger.ndjson', '/ledger.ndjson')]
    argv = ['-I', '-S', '-B', '/adapter.py', '--mode', mode, '--policy', '/policy.json', '--arguments', '/arguments.json',
            '--credential-file', '/credential', '--ca', '/ca.pem', '--out', '/out', '--request', '/request.json',
            '--sources', '/pricing-sources', '--permit', '/permit.json', '--ledger', '/ledger.ndjson', '--episode', run.name]
    budgets = dict(extra_binaries=[Path(p) for p in runtime['extension_binaries']], wall=limits['request_wall_seconds'],
                   cpu=limits['request_cpu_seconds'], memory=limits['request_memory_bytes'],
                   output_limit=limits['request_output_bytes'])
    if live:
        ca_path, described = contract.bundle()
        if described['sha256'] != c['tls']['public_ca_bundle']['sha256']: raise ValueError('pilot_ca_bundle_binding')
        events.append(run, 'proposal', 'live_transport_authorized', {
            'approved_by': c['authorization']['approved_by'], 'approved_utc': c['authorization']['approved_utc'],
            'ca_bundle_sha256': described['sha256'], 'network_namespace': 'shared_with_host',
            'credential_source': 'operator file; value never copied'})
        out = pilot_network.stage(run, 'proposal-1', tools['python'], argv,
                                  [*common, (Path(credential_file), '/credential'), (ca_path, '/ca.pem')], **budgets)
        canary = None
    else:
        r6.write_json(run/'canned-provider.json', canned(r6.get_task(r6.read_json(run/'search-policy.json')['task_id']), request))
        argv += ['--fixture', '/fixture.json', '--server-cert', '/server.pem', '--server-key', '/server.key']
        with credential.delivery(nonce) as (canary, secret), live_tls_fixture.materialize(run, 'valid') as (ca, cert, key):
            out = episode.stage(run, 'proposal-1', tools['python'], argv,
                                [*common, (run/'canned-provider.json', '/fixture.json'), (secret, '/credential'),
                                 (ca, '/ca.pem'), (cert, '/server.pem'), (key, '/server.key')], **budgets)
    http, server = r6.read_json(out/'http.json'), r6.read_json(out/'server.json')
    events.append(run, 'proposal', 'https_observed', {'http_sha256': r6.sha(out/'http.json'),
        'server_sha256': r6.sha(out/'server.json'), 'pricing_check_sha256': r6.sha(out/'pricing-check.json')})
    proposed, text, metadata, validation, error = budget.interpret(out, request, live)
    r6.write_json(run/'transport-validation.json', validation); r6.write_json(run/'provider-metadata.json', metadata)
    if text is not None: (run/'response.json').write_bytes(text)
    events.append(run, 'proposal', 'transport_validated', validation)
    if live:
        # No local receiver exists; the only receipt evidence is the provider's
        # authenticated response, which is recorded as such and not as a canary match.
        receipt = {'schema_version': 'r6-live-receipt-1', 'channel': 'operator_credential_file',
                   'exact_receipt': http['http_status'] is not None and http['http_status'] != 401,
                   'evidence': 'provider HTTP status', 'http_status': http['http_status'],
                   'scope': 'a non-401 provider status is the only observable that the credential was accepted; '
                            'no endpoint digest exists for a real provider'}
        r6.write_json(run/'credential-receipt.json', receipt)
        events.append(run, 'credential-receipt', 'credential_receipt_checked', receipt)
    else:
        receipt = publication_driver.receipt(run, server, canary, mode)
        if error is None and not receipt['exact_receipt']:
            error = budget.previous.Failure('credential_receipt_failure', 'credential_receipt', 'Endpoint did not receive the expected credential')
    raw = (out/'provider-response.json').read_bytes() if (out/'provider-response.json').exists() else None
    usage = provider_payload.usage({}); status = 'unreported'
    if raw is not None:
        try: usage = provider_payload.usage(json.loads(raw)); status = usage['status']
        except (ValueError, AttributeError, TypeError): status = 'invalid'
    estimate = (None if usage['input_tokens'] is None or usage['output_tokens'] is None
                else gate.cost_micro(usage['input_tokens'], usage['output_tokens'], c['pricing']['nano_usd_per_token']))
    accounting = {'attempts_reserved': 1, 'reservation': reservation, 'connection_attempts': http['connection_attempts'],
                  'headers_started': http['header_sends_started'], 'bodies_started': http['body_sends_started'],
                  'bodies_returned': http['body_sends_returned'], 'endpoint_receipts': len(server['requests']),
                  'usage': usage, 'usage_status': status, 'priced_usage_ceiling_micro_usd': estimate,
                  'live_model_calls': 1 if live and http['body_sends_returned'] else 0,
                  'live_model_cost_usd': None if not live else (None if estimate is None else estimate/1e6),
                  'scope': ('one authorized provider request; cost is the priced ceiling of reported usage, not a bill'
                            if live else 'rehearsal against a local canned receiver; no live call, no cost')}
    r6.write_json(run/'accounting.json', accounting)
    return proposed, error, receipt, accounting


def execute(run, task, mode, packages, credential_file):
    if mode not in MODES: raise ValueError('Unknown mode')
    if task.id not in admission.verify()['controls']: raise ValueError('Task outside frozen controls')
    tools = setup(run, task, packages)
    c = contract.config(); nonce = credential.nonce()
    if mode == 'live':
        contract.live_permitted(c)
        if credential_file is None: raise ValueError('live mode requires --credential-file')
    shutil.copytree(contract.SOURCES, run/'pricing-origin')
    r6.write_json(run/'credential-canary.json', credential.record(nonce))
    policy = {'name': contract.NAME, 'mode': mode, 'task_id': task.id, 'config_sha256': r6.sha(contract.CONFIG),
              'source_lock_sha256': r6.sha(contract.LOCK), 'manifest_sha256': r6.sha(task.path/'manifest.json')}
    r6.write_json(run/'search-policy.json', policy)
    events.append(run, 'episode', 'episode_started', {'policy_sha256': r6.sha(run/'search-policy.json'),
        'challenge_sha256': tools['expected']['challenge_sha256'], 'nonce': nonce, 'mode': mode}, task_id=task.id)
    request = prepare(run, task, tools)
    proposer = c['attribution']['witness_proposer'] if mode == 'live' else 'canned_provider_response'
    events.append(run, 'proposal', 'recovery_started', {'route': contract.NAME, 'proposer': proposer})
    response, error, receipt, accounting = invoke(run, tools, mode, nonce, credential_file)
    verdict = None
    if error is None:
        try:
            packet, report, reports, delta, solution_hash = consumer.consume(run, task, tools, response)
            verdict = {'schema_version': 'r6-live-pilot-proof-1', 'task_id': task.id, 'search_policy': contract.NAME,
                'mode': mode, 'manifest_sha256': r6.sha(task.path/'manifest.json'),
                'challenge_sha256': tools['expected']['challenge_sha256'], 'request_sha256': gate.sha(request),
                'solution_sha256': solution_hash, 'final_validation': reports, 'axiom_delta': delta,
                'certificate_validation': report, 'witness_proposer': proposer,
                'certificate_assembler': 'sdk_proposal_assembler_v1', 'certificate_verified': True,
                'certificate_consumed': True, 'derivation_replayed': False, 'residual_closer': 'omega',
                'proof_replayed': True, 'trust_tier': 1, 'local_obligation_closed': True,
                'whole_declaration_validated': True}
            r6.write_json(run/'verdict.json', verdict)
            events.append(run, 'episode', 'proof_validated', {'verdict_sha256': r6.sha(run/'verdict.json'),
                'proof_accepted': True, 'solution_sha256': solution_hash})
        except provider_payload.Failure as failure:
            error = budget.previous.Failure(failure.category, 'certificate_verification', str(failure))
    summary = {'schema_version': 'r6-live-pilot-summary-1', 'task_id': task.id, 'mode': mode,
               'search_policy': contract.NAME, 'proof_accepted': verdict is not None,
               'credential_receipt_accepted': receipt['exact_receipt'],
               'failure_category': error.category if error else None, 'failure_phase': error.phase if error else None,
               'failure_stage': ('certificate-check' if error and error.category == 'certificate_verification'
                                 else 'proposal-1' if error and (run/'stages/proposal-1').exists() else error.phase if error else None),
               'error': str(error) if error else None, 'accounting': accounting, 'scope': c['scope']}
    r6.write_json(run/'credential-summary.json', summary)
    accepted, scan, final = publication_driver.finalize(run, credential.derive(nonce), nonce, summary)
    return {'accepted': accepted, 'mode': mode, 'proof_accepted': verdict is not None,
            'failure_category': summary['failure_category'], 'credential_receipt_accepted': receipt['exact_receipt'],
            'publication_accepted': scan['accepted'] and final['report_clean'], 'accounting': accounting}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode', choices=MODES, required=True)
    parser.add_argument('--task', choices=('verinf-d1-70',), default='verinf-d1-70')
    parser.add_argument('--run-dir', type=Path, required=True)
    parser.add_argument('--credential-file', type=Path)
    args = parser.parse_args()
    run = args.run_dir.resolve(); run.mkdir(parents=True, exist_ok=False)
    result = execute(run, r6.get_task(args.task), args.mode, r6.ROOT.parents[1]/'lean-bridge/.lake/packages',
                     None if args.credential_file is None else args.credential_file.resolve())
    print(json.dumps(result, indent=1, default=str))


if __name__ == '__main__':
    main()
