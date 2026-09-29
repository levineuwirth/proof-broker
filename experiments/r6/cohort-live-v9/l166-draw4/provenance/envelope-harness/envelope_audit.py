"""Audit the canned transport separately from association and proof validity.

This validates retained observations and their consistency, not execution
attestation. Frozen task, policy and source locks supply the acceptance rules.
"""
from pathlib import Path

import admission
import envelope_contract as contract
import envelope_payload as wire
import envelope_proof_audit
import episode
import events
import instrument
import proposal_instrument as overlay
import run as r6
from supervise import resource_violations

STAGES = ('preparation-build', 'preparation', 'pipeline-prepare', 'proposal-1', 'assembly',
          'certificate-check', 'capture-build', 'reconstruct', 'export', 'validation-local', 'validation-whole')


def require(condition, message):
    if not condition: raise ValueError('Envelope audit: '+message)


def same(a, b, message):
    require(events.canonical(a) == events.canonical(b), message)


def audit(run, task):
    run = Path(run)
    require(not (run/'failure.json').exists(), 'episode has a failure marker')
    seal = r6.read_json(run/'seal.json')
    def path(name):
        p = run/name
        require(name in seal['retained_sha256'] and p.resolve().is_relative_to(run.resolve()), 'artifact not retained: '+name)
        return p
    def read(name): return r6.read_json(path(name))
    for name, digest in seal['retained_sha256'].items():
        require(r6.sha(path(name)) == digest, 'sealed artifact changed: '+name)
    rows = episode.observations(run)
    require(len(rows) == seal['event_count'] and rows[-1]['event_hash'] == seal['last_event_hash'], 'receipt seal mismatch')
    require(all(row['task_id'] == task.id for row in rows), 'task identity mismatch')
    def receipt(stage, event):
        matches = [r['payload'] for r in rows if r['source'] == 'supervisor' and r['stage'] == stage and r['event'] == event]
        require(len(matches) == 1, f'expected one receipt: {stage}/{event}')
        return matches[0]
    order = [('episode', 'episode_started')]
    for stage in STAGES:
        if stage == 'proposal-1':
            order += [('payload', 'payload_validated'), ('proposal', 'recovery_started'),
                      ('proposal', 'request_reserved'), ('proposal', 'envelope_serialized')]
        order += [(stage, 'stage_started'), (stage, 'stage_finished')]
        if stage == 'proposal-1':
            order += [('proposal', 'transmission_observed'), ('proposal', 'response_received'), ('proposal', 'transport_validated')]
        if stage == 'assembly': order += [('assembly', 'certificate_assembled')]
        if stage == 'certificate-check':
            order += [('certificate-check', 'independent_certificate_verdict'), ('proposal', 'recovery_finished')]
        if stage == 'reconstruct': order += [('reconstruct', 'context_validated')]
        if stage.startswith('validation-'): order += [(stage, 'kernel_verdict')]
    order += [('episode', 'episode_finished')]
    require([(r['stage'], r['event']) for r in rows if r['source'] == 'supervisor'] == order,
            'missing, extra, or reordered supervisor receipts')

    _, expected = r6.frozen_task(task)
    config, policy, verdict = contract.config(), read('search-policy.json'), read('verdict.json')
    r6.jsonschema.validate(verdict, r6.read_json(r6.ROOT/'schema/envelope-verdict.schema.json'))
    cohort = admission.verify()
    require(task.id in cohort['controls'] and task.id in contract.FIXTURES, 'task is outside frozen cohort')
    require(policy['case'] in {'valid', 'alternate_encoding'}, 'accepted episode uses a negative canned case')
    same(policy, {**config, 'task_id': task.id, 'task_manifest_sha256': r6.sha(task.path/'manifest.json'),
        'contract_sha256': r6.sha(contract.CONFIG), 'case': policy['case'], 'sdk_base_commit': instrument.BASE}, 'frozen envelope policy changed')
    sources, patch = overlay.source_record()
    same(read('provenance/sources.json'), sources, 'source overlay provenance changed')
    require(path('provenance/instrumentation.patch').read_text() == patch, 'source overlay patch changed')
    for name, digest in overlay.source_lock().items():
        require(r6.sha(path('provenance/harness/'+name)) == digest, 'downstream harness source differs: '+name)
    for name in overlay.HARNESS_FILES:
        if name.startswith('policies/'):
            require(r6.sha(path('provenance/harness/'+name)) == r6.sha(r6.ROOT/name), 'downstream frozen policy differs: '+name)
    for name, digest in contract.source_lock().items():
        require(r6.sha(path('provenance/envelope-harness/'+name)) == digest, 'envelope harness source differs: '+name)
    for source in [contract.CONFIG, contract.LOCK]:
        require(r6.sha(path('provenance/envelope-harness/'+str(source.relative_to(r6.ROOT)))) == r6.sha(source),
                'envelope policy/source lock snapshot differs')
    binaries, roles = read('provenance/binaries.json'), read('provenance/roles.json')
    require(len(binaries) == 15 and all(isinstance(k, str) and k.startswith('/')
        and isinstance(v, str) and len(v) == 64 for k, v in binaries.items()), 'binary inventory')
    suffixes = {'receiver': '/canned-envelope/envelope-receiver', 'unused_legacy_responder': '/proposal-instrumented/fixture',
        'assembler': '/validate/proposal_driver.exe', 'verifier': '/validate/verify_certificate.exe', 'checker': '/r6-replay'}
    require(set(roles) == set(suffixes)|{'downstream_setup'}, 'binary role inventory')
    for role, suffix in suffixes.items():
        require(roles[role] in binaries and roles[role].endswith(suffix), 'binary role differs: '+role)
    require(roles['downstream_setup'] == 'frozen proposal_episode.setup; legacy request policy not executed', 'downstream setup scope')
    same(receipt('episode', 'episode_started'), {
        'task_manifest_sha256': r6.sha(task.path/'manifest.json'), 'search_policy_sha256': r6.sha(path('search-policy.json')),
        'challenge_sha256': expected['challenge_sha256']}, 'admission binding')
    require(verdict['task_id'] == task.id and verdict['manifest_sha256'] == r6.sha(task.path/'manifest.json')
        and verdict['challenge_sha256'] == expected['challenge_sha256'], 'verdict challenge binding')

    context = read('stages/preparation/output/context.json')
    same(context, r6.read_json(task.path/'context/local-context.json'), 'preparation context differs')
    same(context, read('stages/reconstruct/output/context.json'), 'reconstructed context differs')
    wire.context(context, read('sanitized-context.json'))
    prepared = read('prepared.json')
    same(prepared, read('stages/pipeline-prepare/output/prepared.json'), 'prepared pipeline output differs')
    reified = read('stages/preparation/output/reification.json')
    same(prepared['input_ir'], reified['ir'], 'prepared input differs from reification')
    same(prepared['input_ir'], read('input-ir.json'), 'preparation input binding')
    request = wire.request(task, prepared)
    require(path('request.json').read_bytes() == request, 'request differs from allowed arithmetic input')
    require(path('request.sha256').read_text() == wire.sha(request)+'  request.json\n', 'request hash file')
    require(path('prompt.txt').read_bytes() == contract.PROMPT.read_bytes(), 'frozen semantic prompt changed')
    args = wire.arguments(request)
    same(read('client-arguments.json'), args, 'client arguments differ from frozen messages')
    same(read('messages.json'), args['messages'], 'recorded messages differ')
    same(read('payload-audit.json'), {
        'request_sha256': wire.sha(request), 'prompt_sha256': r6.sha(path('prompt.txt')),
        'sanitized_context_sha256': r6.sha(path('sanitized-context.json')),
        'context_projection_is_model_visible': False, 'source_context_sha256': r6.sha(task.path/'context/local-context.json'),
        'let_facts_preserved': [r['name'] for r in context['telescope'] if r['kind'] == 'let'],
        'reifier_omissions': reified['skipped_locals'], 'farkas_omissions': prepared['farkas_omissions']}, 'payload audit mismatch')
    same(receipt('payload', 'payload_validated'), {'payload_audit_sha256': r6.sha(path('payload-audit.json')),
        'request_sha256': wire.sha(request), 'prompt_sha256': r6.sha(path('prompt.txt')),
        'client_arguments_sha256': r6.sha(path('client-arguments.json')), 'messages_sha256': r6.sha(path('messages.json'))}, 'payload receipt mismatch')

    outbound, captured = path('serialized-envelope.json').read_bytes(), path('stages/proposal-1/output/received-envelope.json').read_bytes()
    require(captured == outbound, 'receiver capture differs from serialized output')
    envelope = wire.audit_envelope(captured, request)
    require(outbound == wire.serialize(args, variant='alternate' if policy['case'] == 'alternate_encoding' else 'standard'),
            'serialized bytes differ from declared serialization')
    same(read('stages/proposal-1/output/transmission.json'), {'completed': True, 'bytes': len(captured)}, 'transmission receipt mismatch')
    same(receipt('proposal', 'request_reserved'), {'attempt': 1, 'request_sha256': wire.sha(request),
        'prompt_sha256': r6.sha(path('prompt.txt')), 'client_arguments_sha256': r6.sha(path('client-arguments.json'))}, 'reservation receipt mismatch')
    same(receipt('proposal', 'envelope_serialized'), {'serializer': config['serializer'],
        'serialized_envelope_sha256': wire.sha(outbound), 'bytes': len(outbound)}, 'serializer receipt mismatch')
    same(receipt('proposal', 'transmission_observed'), {'attempt': 1, 'captured_envelope_sha256': wire.sha(captured),
        'bytes': len(captured)}, 'transmission event mismatch')
    raw = path('response.json').read_bytes()
    require(raw == path('stages/proposal-1/proposal-1.stdout').read_bytes() == path('canned-response.json').read_bytes(),
            'raw response differs from canned transport')
    response = wire.response(raw, request)
    first, coefficient = contract.FIXTURES[task.id]
    same(response['witness'], {'coefficients': [{'hypothesis': first, 'coefficient': coefficient},
        {'hypothesis': 'neg_goal', 'coefficient': '3'}]}, 'canned control witness differs')
    same(response, read('validated-response.json'), 'validated response changed')
    same(receipt('proposal', 'response_received'), {'attempt': 1, 'response_sha256': wire.sha(raw)}, 'response receipt mismatch')
    transport = {'response_request_binding': wire.echo(raw, request), 'outbound_envelope': envelope,
        'response_validated': True, 'response_failure_category': None}
    for value in [read('transport-validation.json'), receipt('proposal', 'transport_validated'), verdict['transport_validation']]:
        same(value, transport, 'independent transport checks differ')
    accounting = {'attempts_reserved': 1, 'transmissions_observed': 1, 'reported_usage': wire.usage(),
        'live_model_calls': 0, 'live_model_cost_usd': 0,
        'scope': 'local canned transport; absent simulated usage is unknown, actual live calls/cost are zero'}
    same(read('accounting.json'), accounting, 'accounting differs from observed attempt/usage')
    same(verdict['accounting'], accounting, 'verdict accounting differs')

    packet = read('evidence.json')
    same(packet, read('stages/assembly/output/evidence.json'), 'assembled packet changed')
    require(all(packet[k] == prepared[k] for k in ['input_ir', 'final_ir', 'trace']), 'assembly changed the prepared problem')
    cert = packet['certificate']
    same(cert['payload']['witness_data'], response['witness'], 'proposed and assembled witnesses differ')
    same(cert['backend'], {'name': config['certificate_backend'], 'version': '1', 'config_hash': 'sha256:'+r6.sha(contract.CONFIG)},
        'certificate envelope policy')
    require(type(cert['tier']) is int and cert['tier'] == 1 and cert['format'] == 'farkas', 'certificate tier/format')
    same(receipt('assembly', 'certificate_assembled'), {'certificate_sha256': events.digest(cert),
        'witness_proposer': config['witness_proposer'], 'certificate_assembler': config['certificate_assembler'],
        'response_sha256': r6.sha(path('validated-response.json'))}, 'proposer/assembler receipt mismatch')
    report = read('certificate-verdict.json')
    require(report.get('accepted') is True and report.get('stage') == 'certificate_verification'
        and report.get('reason') == {'kind': 'verified_farkas'}
        and report.get('certificate_hash') == 'sha256:'+events.digest(cert), 'independent certificate verification')
    same(report, verdict['certificate_validation'], 'certificate report/verdict mismatch')
    same(report, receipt('certificate-check', 'independent_certificate_verdict'), 'certificate report/receipt mismatch')
    same(receipt('proposal', 'recovery_started'), {'route': config['name'], 'proposer': config['witness_proposer']}, 'recovery start attribution')
    same(receipt('proposal', 'recovery_finished'), {'route': config['name'], 'ok': True, 'witness': response['witness'],
        'reason': report['reason'], 'proposer': config['witness_proposer']}, 'recovery finish attribution')
    envelope_proof_audit.audit(task, packet, verdict, rows, path, read, receipt)
    flags = {'accepted': True, 'search_succeeded': True, 'certificate_type': 'farkas', 'trust_tier': 1,
        'certificate_verified': True, 'certificate_consumed': True, 'derivation_replayed': False,
        'residual_closer': 'omega', 'proof_replayed': True, 'local_obligation_closed': True, 'whole_declaration_validated': True,
        'witness_proposer': config['witness_proposer'], 'certificate_assembler': config['certificate_assembler'],
        'recovery_route': config['name'], 'local_proof_required_reference': episode.FARKAS_HELPER,
        'failure_category': None, 'failure_phase': None, 'prompt_sha256': r6.sha(path('prompt.txt')),
        'request_sha256': wire.sha(request), 'response_sha256': wire.sha(raw),
        'evidence_receipt_claim': 'trusted local canned transport and proof checks; no provider SDK or inference attestation'}
    for key, value in flags.items(): same(verdict[key], value, 'verdict evidence claim differs: '+key)
    require(set(verdict['resources']) == set(STAGES), 'stage resource inventory')
    for stage in STAGES:
        spec, stats = read(f'stages/{stage}/command.json'), read(f'stages/{stage}/{stage}.process.json')
        same(stats, verdict['resources'][stage], 'stage resource/verdict mismatch')
        same(stats, receipt(stage, 'stage_finished'), 'stage resource/receipt mismatch')
        require(stats['exit_code'] == 0 and stats['resource_exhausted'] is None and stats.get('monitor_error') is None
            and stats.get('observation_error') is None and stats.get('workload_empty_after_cleanup') is True, 'unhealthy stage')
        require(not resource_violations(spec, stats.get('execution_wall_seconds', stats['wall_seconds']),
            stats['cgroup_cpu_usec'], stats['memory_events'], stats['output_bytes']), 'stage exceeded budget')
        begun = receipt(stage, 'stage_started')
        require(begun['command_file'] == f'stages/{stage}/command.json' and spec['stage'] == stage, 'stage command binding')
        for flag, key in [('wall_limit_seconds', 'wall_seconds'), ('cpu_limit_seconds', 'cpu_seconds'), ('memory_limit_bytes', 'memory_bytes')]:
            require(begun[flag] == spec[key], 'stage limit receipt mismatch')
        if stage == 'proposal-1':
            for key in ['wall_seconds', 'cpu_seconds', 'memory_bytes', 'output_bytes']:
                require(spec[key] == config['request_'+key], 'request budget differs from contract')
            check_receiver_command(spec, read('provenance/receiver-runtime.json'), binaries, roles['receiver'])
    same(receipt('episode', 'episode_finished'), {'accepted': True, 'verdict_sha256': r6.sha(path('verdict.json'))}, 'terminal verdict')
    return verdict


def check_receiver_command(spec, libraries, binaries, receiver):
    """Require the whole isolated command; no arithmetic file beyond the wire body.

    Paths describe the recorded host. A retained-only audit need not recreate
    them and does not attest to the execution that produced the record.
    """
    prefix = ['bwrap', '--unshare-all', '--die-with-parent', '--new-session', '--cap-drop', 'ALL',
        '--clearenv', '--setenv', 'PATH', '/no-programs', '--setenv', 'LEAN_ABORT_ON_PANIC', '1',
        '--symlink', 'usr/lib', '/lib', '--symlink', 'usr/lib64', '/lib64',
        '--proc', '/proc', '--dev', '/dev', '--tmpfs', '/tmp', '--dir', '/work', '--chdir', '/work']
    guests = set()
    for item in libraries:
        require(set(item) == {'host', 'guest', 'sha256'} and len(item['sha256']) == 64, 'receiver library provenance')
        require(item['guest'].startswith(('/usr/lib/', '/usr/lib64/', '/lib/', '/lib64/'))
            and item['host'].startswith(('/usr/lib/', '/usr/lib64/'))
            and '..' not in Path(item['guest']).parts and '..' not in Path(item['host']).parts
            and item['guest'] not in guests, 'receiver library mount')
        guests.add(item['guest'])
        prefix += ['--ro-bind', item['host'], item['guest']]
    require(bool(guests) and receiver in binaries, 'missing receiver binary/runtime provenance')
    original = Path(spec['run'])
    require(original.is_absolute() and spec['records'] == str(original/'stages/proposal-1'), 'transport command record root')
    prefix += ['--ro-bind', str(original/'serialized-envelope.json'), '/wire.json',
        '--ro-bind', str(original/'canned-response.json'), '/canned.json', '--ro-bind', receiver, '/runner/bin/program',
        '--bind', str(original/'stages/proposal-1/output'), '/out', '/runner/bin/program', 'normal']
    require(spec['argv'] == prefix and spec['capture_events'] is False,
        'receiver command permits extra inputs, capabilities, or a different envelope')
