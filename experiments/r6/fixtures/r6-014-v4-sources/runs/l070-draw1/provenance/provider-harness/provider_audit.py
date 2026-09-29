"""Audit the canned transport separately from association and proof validity.

This validates retained observations and their consistency, not execution
attestation. Frozen task, policy and source locks supply the acceptance rules.
"""
from pathlib import Path

import admission
import provider_contract as contract
import provider_payload as wire
import provider_http
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
    if not condition: raise ValueError('Provider audit: '+message)


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
                      ('proposal', 'request_reserved')]
        order += [(stage, 'stage_started'), (stage, 'stage_finished')]
        if stage == 'proposal-1':
            order += [('proposal', 'http_observed'), ('proposal', 'transport_validated')]
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
    r6.jsonschema.validate(verdict, r6.read_json(r6.ROOT/'schema/provider-verdict.schema.json'))
    cohort = admission.verify()
    require(task.id in cohort['controls'] and task.id in contract.FIXTURES, 'task is outside frozen cohort')
    require(policy['case'] in {'valid', 'alternate_encoding'}, 'accepted episode uses a negative canned case')
    same(policy, {**config, 'task_id': task.id, 'task_manifest_sha256': r6.sha(task.path/'manifest.json'),
        'contract_sha256': r6.sha(contract.CONFIG), 'case': policy['case'], 'sdk_base_commit': instrument.BASE}, 'frozen envelope policy changed')
    binaries, roles, runtime = check_provenance(path, read)
    same(receipt('episode', 'episode_started'), {
        'task_manifest_sha256': r6.sha(task.path/'manifest.json'), 'search_policy_sha256': r6.sha(path('search-policy.json')),
        'challenge_sha256': expected['challenge_sha256']}, 'admission binding')
    require(verdict['task_id'] == task.id and verdict['manifest_sha256'] == r6.sha(task.path/'manifest.json')
        and verdict['challenge_sha256'] == expected['challenge_sha256'], 'verdict challenge binding')

    context = read('stages/preparation/output/context.json')
    same(context, r6.read_json(task.path/'context/local-context.json'), 'preparation context differs')
    same(context, read('stages/reconstruct/output/context.json'), 'reconstructed context differs')
    wire.old.context(context, read('sanitized-context.json'))
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
    same(read('messages.json'), args['input'], 'recorded messages differ')
    same(read('payload-audit.json'), {
        'request_sha256': wire.sha(request), 'prompt_sha256': r6.sha(path('prompt.txt')),
        'sanitized_context_sha256': r6.sha(path('sanitized-context.json')),
        'context_projection_is_model_visible': False, 'source_context_sha256': r6.sha(task.path/'context/local-context.json'),
        'let_facts_preserved': [r['name'] for r in context['telescope'] if r['kind'] == 'let'],
        'reifier_omissions': reified['skipped_locals'], 'farkas_omissions': prepared['farkas_omissions']}, 'payload audit mismatch')
    same(receipt('payload', 'payload_validated'), {'payload_audit_sha256': r6.sha(path('payload-audit.json')),
        'request_sha256': wire.sha(request), 'prompt_sha256': r6.sha(path('prompt.txt')),
        'client_arguments_sha256': r6.sha(path('client-arguments.json')), 'messages_sha256': r6.sha(path('messages.json'))}, 'payload receipt mismatch')

    response, raw, transport, accounting, transport_error = check_transport(path, read, receipt, task, policy, request)
    if transport_error: raise transport_error
    same(response, read('validated-response.json'), 'validated response changed')
    same(verdict['transport_validation'], transport, 'verdict transport checks differ')
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
        'evidence_receipt_claim': 'local HTTP fixture and proof checks; no remote receipt, compilation or inference attestation'}
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
            check_command(spec, runtime, roles, policy['case'])
    same(receipt('episode', 'episode_finished'), {'accepted': True, 'verdict_sha256': r6.sha(path('verdict.json'))}, 'terminal verdict')
    return verdict


def check_transport(path, read, receipt, task, policy, request):
    """Recompute diagnostics from observations, including rejected transports."""
    import provider_episode as harness
    root = 'stages/proposal-1/output/'
    http, server = read(root+'http.json'), read(root+'server.json')
    expected_files = {'http.json', 'server.json', 'outbound-body.json'} | {
        f'received-body-{i+1}.json' for i in range(len(server['requests']))}
    if http['response_sha256'] is not None: expected_files.add('provider-response.json')
    require({p.name for p in path(root+'http.json').parent.iterdir()} == expected_files,
            'HTTP observation file inventory differs; possible unreported capture')
    outbound = path(root+'outbound-body.json').read_bytes()
    require(http['request_bytes'] == len(outbound) and http['request_sha256'] == wire.sha(outbound), 'HTTP request body binding')
    require(http['mode'] == 'isolated_loopback_http_fixture' and http['method'] == 'POST'
        and http['request_path'] == '/v1/responses', 'HTTP method/path/mode differs')
    endpoint = http['endpoint']
    require(endpoint == {'scheme': 'http', 'host': '127.0.0.1', 'port': endpoint['port'], 'path': '/v1/responses'}
        and type(endpoint['port']) is int and 0 < endpoint['port'] < 65536, 'HTTP endpoint differs')
    require(type(http['elapsed_ns']) is int and http['elapsed_ns'] > 0, 'HTTP timing missing')
    require(all(type(http[k]) is int for k in ['connection_attempts','body_sends_started','body_sends_returned'])
        and http['connection_attempts'] == 1 and http['body_sends_started'] in [0,1] and http['body_sends_returned'] >= 0
        and http['body_sends_returned'] <= http['body_sends_started'] and len(server['requests']) <= 1, 'unreserved transmission/retry')
    require(outbound == provider_http.serialize(wire.arguments(request), policy['case']), 'declared HTTP serialization differs')
    captured = None
    if server['requests']:
        captured = path(root+'received-body-1.json').read_bytes()
        same(server['requests'], [{'method': 'POST', 'path': '/v1/responses', 'content_type': 'application/json',
            'declared_bytes': len(captured), 'observed_bytes': len(captured), 'complete': True,
            'body_sha256': wire.sha(captured), 'authorization_present': True}], 'server receipt differs')
    fixture = harness.canned_provider(task, request, policy['case'])
    same(read('canned-provider.json'), fixture, 'canned provider response differs')
    provider_raw = None
    if http['response_sha256'] is not None:
        provider_raw = path(root+'provider-response.json').read_bytes()
        require(http['response_sha256'] == wire.sha(provider_raw) and http['response_bytes'] == len(provider_raw), 'HTTP response body binding')
        require(provider_raw == fixture['body'].encode(), 'fixture/server response differs')
        require(http['http_status'] == fixture['status'], 'HTTP status differs from canned endpoint')
        same(http['response_headers'], {'Content-Type':'application/json','Content-Length':str(len(fixture['body'].encode())),
            'x-request-id':'r6-local-canned-request'}, 'filtered HTTP response headers differ')
    response, raw, metadata, validation, error = wire.transport(outbound, captured, provider_raw, http, request)
    same(read('provider-metadata.json'), metadata, 'provider decode metadata differs')
    if raw is not None: require(path('response.json').read_bytes() == raw, 'extracted provider output differs')
    same(read('transport-validation.json'), validation, 'independently reconstructed transport diagnostics differ')
    same(receipt('proposal', 'transport_validated'), validation, 'transport diagnostic receipt differs')
    accounting = {'attempts_reserved': 1, 'client_connection_attempts': http['connection_attempts'],
        'body_sends_started': http['body_sends_started'], 'body_sends_returned': http['body_sends_returned'],
        'transmissions_observed': sum(r['complete'] is True for r in server['requests']),
        'reported_usage': (metadata or {}).get('usage', wire.usage({})), 'live_model_calls': 0, 'live_model_cost_usd': 0,
        'scope': 'local HTTP fixture; usage is synthetic or unreported, cost unknown; actual live calls/cost zero'}
    same(read('accounting.json'), accounting, 'accounting differs from HTTP observations')
    before_decode = {**accounting, 'reported_usage': wire.usage({})}
    same(receipt('proposal', 'http_observed'), {'http_sha256': r6.sha(path(root+'http.json')),
        'server_sha256': r6.sha(path(root+'server.json')), 'accounting': before_decode}, 'HTTP observation receipt differs')
    same(receipt('proposal', 'request_reserved'), {'attempt': 1, 'request_sha256': wire.sha(request),
        'prompt_sha256': r6.sha(path('prompt.txt')), 'client_arguments_sha256': r6.sha(path('client-arguments.json'))}, 'reservation receipt differs')
    if policy['case'] in {'valid', 'alternate_encoding'}:
        require(http['failure_category'] is None and http['http_status'] == 200 and http['response_complete'] is True
            and len(server['requests']) == http['body_sends_started'] == http['body_sends_returned'] == 1, 'successful HTTP record is incomplete')
    return response, raw, validation, accounting, error


def check_command(spec, runtime, roles, case):
    prefix = ['bwrap', '--unshare-all', '--die-with-parent', '--new-session', '--cap-drop', 'ALL',
        '--clearenv', '--setenv', 'PATH', '/no-programs', '--setenv', 'LEAN_ABORT_ON_PANIC', '1',
        '--symlink', 'usr/lib', '/lib', '--symlink', 'usr/lib64', '/lib64',
        '--proc', '/proc', '--dev', '/dev', '--tmpfs', '/tmp', '--dir', '/work', '--chdir', '/work']
    for item in runtime['libraries']: prefix += ['--ro-bind', item['host'], item['guest']]
    original, c = Path(spec['run']), contract.config()
    require(original.is_absolute() and spec['records'] == str(original/'stages/proposal-1'), 'HTTP command record root')
    prefix += ['--ro-bind', roles['runtime_path'], runtime['stdlib'],
        '--ro-bind', roles['actor_source'], '/adapter.py',
        '--ro-bind', str(original/'client-arguments.json'), '/arguments.json',
        '--ro-bind', str(original/'canned-provider.json'), '/fixture.json',
        '--ro-bind', runtime['python'], '/runner/bin/program', '--bind', str(original/'stages/proposal-1/output'), '/out',
        '/runner/bin/program', '-I', '-S', '-B', '/adapter.py', '--arguments', '/arguments.json', '--fixture', '/fixture.json',
        '--case', case, '--out', '/out', '--timeout', str(c['http_timeout_seconds']),
        '--maximum-body', str(c['maximum_request_bytes']), '--maximum-response', str(c['maximum_provider_response_bytes'])]
    require(spec['argv'] == prefix and spec['capture_events'] is False, 'HTTP command permits extra inputs/capabilities or a different boundary')


def check_provenance(path, read):
    sources, patch = overlay.source_record()
    same(read('provenance/sources.json'), sources, 'source overlay provenance changed')
    require(path('provenance/instrumentation.patch').read_text() == patch, 'source overlay patch changed')
    for name, digest in overlay.source_lock().items():
        require(r6.sha(path('provenance/harness/'+name)) == digest, 'downstream harness source differs: '+name)
    for name in overlay.HARNESS_FILES:
        if name.startswith('policies/'):
            require(r6.sha(path('provenance/harness/'+name)) == r6.sha(r6.ROOT/name), 'downstream frozen policy differs: '+name)
    for section, module, extras in [('envelope-harness', contract.previous, []), ('provider-harness', contract, [contract.RUNTIME])]:
        for name, digest in module.source_lock().items():
            require(r6.sha(path('provenance/'+section+'/'+name)) == digest, 'retained harness source differs: '+section+'/'+name)
        for source in [module.CONFIG, module.LOCK, *extras]:
            require(r6.sha(path('provenance/'+section+'/'+str(source.relative_to(r6.ROOT)))) == r6.sha(source), 'retained policy lock differs')
    binaries, roles = read('provenance/binaries.json'), read('provenance/roles.json')
    runtime = read('provenance/python-runtime.json')
    same(runtime, r6.read_json(contract.RUNTIME), 'pinned runtime inventory differs')
    require(len(binaries) == 15 and all(isinstance(k, str) and k.startswith('/') and isinstance(v, str) and len(v) == 64
        for k, v in binaries.items()), 'binary inventory')
    suffixes = {'unused_legacy_responder': '/proposal-instrumented/fixture', 'assembler': '/validate/proposal_driver.exe',
        'verifier': '/validate/verify_certificate.exe', 'checker': '/r6-replay'}
    require(set(roles) == set(suffixes)|{'python', 'runtime_path', 'actor_source', 'downstream_setup'}, 'binary role inventory')
    for role, suffix in suffixes.items():
        require(roles[role] in binaries and roles[role].endswith(suffix), 'binary role differs: '+role)
    require(roles['python'] == runtime['python'] and binaries[roles['python']] == runtime['python_sha256'], 'Python binary binding')
    require(Path(roles['runtime_path']).is_absolute() and '..' not in Path(roles['runtime_path']).parts
        and roles['runtime_path'].endswith('/experiments/r6/.cache/provider-runtime/'+r6.sha(contract.RUNTIME)+'/stdlib'), 'filtered runtime location')
    require(Path(roles['actor_source']).is_absolute() and '..' not in Path(roles['actor_source']).parts
        and roles['actor_source'].endswith('/experiments/r6/provider_http.py'), 'HTTP actor source location')
    require(roles['downstream_setup'] == 'frozen proposal_episode.setup; legacy request policy not executed', 'downstream setup scope')
    return binaries, roles, runtime


def audit_failure(run, task):
    """Audit a rejected episode's recorded boundary, without a proof-success claim."""
    import provider_episode as harness
    run = Path(run)
    require((run/'failure.json').exists() and not (run/'seal.json').exists() and not (run/'verdict.json').exists(), 'failed-episode terminal state')
    seal = r6.read_json(run/'failure-seal.json')
    require(seal['schema_version']=='r6-failure-seal-1' and seal['accepted'] is False, 'failure seal scope')
    def path(name):
        p=run/name
        require(name in seal['retained_sha256'] and p.resolve().is_relative_to(run.resolve()), 'artifact not retained: '+name)
        require(r6.sha(p)==seal['retained_sha256'][name], 'failure artifact hash changed: '+name)
        return p
    def read(name): return r6.read_json(path(name))
    for name in seal['retained_sha256']: path(name)
    rows=episode.observations(run)
    require(len(rows)==seal['event_count'] and rows[-1]['event_hash']==seal['last_event_hash'], 'failure receipt seal differs')
    require(all(r['task_id']==task.id for r in rows) and not any(r['source']=='child_report' for r in rows), 'failure task or reconstruction boundary')
    def receipt(stage,event):
        selected=[r['payload'] for r in rows if r['source']=='supervisor' and r['stage']==stage and r['event']==event]
        require(len(selected)==1,'expected one receipt: '+stage+'/'+event)
        return selected[0]
    failed=read('failure.json'); policy=read('search-policy.json'); config=contract.config()
    same(rows[-1]['payload'],failed,'failure marker/receipt differs')
    require(rows[-1]['event']=='episode_failed' and failed['accepted'] is False, 'missing terminal failure')
    require(policy['case'] in set(harness.CASES)-{'valid','alternate_encoding'},'not a declared negative control')
    same(policy,{**config,'task_id':task.id,'task_manifest_sha256':r6.sha(task.path/'manifest.json'),
        'contract_sha256':r6.sha(contract.CONFIG),'case':policy['case'],'sdk_base_commit':instrument.BASE},'frozen provider policy changed')
    _, expected=r6.frozen_task(task)
    same(receipt('episode','episode_started'),{'task_manifest_sha256':r6.sha(task.path/'manifest.json'),
        'search_policy_sha256':r6.sha(path('search-policy.json')),'challenge_sha256':expected['challenge_sha256']},'failure admission binding')
    binaries, roles, runtime=check_provenance(path,read)
    prepared=read('prepared.json')
    same(prepared,read('stages/pipeline-prepare/output/prepared.json'),'failed preparation output differs')
    same(prepared['input_ir'],read('stages/preparation/output/reification.json')['ir'],'failed reification binding')
    context=read('stages/preparation/output/context.json')
    same(context,r6.read_json(task.path/'context/local-context.json'),'failed preparation context differs')
    wire.old.context(context,read('sanitized-context.json'))
    request=wire.request(task,prepared)
    require(path('request.json').read_bytes()==request and path('prompt.txt').read_bytes()==contract.PROMPT.read_bytes(),'failure prompt/request differs')
    same(read('client-arguments.json'),wire.arguments(request),'failure client arguments differ')
    response, raw, validation, accounting, error=check_transport(path,read,receipt,task,policy,request)
    stages=list(STAGES[:4])
    order=[('episode','episode_started')]
    for stage in stages:
        if stage=='proposal-1': order += [('payload','payload_validated'),('proposal','recovery_started'),('proposal','request_reserved')]
        order += [(stage,'stage_started'),(stage,'stage_finished')]
    order += [('proposal','http_observed'),('proposal','transport_validated')]
    if error is None and policy['case']=='exhausted_budget':
        order.append(('proposal','request_budget_exhausted'))
        same(receipt('proposal','request_budget_exhausted'),accounting,'budget exhaustion receipt differs')
        error=wire.Failure('request_budget_exhaustion','proposal','Frozen transmission budget exhausted')
    elif error is None and policy['case']=='invalid_witness':
        stages += ['assembly','certificate-check']
        order += [('assembly','stage_started'),('assembly','stage_finished'),('assembly','certificate_assembled'),
            ('certificate-check','stage_started'),('certificate-check','stage_finished'),
            ('certificate-check','independent_certificate_verdict'),('proposal','recovery_finished')]
        report=read('certificate-verdict.json')
        require(report['accepted'] is False and report['stage']=='certificate_verification'
            and report['reason']['kind']=='farkas_not_contradictory','wrong invalid-witness boundary')
        same(report,receipt('certificate-check','independent_certificate_verdict'),'failed certificate receipt differs')
        error=wire.Failure('certificate_verification','certificate-check','Farkas witness was not verified',report)
    require(error is not None,'negative transport was accepted')
    same(failed,{'accepted':False,'task_id':task.id,'search_policy':contract.NAME,'failure_stage':error.stage,
        'failure_phase':error.phase,'failure_category':error.category,'error':str(error),'evidence':error.evidence,
        'process':None,'causal_attribution':'unassigned; observed boundary only'},'failure diagnostic differs from retained bytes')
    order.append(('episode','episode_failed'))
    require([(r['stage'],r['event']) for r in rows if r['source']=='supervisor']==order,'failed supervisor receipts missing/extra/reordered')
    for stage in stages:
        stats=read(f'stages/{stage}/{stage}.process.json')
        same(stats,receipt(stage,'stage_finished'),'failure stage receipt differs')
        require(stats['resource_exhausted'] is None and stats.get('monitor_error') is None
            and stats.get('observation_error') is None and stats['workload_empty_after_cleanup'] is True,'unhealthy failure stage')
        require((stats['exit_code']!=0)==(stage=='certificate-check'),'unexpected process rejection boundary')
    spec=read('stages/proposal-1/command.json')
    check_command(spec,runtime,roles,policy['case'])
    for key in ['wall_seconds','cpu_seconds','memory_bytes','output_bytes']:
        require(spec[key]==config['request_'+key],'failed request budget differs')
    return {'accepted':False,'audit_accepted':True,'failure_category':error.category,'failure_stage':error.stage,
        'failure_phase':error.phase,'transport_validation':validation,'accounting':accounting,
        'scope':'recorded rejection boundary; no proof-success or execution-attestation claim'}
