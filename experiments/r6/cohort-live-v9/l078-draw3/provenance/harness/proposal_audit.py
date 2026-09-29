"""Policy-specific fixture receipt order and cross-artifact consistency.

The historical CVC4 audit is unchanged. This reader uses publication artifacts
and the frozen task; it does not trust an episode to choose its acceptance rules.
It checks saved observations, not an attestation of the host's computation.
"""
import copy
import difflib
import gzip
import hashlib
import json
from pathlib import Path

import episode
import admission
import events
import instrument
import payload
import proposal_instrument as overlay
import run as r6
from supervise import resource_violations

STAGES = ('preparation-build', 'preparation', 'pipeline-prepare', 'proposal-1', 'assembly',
          'certificate-check', 'capture-build', 'reconstruct', 'export', 'validation-local', 'validation-whole')


def require(condition, message):
    if not condition:
        raise ValueError('Proposal audit: '+message)


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
            order += [('payload', 'payload_validated'), ('proposal', 'recovery_started'), ('proposal', 'request_started')]
        order += [(stage, 'stage_started'), (stage, 'stage_finished')]
        if stage == 'proposal-1': order += [('proposal', 'response_received')]
        if stage == 'assembly': order += [('assembly', 'certificate_assembled')]
        if stage == 'certificate-check':
            order += [('certificate-check', 'independent_certificate_verdict'), ('proposal', 'recovery_finished')]
        if stage == 'reconstruct': order += [('reconstruct', 'context_validated')]
        if stage.startswith('validation-'): order += [(stage, 'kernel_verdict')]
    order += [('episode', 'episode_finished')]
    require([(r['stage'], r['event']) for r in rows if r['source'] == 'supervisor'] == order,
            'missing, extra, or reordered supervisor receipts')

    manifest, expected = r6.frozen_task(task)
    config, policy, verdict = r6.read_json(payload.CONTRACT), read('search-policy.json'), read('verdict.json')
    r6.jsonschema.validate(verdict, r6.read_json(r6.ROOT/'schema/proposal-episode.schema.json'))
    admission.verify()
    require(config['admission_sha256'] == r6.sha(admission.FROZEN), 'admission cohort hash changed')
    require(config['source_lock_sha256'] == r6.sha(overlay.SOURCE_LOCK), 'source lock hash changed')
    require(events.canonical(policy) == events.canonical({**config, 'task_id': task.id, 'parent_task_manifest_sha256': r6.sha(task.path/'manifest.json'),
                       'contract_sha256': r6.sha(payload.CONTRACT), 'sdk_base_commit': instrument.BASE,
                       'fixture_case': 'valid', 'preparation_closer': 'frozen_human_omega'}), 'frozen fixture policy changed')
    sources, patch = overlay.source_record()
    require(read('provenance/sources.json') == sources
            and path('provenance/instrumentation.patch').read_text() == patch, 'source/dispatch overlay provenance changed')
    for name, digest in overlay.source_lock().items():
        require(r6.sha(path('provenance/harness/'+name)) == digest, 'harness source differs: '+name)
    for name in overlay.HARNESS_FILES:
        if name.startswith('policies/'):
            require(r6.sha(path('provenance/harness/'+name)) == r6.sha(r6.ROOT/name), 'frozen policy differs: '+name)
    binaries = read('provenance/binaries.json')
    require(len(binaries) == 14 and all(isinstance(k, str) and k.startswith('/')
            and isinstance(v, str) and len(v) == 64 for k, v in binaries.items()), 'binary inventory')
    require(verdict['schema_version'] == 'r6-proposal-episode-1' and verdict['search_policy'] == config['name']
            and verdict['task_id'] == task.id, 'verdict identity')
    require(receipt('episode', 'episode_started') == {
        'task_manifest_sha256': r6.sha(task.path/'manifest.json'), 'search_policy_sha256': r6.sha(path('search-policy.json')),
        'challenge_sha256': expected['challenge_sha256']}, 'admission binding')
    require(verdict['manifest_sha256'] == r6.sha(task.path/'manifest.json')
            and verdict['challenge_sha256'] == expected['challenge_sha256'], 'verdict challenge binding')
    context = read('stages/preparation/output/context.json')
    require(context == r6.read_json(task.path/'context/local-context.json') == read('stages/reconstruct/output/context.json'),
            'captured context differs from frozen task')
    payload.validate_context(read('sanitized-context.json'), context)
    prepared = read('prepared.json')
    require(prepared == read('stages/pipeline-prepare/output/prepared.json'), 'prepared pipeline output differs')
    reified = read('stages/preparation/output/reification.json')
    require(prepared['input_ir'] == reified['ir'] == read('input-ir.json'), 'preparation input binding')
    request = payload.request(task, prepared)
    request_bytes = events.canonical(request)+b'\n'
    require(path('request.json').read_bytes() == request_bytes, 'model request differs from the allowed arithmetic inputs')
    require(path('request.sha256').read_text() == r6.sha(path('request.json'))+'  request.json\n', 'payload hash file')
    payload_audit = read('payload-audit.json')
    require(payload_audit == {'request_sha256': r6.sha(path('request.json')),
        'sanitized_context_sha256': r6.sha(path('sanitized-context.json')),
        'source_context_sha256': r6.sha(task.path/'context/local-context.json'),
        'context_projection_is_model_visible': False, 'context_policy': config['context_policy'],
        'let_facts_preserved': [r['name'] for r in context['telescope'] if r['kind'] == 'let'],
        'reifier_omissions': reified['skipped_locals'], 'farkas_omissions': prepared['farkas_omissions']}, 'payload audit mismatch')
    require(receipt('payload', 'payload_validated') == {'request_sha256': r6.sha(path('request.json')),
        'payload_audit_sha256': r6.sha(path('payload-audit.json'))}, 'payload receipt mismatch')
    raw = path('response.json').read_bytes()
    require(raw == path('stages/proposal-1/proposal-1.stdout').read_bytes(), 'raw response differs from transport')
    response = payload.response(raw, request_bytes)
    require(response == read('validated-response.json'), 'validated response changed')
    require(response['witness'] == read('fixture-witness.json'), 'fixture did not deliver its selected witness')
    require(receipt('proposal', 'request_started') == {'attempt': 1, 'request_sha256': r6.sha(path('request.json'))}
            and receipt('proposal', 'response_received') == {'attempt': 1, 'response_sha256': r6.sha(path('response.json'))},
            'request/response receipt binding')
    packet = read('evidence.json')
    require(packet == read('stages/assembly/output/evidence.json'), 'assembled packet changed')
    require(all(packet[k] == prepared[k] for k in ['input_ir', 'final_ir', 'trace']), 'assembly changed the prepared problem')
    cert = packet['certificate']
    require(cert['payload']['witness_data'] == response['witness'], 'proposed and assembled witnesses differ')
    require(cert['backend'] == {'name': 'r6_fixture_witness', 'version': '1', 'config_hash': 'sha256:'+r6.sha(payload.CONTRACT)}
            and cert['tier'] == 1 and cert['format'] == 'farkas', 'certificate envelope policy')
    require(receipt('assembly', 'certificate_assembled') == {'certificate_sha256': events.digest(cert),
        'witness_proposer': config['proposer'], 'certificate_assembler': config['certificate_assembler'],
        'response_sha256': r6.sha(path('validated-response.json'))}, 'proposer/assembler receipt mismatch')
    certificate_report = read('certificate-verdict.json')
    require(certificate_report.get('accepted') is True and certificate_report.get('stage') == 'certificate_verification'
            and certificate_report.get('reason') == {'kind': 'verified_farkas'}
            and certificate_report.get('certificate_hash') == 'sha256:'+events.digest(cert), 'independent certificate verification')
    require(certificate_report == verdict['certificate_validation'] == receipt('certificate-check', 'independent_certificate_verdict'),
            'certificate report/receipt mismatch')
    require(receipt('proposal', 'recovery_started') == {'route': config['name'], 'proposer': config['proposer']}
            and receipt('proposal', 'recovery_finished') == {'route': config['name'], 'ok': True, 'witness': response['witness'],
            'reason': certificate_report['reason'], 'proposer': config['proposer']}, 'proposal recovery attribution')

    child_names = ['reification_started', 'reification_finished', 'dispatch_started', 'dispatch_received',
                   'certificate_verification_started', 'certificate_verification_finished',
                   'reconstruction_started', 'residual_started', 'residual_finished', 'reconstruction_finished']
    children = [r for r in rows if r['source'] == 'child_report']
    require([r['event'] for r in children] == child_names, 'unexpected reconstruction observations or hidden search route')
    start = next(r['sequence'] for r in rows if r['stage'] == 'reconstruct' and r['event'] == 'stage_started')
    finish = next(r['sequence'] for r in rows if r['stage'] == 'reconstruct' and r['event'] == 'stage_finished')
    require(all(start < r['sequence'] < finish and r['stage'] == 'reconstruct'
                and r['payload']['component'] == 'lean_bridge' for r in children), 'child observation boundary')
    observed = {r['event']: r['payload']['data'] for r in children}
    actual_input = copy.deepcopy(observed['reification_finished']['ir'])
    actual_input['user_directives']['tier_preference'] = ['1', '2']
    require(actual_input == packet['input_ir'] == observed['dispatch_started']['ir'], 'fresh reification differs from proposal input')
    require(observed['dispatch_started']['manifests'] == [] and observed['dispatch_started']['prefer_higher_tier'] is False,
            'proposal delivery invoked solver dispatch')
    received = observed['dispatch_received']
    require(received['certificate'] == cert and received['final_ir'] == packet['final_ir']
            and received['trace'] == packet['trace'], 'reconstruction received different evidence')
    for name in ['certificate_verification_started', 'certificate_verification_finished', 'reconstruction_started', 'reconstruction_finished']:
        require(observed[name]['certificate'] == cert, 'certificate changed at '+name)
    require(observed['certificate_verification_finished']['ok'] is True
            and observed['certificate_verification_finished']['envelope_ok'] is True, 'bridge verifier did not accept')
    require(observed['reconstruction_finished'] == {'certificate': cert, 'closer': 'term_mode_nat',
        'certificate_consumed': True, 'derivation_replayed': False, 'residual_closer': 'omega'}, 'consumption path changed')
    require(receipt('reconstruct', 'context_validated') == {
        'captured_context_sha256': r6.sha(path('stages/reconstruct/output/context.json')),
        'frozen_context_sha256': r6.sha(task.path/'context/local-context.json')}, 'reconstruction context receipt')

    for directory, helper, preparation in [('preparation-input', 'PreparationCapture', True), ('input', 'ProposalCapture', False)]:
        pristine = (task.path/'Pristine.lean').read_text()
        source = r6.instrument(pristine, task).replace('import Capture\n', f'import {helper}\n').replace(
            'r6_capture_human', 'r6_prepare' if preparation else 'r6_capture_proposal')
        require(path(f'{directory}/Frozen.lean').read_text() == source
                and path(f'{directory}/{helper}.lean').read_text() == overlay.capture_source(task, preparation),
                'source differs from permitted extraction')
        require(path(f'{directory}/source.patch').read_text() == ''.join(difflib.unified_diff(
            pristine.splitlines(True), source.splitlines(True), fromfile='Pristine.lean', tofile='Frozen.lean')),
            'reported source modification differs')
    # Same independent declaration/type/reference/axiom requirements as R6-000.
    baseline = {t['name']: t for t in expected['targets']}
    delta = {}
    digest = hashlib.sha256()
    length = 0
    with gzip.open(path('solution.ndjson.gz'), 'rb') as f:
        while block := f.read(1024**2):
            length += len(block)
            require(length <= 256*1024**2, 'proof export exceeds budget')
            digest.update(block)
    require(digest.hexdigest() == verdict['solution_sha256'], 'proof hash mismatch')
    for kind, target, config_policy in [('local', task.local, episode.local_policy(task)),
                                       ('whole', task.whole, r6.policy([task.whole], True, task=task))]:
        require(read(f'validation-input/{kind}/policy.json') == config_policy, 'validation policy changed')
        with gzip.open(path(f'validation-{kind}.raw.json.gz'), 'rb') as f:
            raw_report = f.read(4*1024**2+1)
        require(len(raw_report) <= 4*1024**2, 'oversized replay report')
        report = json.loads(raw_report)
        require(report['accepted'] is True and report['stage'] == 'complete' and report['kernel_version'] == '4.32.2'
                and report['local_proof_binding_checked'] is True and report['checked_declarations'] > 0,
                'independent kernel/reference check failed')
        require(len(report['targets']) == 1 and report['targets'][0]['name'] == target, 'missing expected declaration')
        t = report['targets'][0]
        require(all(t[k] is True for k in ['declaration_exists', 'statement_and_dependencies_match', 'kernel_accepted']), 'target validation')
        t['type_sha256'] = hashlib.sha256(t.pop('type_repr').encode()).hexdigest()
        t['type_hash_format'] = 'Lean-4.32.2-reprStr-Expr-UTF8'
        require(t['type_sha256'] == baseline[target]['type_sha256'] and set(t['axioms']) <= set(r6.AXIOMS), 'frozen type/axiom policy')
        require(report == verdict['final_validation'][kind] == receipt('validation-'+kind, 'kernel_verdict'), 'replay report/receipt mismatch')
        delta[target] = {'added': sorted(set(t['axioms'])-set(baseline[target]['axioms'])),
                         'removed': sorted(set(baseline[target]['axioms'])-set(t['axioms']))}
    require(verdict['axiom_delta'] == delta, 'axiom delta mismatch')
    flags = {'accepted': True, 'search_succeeded': True, 'certificate_type': 'farkas', 'trust_tier': 1,
             'certificate_verified': True, 'certificate_consumed': True, 'derivation_replayed': False,
             'residual_closer': 'omega', 'proof_replayed': True, 'local_obligation_closed': True,
             'whole_declaration_validated': True, 'witness_proposer': config['proposer'],
             'certificate_assembler': config['certificate_assembler'], 'recovery_route': config['name'],
             'local_proof_required_reference': episode.FARKAS_HELPER, 'fixture_requests': 1,
             'model_calls': 0, 'model_tokens': 0, 'model_cost_usd': 0,
             'failure_category': None,
             'request_sha256': r6.sha(path('request.json')), 'response_sha256': r6.sha(path('response.json'))}
    require(all(events.canonical(verdict.get(k)) == events.canonical(v) for k, v in flags.items()), 'verdict evidence/producer claims')
    require(set(verdict['resources']) == set(STAGES), 'stage resource inventory')
    for stage in STAGES:
        spec, stats = read(f'stages/{stage}/command.json'), read(f'stages/{stage}/{stage}.process.json')
        require(stats == verdict['resources'][stage] == receipt(stage, 'stage_finished'), 'stage resource/receipt mismatch')
        require(stats['exit_code'] == 0 and stats['resource_exhausted'] is None and stats.get('monitor_error') is None
                and stats.get('observation_error') is None and stats.get('workload_empty_after_cleanup') is True, 'unhealthy stage')
        require(not resource_violations(spec, stats.get('execution_wall_seconds', stats['wall_seconds']),
                stats['cgroup_cpu_usec'], stats['memory_events'], stats['output_bytes']), 'stage exceeded budget')
        begun = receipt(stage, 'stage_started')
        require(begun['command_file'] == f'stages/{stage}/command.json' and spec['stage'] == stage, 'stage command binding')
        for flag, key in [('wall_limit_seconds', 'wall_seconds'), ('cpu_limit_seconds', 'cpu_seconds'), ('memory_limit_bytes', 'memory_bytes')]:
            require(begun[flag] == spec[key], 'stage limit receipt mismatch')
        if stage == 'proposal-1':
            for field in ['wall_seconds', 'cpu_seconds', 'memory_bytes', 'output_bytes']:
                require(spec[field] == config['request_'+field], 'request budget differs from contract')
            check_fixture_command(spec, read('provenance/fixture-runtime.json'), binaries, r6.sha(path('request.json')))
    require(receipt('episode', 'episode_finished') == {'accepted': True, 'verdict_sha256': r6.sha(path('verdict.json'))}, 'terminal verdict')
    return verdict


def check_fixture_command(spec, libraries, binaries, request_hash):
    """Match the complete isolated command, including mount sources and flags.

    Absolute host paths describe the recorded host. A retained-only copy need
    not recreate those paths; this audit does not re-execute the process.
    """
    prefix = ['bwrap', '--unshare-all', '--die-with-parent', '--new-session', '--cap-drop', 'ALL',
        '--clearenv', '--setenv', 'PATH', '/no-programs', '--setenv', 'LEAN_ABORT_ON_PANIC', '1',
        '--symlink', 'usr/lib', '/lib', '--symlink', 'usr/lib64', '/lib64',
        '--proc', '/proc', '--dev', '/dev', '--tmpfs', '/tmp', '--dir', '/work', '--chdir', '/work']
    guests = set()
    for item in libraries:
        require(set(item) == {'host', 'guest', 'sha256'} and len(item['sha256']) == 64, 'fixture library provenance')
        require(item['guest'].startswith(('/usr/lib/', '/usr/lib64/', '/lib/', '/lib64/'))
                and item['host'].startswith(('/usr/lib/', '/usr/lib64/'))
                and '..' not in Path(item['guest']).parts and '..' not in Path(item['host']).parts
                and item['guest'] not in guests, 'fixture library mount')
        guests.add(item['guest'])
        prefix += ['--ro-bind', item['host'], item['guest']]
    require(bool(guests), 'missing fixture runtime libraries')
    fixtures = [p for p in binaries if p.endswith('/proposal-instrumented/fixture')]
    require(len(fixtures) == 1, 'missing fixture binary provenance')
    original = Path(spec['run'])
    require(original.is_absolute() and spec['records'] == str(original/'stages/proposal-1'), 'request command record root')
    prefix += ['--ro-bind', str(original/'request.json'), '/request.json',
        '--ro-bind', str(original/'fixture-witness.json'), '/witness.json',
        '--ro-bind', fixtures[0], '/runner/bin/program',
        '--bind', str(original/'stages/proposal-1/output'), '/out', '/runner/bin/program', 'valid', request_hash]
    require(spec['argv'] == prefix and spec['capture_events'] is False,
            'fixture command permits extra inputs, capabilities, or a different request')
