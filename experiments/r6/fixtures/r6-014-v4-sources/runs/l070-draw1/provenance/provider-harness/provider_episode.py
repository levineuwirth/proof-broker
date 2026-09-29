#!/usr/bin/env python3
"""R6-003: the first provider wire adapter, exercised only by isolated HTTP fixtures."""
import argparse
from pathlib import Path
import shutil
import tempfile

import admission
import provider_contract as contract
import provider_payload as wire
import episode
import events
import instrument
import proposal_episode as downstream
import proposal_instrument as overlay
import run as r6

CASES = ('valid', 'alternate_encoding', 'invalid_witness', 'malformed', 'wrong_echo',
    'altered_prompt', 'omitted_prompt', 'altered_prefix', 'altered_body', 'timeout', 'connection_error',
    'disconnect', 'http429', 'http503', 'redirect', 'refusal', 'incomplete', 'tool_call',
    'malformed_provider', 'oversized_response', 'exhausted_budget')


def require(condition, message):
    if not condition: raise ValueError('Provider episode: '+message)


def setup(run, task, packages):
    contract.verify_sources()
    runtime_path, runtime = contract.materialize_runtime()
    tools = downstream.setup(run, task, packages)
    tools.update(python=Path(runtime['python']), runtime=runtime, runtime_path=runtime_path)
    binaries = r6.read_json(run/'provenance/binaries.json')
    binaries[runtime['python']] = runtime['python_sha256']
    r6.write_json(run/'provenance/binaries.json', binaries)
    r6.write_json(run/'provenance/python-runtime.json', runtime)
    r6.write_json(run/'provenance/roles.json', {'python': runtime['python'], 'runtime_path': str(runtime_path),
        'actor_source': str(r6.ROOT/'provider_http.py'),
        'unused_legacy_responder': str(tools['fixture']), 'assembler': str(tools['driver']),
        'verifier': str(tools['verifier']), 'checker': str(tools['checker']),
        'downstream_setup': 'frozen proposal_episode.setup; legacy request policy not executed'})
    for section, module, extra in [('envelope-harness', contract.previous, []),
                                  ('provider-harness', contract, [contract.RUNTIME])]:
        sources = [r6.ROOT/name for name in module.FILES]+[module.CONFIG, module.LOCK]+extra
        for source in sources:
            target = run/'provenance'/section/source.relative_to(r6.ROOT)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
    return tools


def prepare(run, task, tools):
    inputs = downstream.compile_input(run, 'preparation-input', 'PreparationCapture', overlay.capture_source(task, True), task)
    compiler = tools['compiler']
    mounts = [*tools['mounts'], (inputs, '/input')]
    built = episode.stage(run, 'preparation-build', compiler/'bin/lean',
        [*tools['loads'], '-R', '/input', '-o', '/out/PreparationCapture.olean', '/input/PreparationCapture.lean'],
        mounts, compiler=compiler, env={'LEAN_PATH': tools['lean_path']+':/out'}, extra_binaries=tools['extras'])
    captured = episode.stage(run, 'preparation', compiler/'bin/lean',
        [*tools['loads'], '-R', '/input', '-o', '/out/Frozen.olean', '/input/Frozen.lean'],
        [*mounts, (built, '/capture')], compiler=compiler, extra_binaries=tools['extras'],
        env={'LEAN_PATH': tools['lean_path']+':/capture', 'R6_CAPTURE_OUTPUT': '/out/context.json',
             'R6_PREPARE_OUTPUT': '/out/reification.json'})
    context = r6.read_json(captured/'context.json')
    require(context == r6.read_json(task.path/'context/local-context.json'), 'preparation changed frozen context')
    # Admission precedes request construction or reservation.
    r6.write_json(run/'sanitized-context.json', wire.old.context(context))
    reified = r6.read_json(captured/'reification.json')
    r6.write_json(run/'input-ir.json', reified['ir'])
    output = episode.stage(run, 'pipeline-prepare', tools['driver'], ['prepare', '/input-ir.json', '/out/prepared.json'],
                           [(run/'input-ir.json', '/input-ir.json')])
    shutil.copyfile(output/'prepared.json', run/'prepared.json')
    prepared = r6.read_json(run/'prepared.json')
    request = wire.request(task, prepared)
    (run/'request.json').write_bytes(request)
    (run/'request.sha256').write_text(wire.sha(request)+'  request.json\n')
    shutil.copyfile(contract.PROMPT, run/'prompt.txt')
    args = wire.arguments(request)
    r6.write_json(run/'client-arguments.json', args)
    r6.write_json(run/'messages.json', args['input'])
    r6.write_json(run/'payload-audit.json', {
        'request_sha256': wire.sha(request), 'prompt_sha256': r6.sha(run/'prompt.txt'),
        'sanitized_context_sha256': r6.sha(run/'sanitized-context.json'),
        'context_projection_is_model_visible': False, 'source_context_sha256': r6.sha(task.path/'context/local-context.json'),
        'let_facts_preserved': [r['name'] for r in context['telescope'] if r['kind'] == 'let'],
        'reifier_omissions': reified['skipped_locals'], 'farkas_omissions': prepared['farkas_omissions']})
    events.append(run, 'payload', 'payload_validated', {'payload_audit_sha256': r6.sha(run/'payload-audit.json'),
        'request_sha256': wire.sha(request), 'prompt_sha256': r6.sha(run/'prompt.txt'),
        'client_arguments_sha256': r6.sha(run/'client-arguments.json'), 'messages_sha256': r6.sha(run/'messages.json')})
    return prepared


def canned_provider(task, request, case):
    first, coefficient = contract.FIXTURES[task.id]
    witness = {'request_sha256': '0'*64 if case == 'wrong_echo' else wire.sha(request), 'witness': {'coefficients': [
        {'hypothesis': first, 'coefficient': '1' if case == 'invalid_witness' else coefficient},
        {'hypothesis': 'neg_goal', 'coefficient': '4'}]}}
    # Cancel the otherwise large slack. The resulting constant is exactly four;
    # omitting the integer +1 in neg_goal would leave zero, not a contradiction.
    if task == r6.D1: witness['witness']['coefficients'].append({'hypothesis':'hnum', 'coefficient':'4'})
    text = '{"witness":' if case == 'malformed' else (events.canonical(witness)+b'\n').decode()
    # D1 covers a reasoning item before the assistant message and multiple text
    # parts. The server never derives any of this from its received arithmetic.
    parts = [text[:17], text[17:]] if task == r6.D1 else [text]
    content = [{'type': 'output_text', 'text': part, 'annotations': []} for part in parts]
    output = [{'type': 'reasoning', 'id': 'r6_reasoning', 'summary': []}] if task == r6.D1 else []
    output.append({'type': 'message', 'id': 'r6_message', 'status': 'completed', 'role': 'assistant', 'content': content})
    response = {'id': 'r6_canned_response', 'object': 'response', 'model': contract.MODEL,
        'status': 'completed', 'error': None, 'incomplete_details': None, 'output': output,
        'usage': {'input_tokens': 11, 'output_tokens': 7, 'total_tokens': 18,
                  'input_tokens_details': {'cached_tokens': 2}, 'output_tokens_details': {'reasoning_tokens': 3}} if task == r6.D1 else None}
    if case == 'refusal': output[-1]['content'] = [{'type': 'refusal', 'refusal': 'Canned refusal'}]
    elif case == 'incomplete': response.update(status='incomplete', incomplete_details={'reason': 'max_output_tokens'})
    elif case == 'tool_call': output.append({'type': 'function_call', 'name': 'unrequested', 'arguments': '{}'})
    status = {'http429': 429, 'http503': 503, 'redirect': 307}.get(case, 200)
    body = (events.canonical(response)+b'\n').decode()
    if status != 200: body = '{"error":{"message":"canned HTTP control","type":"fixture_error"}}\n'
    elif case == 'malformed_provider': body = '{'
    elif case == 'oversized_response': body = ' '*(contract.config()['maximum_provider_response_bytes']+1)
    return {'status': status, 'body': body}


class Session:
    def __init__(self, run):
        self.run, self.reserved = run, 0
        self.http, self.server, self.metadata = None, None, None
        self.write_accounting()

    def write_accounting(self):
        http = self.http or {}
        absent = None if self.reserved else 0
        value = {'attempts_reserved': self.reserved, 'client_connection_attempts': http.get('connection_attempts', absent),
            'body_sends_started': http.get('body_sends_started', absent), 'body_sends_returned': http.get('body_sends_returned', absent),
            'transmissions_observed': sum(r['complete'] is True for r in self.server['requests']) if self.server is not None else absent,
            'reported_usage': (self.metadata or {}).get('usage', wire.usage({})),
            'live_model_calls': 0, 'live_model_cost_usd': 0,
            'scope': 'local HTTP fixture; usage is synthetic or unreported, cost unknown; actual live calls/cost zero'}
        r6.write_json(self.run/'accounting.json', value)
        return value

    def invoke(self, tools, case):
        c, root = contract.config(), self.run
        if self.reserved >= c['attempt_limit']:
            events.append(root, 'proposal', 'request_budget_exhausted', self.write_accounting())
            raise wire.Failure('request_budget_exhaustion', 'proposal', 'Frozen transmission budget exhausted')
        self.reserved += 1; self.write_accounting()
        request = (root/'request.json').read_bytes()
        require(r6.read_json(root/'client-arguments.json') == wire.arguments(request), 'client arguments changed before serialization')
        events.append(root, 'proposal', 'request_reserved', {'attempt': self.reserved, 'request_sha256': wire.sha(request),
            'prompt_sha256': r6.sha(root/'prompt.txt'), 'client_arguments_sha256': r6.sha(root/'client-arguments.json')})
        runtime = tools['runtime']
        stage_error = None
        try:
            out = episode.stage(root, 'proposal-1', tools['python'],
                ['-I', '-S', '-B', '/adapter.py', '--arguments', '/arguments.json', '--fixture', '/fixture.json',
                 '--case', case, '--out', '/out', '--timeout', str(c['http_timeout_seconds']),
                 '--maximum-body', str(c['maximum_request_bytes']), '--maximum-response', str(c['maximum_provider_response_bytes'])],
                [(tools['runtime_path'], runtime['stdlib']), (r6.ROOT/'provider_http.py', '/adapter.py'),
                 (root/'client-arguments.json', '/arguments.json'), (root/'canned-provider.json', '/fixture.json')],
                extra_binaries=[Path(p) for p in runtime['extension_binaries']],
                wall=c['request_wall_seconds'], cpu=c['request_cpu_seconds'],
                memory=c['request_memory_bytes'], output_limit=c['request_output_bytes'])
        except episode.StageFailure as error:
            stage_error, out = error, root/'stages/proposal-1/output'
        if stage_error:
            for name, attribute in [('http.json', 'http'), ('server.json', 'server')]:
                try: setattr(self, attribute, r6.read_json(out/name))
                except (OSError, ValueError): pass
            self.write_accounting()
            raise stage_error
        try: self.http, self.server = r6.read_json(out/'http.json'), r6.read_json(out/'server.json')
        except (OSError, ValueError) as error:
            raise wire.Failure('transport_capture_failure', 'proposal-1', 'HTTP actor lacks readable observations') from error
        self.write_accounting()
        require(self.http['connection_attempts'] <= self.reserved and self.http['body_sends_started'] <= self.reserved
            and len(self.server['requests']) <= self.reserved, 'hidden retry exceeded reserved budget')
        events.append(root, 'proposal', 'http_observed', {'http_sha256': r6.sha(out/'http.json'),
            'server_sha256': r6.sha(out/'server.json'), 'accounting': self.write_accounting()})
        outbound = (out/'outbound-body.json').read_bytes()
        captured = (out/'received-body-1.json').read_bytes() if (out/'received-body-1.json').exists() else None
        raw = (out/'provider-response.json').read_bytes() if (out/'provider-response.json').exists() else None
        response, text, metadata, validation, error = wire.transport(outbound, captured, raw, self.http, request)
        self.metadata = metadata
        r6.write_json(root/'provider-metadata.json', metadata)
        if text is not None: (root/'response.json').write_bytes(text)
        r6.write_json(root/'transport-validation.json', validation)
        events.append(root, 'proposal', 'transport_validated', validation)
        self.write_accounting()
        if error: raise error
        return response


def consume(run, task, tools, response):
    r6.write_json(run/'validated-response.json', response)
    assembled = episode.stage(run, 'assembly', tools['driver'],
        ['assemble', '/prepared.json', '/response.json', 'sha256:'+r6.sha(contract.CONFIG), '/out/evidence.json'],
        [(run/'prepared.json', '/prepared.json'), (run/'validated-response.json', '/response.json')])
    shutil.copyfile(assembled/'evidence.json', run/'evidence.json')
    packet = r6.read_json(run/'evidence.json')
    events.append(run, 'assembly', 'certificate_assembled', {'certificate_sha256': events.digest(packet['certificate']),
        'witness_proposer': 'canned_provider_response', 'certificate_assembler': 'sdk_proposal_assembler_v1',
        'response_sha256': r6.sha(run/'validated-response.json')})
    try:
        verified = episode.stage(run, 'certificate-check', tools['verifier'], ['/evidence.json', '/out/verdict.json'],
                                  [(run/'evidence.json', '/evidence.json')])
    except episode.StageFailure as error:
        if error.category != 'stage_rejected': raise
        verified = run/'stages/certificate-check/output'
    report = r6.read_json(verified/'verdict.json')
    r6.write_json(run/'certificate-verdict.json', report)
    events.append(run, 'certificate-check', 'independent_certificate_verdict', report)
    events.append(run, 'proposal', 'recovery_finished', {'route': contract.NAME, 'ok': report['accepted'],
        'witness': response['witness'], 'reason': report.get('reason'), 'proposer': 'canned_provider_response'})
    if report['accepted'] is not True:
        raise wire.Failure('certificate_verification', 'certificate-check', 'Farkas witness was not verified', report)
    inputs = downstream.compile_input(run, 'input', 'ProposalCapture', overlay.capture_source(task), task)
    compiler = tools['compiler']
    mounts = [*tools['mounts'], (inputs, '/input')]
    built = episode.stage(run, 'capture-build', compiler/'bin/lean',
        [*tools['loads'], '-R', '/input', '-o', '/out/ProposalCapture.olean', '/input/ProposalCapture.lean'],
        mounts, compiler=compiler, env={'LEAN_PATH': tools['lean_path']+':/out'}, extra_binaries=tools['extras'])
    reconstructed = episode.stage(run, 'reconstruct', compiler/'bin/lean',
        [*tools['loads'], '-R', '/input', '-o', '/out/Frozen.olean', '/input/Frozen.lean'],
        [*mounts, (built, '/capture'), (run/'evidence.json', '/evidence.json')], compiler=compiler,
        extra_binaries=tools['extras'], capture_events=True,
        env={'LEAN_PATH': tools['lean_path']+':/capture', 'R6_PROPOSAL_PACKET': '/evidence.json',
             'PROOF_BROKER_EPISODE_TRACE': '1', 'R6_CAPTURE_OUTPUT': '/out/context.json'})
    require(r6.read_json(reconstructed/'context.json') == r6.read_json(task.path/'context/local-context.json'),
            'reconstruction changed frozen context')
    events.append(run, 'reconstruct', 'context_validated', {'captured_context_sha256': r6.sha(reconstructed/'context.json'),
        'frozen_context_sha256': r6.sha(task.path/'context/local-context.json')})
    exported = episode.stage(run, 'export', tools['exporter'], ['Frozen', '--', task.whole, task.local, *r6.EXPORT_TARGETS],
        [*tools['mounts'], (reconstructed, '/objects'), (built, '/capture')], compiler=compiler,
        extra_binaries=tools['extras'], env={'LEAN_PATH': tools['lean_path']+':/capture:/objects'})
    solution = exported.parent/'export.stdout'
    r6.pack(solution, run/'solution.ndjson.gz')
    with tempfile.TemporaryDirectory(prefix='r6-provider-challenge-') as temp:
        challenge = Path(temp)/'challenge.ndjson'
        r6.unpack(task.path/'challenge.ndjson.gz', challenge)
        require(r6.sha(challenge) == tools['expected']['challenge_sha256'], 'challenge changed')
        reports, delta = episode.final_validation(run, challenge, solution, tools['checker'], tools['expected'], task)
    return packet, report, reports, delta, r6.sha(solution)


def execute(run, task, case, packages):
    config, cohort = contract.config(), admission.verify()
    require(task.id in cohort['controls'] and task.id in contract.FIXTURES, 'task is outside frozen cohort')
    tools = setup(run, task, packages)
    policy = {**config, 'task_id': task.id, 'task_manifest_sha256': r6.sha(task.path/'manifest.json'),
              'contract_sha256': r6.sha(contract.CONFIG), 'case': case, 'sdk_base_commit': instrument.BASE}
    r6.write_json(run/'search-policy.json', policy)
    events.append(run, 'episode', 'episode_started', {'task_manifest_sha256': policy['task_manifest_sha256'],
        'search_policy_sha256': r6.sha(run/'search-policy.json'), 'challenge_sha256': tools['expected']['challenge_sha256']}, task_id=task.id)
    session = Session(run)
    prepare(run, task, tools)
    request = (run/'request.json').read_bytes()
    r6.write_json(run/'canned-provider.json', canned_provider(task, request, case))
    events.append(run, 'proposal', 'recovery_started', {'route': contract.NAME, 'proposer': 'canned_provider_response'})
    response = session.invoke(tools, case)
    if case == 'exhausted_budget':
        session.invoke(tools, case)
        raise AssertionError('Second transmission escaped budget')
    packet, report, reports, delta, solution_hash = consume(run, task, tools, response)
    require(all(r6.sha(Path(p)) == h for p, h in r6.read_json(run/'provenance/binaries.json').items()), 'binary changed')
    r6.frozen_task(task)
    verdict = {'schema_version': 'r6-provider-episode-1', 'search_policy': contract.NAME, 'task_id': task.id,
        'accepted': True, 'search_succeeded': True, 'certificate_type': 'farkas', 'trust_tier': 1,
        'witness_proposer': 'canned_provider_response', 'certificate_assembler': 'sdk_proposal_assembler_v1',
        'recovery_route': contract.NAME, 'certificate_verified': True, 'certificate_consumed': True,
        'derivation_replayed': False, 'residual_closer': 'omega', 'proof_replayed': True,
        'local_obligation_closed': True, 'whole_declaration_validated': True, 'axiom_delta': delta,
        'local_proof_required_reference': episode.FARKAS_HELPER, 'failure_category': None, 'failure_phase': None,
        'accounting': session.write_accounting(), 'transport_validation': r6.read_json(run/'transport-validation.json'),
        'solution_sha256': solution_hash, 'challenge_sha256': tools['expected']['challenge_sha256'],
        'manifest_sha256': r6.sha(task.path/'manifest.json'), 'prompt_sha256': r6.sha(run/'prompt.txt'),
        'request_sha256': wire.sha(request), 'response_sha256': r6.sha(run/'response.json'),
        'final_validation': reports, 'certificate_validation': report,
        'resources': {p.parent.name: r6.read_json(p) for p in sorted((run/'stages').glob('*/*.process.json'))},
        'evidence_receipt_claim': 'local HTTP fixture and proof checks; no remote receipt, compilation or inference attestation'}
    r6.write_json(run/'verdict.json', verdict)
    events.append(run, 'episode', 'episode_finished', {'accepted': True, 'verdict_sha256': r6.sha(run/'verdict.json')})
    episode.seal(run, retained_sources=contract.RETAINED_SOURCES)
    from provider_audit import audit
    audit(run, task)
    return verdict


def seal_failure(run):
    rows = episode.observations(run)
    require(rows and rows[-1]['event'] == 'episode_failed', 'failure seal requires a terminal failure')
    retained = {}
    for p in sorted(run.rglob('*')):
        if not p.is_file() or p.name in {'failure-seal.json', 'seal.json'}: continue
        name = str(p.relative_to(run))
        ephemeral = '.olean' in p.name or p.suffix in {'.ilean', '.c', '.o'} or (p.name == 'verdict.json' and '/output/' in name)
        if not ephemeral or name in contract.RETAINED_SOURCES: retained[name] = r6.sha(p)
    r6.write_json(run/'failure-seal.json', {'schema_version': 'r6-failure-seal-1', 'accepted': False,
        'event_count': len(rows), 'last_event_hash': rows[-1]['event_hash'], 'retained_sha256': retained})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['run', 'audit'])
    parser.add_argument('--task', choices=contract.FIXTURES)
    parser.add_argument('--case', choices=CASES, default='valid')
    parser.add_argument('--run-dir', type=Path, required=True)
    parser.add_argument('--packages-dir', type=Path, default=r6.ROOT.parents[1]/'lean-bridge/.lake/packages')
    parser.add_argument('--development-policy-dir', type=Path)
    args = parser.parse_args()
    if args.development_policy_dir: contract.development(args.development_policy_dir)
    run = args.run_dir.resolve()
    if args.action == 'audit':
        from provider_audit import audit
        task = r6.get_task(args.task or r6.read_json(run/'verdict.json')['task_id'])
        audit(run, task)
        print('Provider HTTP fixture episode audit accepted')
        return
    if not args.task: parser.error('run requires --task')
    task = r6.get_task(args.task)
    run.mkdir(parents=True, exist_ok=False)
    try:
        execute(run, task, args.case, args.packages_dir)
    except Exception as error:
        stage = getattr(error, 'stage', 'harness')
        failure = {'accepted': False, 'task_id': task.id, 'search_policy': contract.NAME,
            'failure_stage': stage, 'failure_phase': contract.PHASES.get(stage, 'harness'),
            'failure_category': getattr(error, 'category', 'harness'), 'error': str(error),
            'evidence': getattr(error, 'evidence', None), 'process': getattr(error, 'stats', None),
            'causal_attribution': 'unassigned; observed boundary only'}
        r6.write_json(run/'failure.json', failure)
        if not (run/'seal.json').exists():
            events.append(run, 'episode', 'episode_failed', failure, task_id=task.id)
            seal_failure(run)
        raise
    print(f'Provider HTTP fixture episode validated: {run}')


if __name__ == '__main__':
    main()
