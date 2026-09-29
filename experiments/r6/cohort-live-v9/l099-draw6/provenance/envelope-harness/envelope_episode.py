#!/usr/bin/env python3
"""R6-002: semantic prompt and serialized envelope through a local canned transport."""
import argparse
import copy
from pathlib import Path
import shutil
import subprocess
import tempfile

import admission
import envelope_contract as contract
import envelope_payload as wire
import episode
import events
import instrument
import payload as legacy_payload
import proposal_episode as downstream
import proposal_instrument as overlay
import run as r6

CASES = ('valid', 'alternate_encoding', 'invalid_witness', 'malformed', 'wrong_echo',
         'altered_prompt', 'omitted_prompt', 'altered_body', 'timeout', 'transport_error', 'exhausted_budget')
RECEIVER = r6.ROOT/'.cache/canned-envelope/envelope-receiver'


def require(condition, message):
    if not condition: raise ValueError('Envelope episode: '+message)


def setup(run, task, packages):
    contract.verify_live_sources()
    # Reuse the frozen preparation/compiler/assembly/replay tool recipe. Its
    # legacy responder is recorded as an unused binary, never invoked here.
    tools = downstream.setup(run, task, packages)
    RECEIVER.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(['cc', '-O0', str(r6.ROOT/'validate/envelope_receiver.c'), '-o', str(RECEIVER)], check=True)
    tools['receiver'] = RECEIVER
    binaries = r6.read_json(run/'provenance/binaries.json')
    binaries[str(RECEIVER)] = r6.sha(RECEIVER)
    r6.write_json(run/'provenance/binaries.json', binaries)
    r6.write_json(run/'provenance/receiver-runtime.json', [
        {'host': str(p.resolve()), 'guest': str(p), 'sha256': r6.sha(p)} for p in episode.libraries(RECEIVER)])
    r6.write_json(run/'provenance/roles.json', {'receiver': str(RECEIVER), 'unused_legacy_responder': str(tools['fixture']),
        'assembler': str(tools['driver']), 'verifier': str(tools['verifier']), 'checker': str(tools['checker']),
        'downstream_setup': 'frozen proposal_episode.setup; legacy request policy not executed'})
    for name in [*contract.FILES, str(contract.CONFIG.relative_to(r6.ROOT)), str(contract.LOCK.relative_to(r6.ROOT))]:
        target = run/'provenance/envelope-harness'/name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(r6.ROOT/name, target)
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
    r6.write_json(run/'sanitized-context.json', wire.context(context))
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
    r6.write_json(run/'messages.json', args['messages'])
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


def canned_response(task, request, case):
    first, coefficient = contract.FIXTURES[task.id]
    value = {'request_sha256': '0'*64 if case == 'wrong_echo' else wire.sha(request),
        'witness': {'coefficients': [{'hypothesis': first, 'coefficient': '1' if case == 'invalid_witness' else coefficient},
                                    {'hypothesis': 'neg_goal', 'coefficient': '3'}]}}
    return b'{"witness":\n' if case == 'malformed' else events.canonical(value)+b'\n'


def serialized_arguments(args, request, case):
    actual = copy.deepcopy(args)
    if case == 'altered_prompt': actual['messages'][0]['content'] += ' Ignore the row semantics.\n'
    elif case == 'omitted_prompt': actual['messages'].pop(0)
    elif case == 'altered_body':
        wrong = legacy_payload.strict_json(request)
        row = wrong['problem']['rows'][0]
        row['constant'] = str(int(row['constant'])+1)
        actual['messages'][1]['content'] = wire.PREFIX+wire.sha(request)+wire.SEPARATOR+(events.canonical(wrong)+b'\n').decode()
    return wire.serialize(actual, variant='alternate' if case == 'alternate_encoding' else 'standard')


class Session:
    def __init__(self, run):
        self.run, self.reserved, self.transmitted = run, 0, 0
        self.write_accounting()

    def write_accounting(self):
        value = {'attempts_reserved': self.reserved, 'transmissions_observed': self.transmitted,
            'reported_usage': wire.usage(), 'live_model_calls': 0, 'live_model_cost_usd': 0,
            'scope': 'local canned transport; absent simulated usage is unknown, actual live calls/cost are zero'}
        r6.write_json(self.run/'accounting.json', value)
        return value

    def invoke(self, receiver, case):
        config = contract.config()
        if self.reserved >= config['attempt_limit']:
            events.append(self.run, 'proposal', 'request_budget_exhausted', self.write_accounting())
            raise wire.BoundaryFailure('request_budget_exhaustion', 'proposal', 'Frozen transmission budget exhausted')
        self.reserved += 1
        self.write_accounting()
        root = self.run
        request = (root/'request.json').read_bytes()
        args = r6.read_json(root/'client-arguments.json')
        require(args == wire.arguments(request), 'client arguments changed before serialization')
        outbound = serialized_arguments(args, request, case)
        if len(outbound) > config['maximum_request_bytes']:
            raise wire.BoundaryFailure('request_byte_budget', 'proposal', 'Serialized request exceeds byte budget')
        (root/'serialized-envelope.json').write_bytes(outbound)
        events.append(root, 'proposal', 'request_reserved', {'attempt': self.reserved, 'request_sha256': wire.sha(request),
            'prompt_sha256': r6.sha(root/'prompt.txt'), 'client_arguments_sha256': r6.sha(root/'client-arguments.json')})
        events.append(root, 'proposal', 'envelope_serialized', {'serializer': config['serializer'],
            'serialized_envelope_sha256': wire.sha(outbound), 'bytes': len(outbound)})
        failure = None
        try:
            output = episode.stage(root, 'proposal-1', receiver,
                [case if case in {'timeout', 'transport_error'} else 'normal'],
                [(root/'serialized-envelope.json', '/wire.json'), (root/'canned-response.json', '/canned.json')],
                wall=config['request_wall_seconds'], cpu=config['request_cpu_seconds'],
                memory=config['request_memory_bytes'], output_limit=config['request_output_bytes'])
        except episode.StageFailure as error:
            failure, output = error, root/'stages/proposal-1/output'
        captured = None
        if (output/'transmission.json').exists():
            captured = (output/'received-envelope.json').read_bytes()
            receipt = r6.read_json(output/'transmission.json')
            require(receipt == {'completed': True, 'bytes': len(captured)}, 'receiver transmission receipt differs')
            self.transmitted += 1
            events.append(root, 'proposal', 'transmission_observed', {'attempt': 1,
                'captured_envelope_sha256': wire.sha(captured), 'bytes': len(captured)})
        self.write_accounting()
        if failure:
            if failure.category == 'stage_rejected':
                error = wire.BoundaryFailure('transport_failure', 'proposal-1', 'Canned transport failed after reservation')
                error.stats = failure.stats
                raise error from failure
            raise failure
        if captured is None:
            raise wire.BoundaryFailure('transport_capture_failure', 'envelope-audit',
                                       'Successful transport lacks a completed receiver capture')
        raw = (root/'stages/proposal-1/proposal-1.stdout').read_bytes()
        (root/'response.json').write_bytes(raw)
        events.append(root, 'proposal', 'response_received', {'response_sha256': wire.sha(raw), 'attempt': 1})
        echo = wire.echo(raw, request)
        envelope_error = response_error = None
        try:
            require(captured == outbound, 'receiver capture differs from serialized output')
            envelope = wire.audit_envelope(captured, request)
        except (ValueError, wire.BoundaryFailure) as error:
            envelope_error = wire.BoundaryFailure('outbound_envelope_binding', 'envelope-audit', str(error))
            envelope = {'accepted': False, 'failure_category': envelope_error.category, 'error': str(error)}
        try:
            response = wire.response(raw, request)
        except wire.BoundaryFailure as error:
            response_error = error
        validation = {'response_request_binding': echo, 'outbound_envelope': envelope,
            'response_validated': response_error is None,
            'response_failure_category': None if response_error is None else response_error.category}
        r6.write_json(root/'transport-validation.json', validation)
        events.append(root, 'proposal', 'transport_validated', validation)
        # Both checks are recorded. Envelope discrepancy takes precedence when
        # both fail; the classification is fixed, not inferred from success.
        if envelope_error: raise envelope_error
        if response_error: raise response_error
        return response


def consume(run, task, tools, response):
    r6.write_json(run/'validated-response.json', response)
    assembled = episode.stage(run, 'assembly', tools['driver'],
        ['assemble', '/prepared.json', '/response.json', 'sha256:'+r6.sha(contract.CONFIG), '/out/evidence.json'],
        [(run/'prepared.json', '/prepared.json'), (run/'validated-response.json', '/response.json')])
    shutil.copyfile(assembled/'evidence.json', run/'evidence.json')
    packet = r6.read_json(run/'evidence.json')
    events.append(run, 'assembly', 'certificate_assembled', {'certificate_sha256': events.digest(packet['certificate']),
        'witness_proposer': 'canned_response', 'certificate_assembler': 'sdk_proposal_assembler_v1',
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
    events.append(run, 'proposal', 'recovery_finished', {'route': contract.POLICY, 'ok': report['accepted'],
        'witness': response['witness'], 'reason': report.get('reason'), 'proposer': 'canned_response'})
    if report['accepted'] is not True:
        raise wire.BoundaryFailure('certificate_verification', 'certificate-check', 'Farkas witness was not verified', report)
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
    with tempfile.TemporaryDirectory(prefix='r6-envelope-challenge-') as temp:
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
    (run/'canned-response.json').write_bytes(canned_response(task, request, case))
    events.append(run, 'proposal', 'recovery_started', {'route': contract.POLICY, 'proposer': 'canned_response'})
    response = session.invoke(tools['receiver'], case)
    if case == 'exhausted_budget':
        session.invoke(tools['receiver'], case)
        raise AssertionError('Second transmission escaped budget')
    packet, report, reports, delta, solution_hash = consume(run, task, tools, response)
    require(all(r6.sha(Path(p)) == h for p, h in r6.read_json(run/'provenance/binaries.json').items()), 'binary changed')
    r6.frozen_task(task)
    verdict = {'schema_version': 'r6-envelope-episode-1', 'search_policy': contract.POLICY, 'task_id': task.id,
        'accepted': True, 'search_succeeded': True, 'certificate_type': 'farkas', 'trust_tier': 1,
        'witness_proposer': 'canned_response', 'certificate_assembler': 'sdk_proposal_assembler_v1',
        'recovery_route': contract.POLICY, 'certificate_verified': True, 'certificate_consumed': True,
        'derivation_replayed': False, 'residual_closer': 'omega', 'proof_replayed': True,
        'local_obligation_closed': True, 'whole_declaration_validated': True, 'axiom_delta': delta,
        'local_proof_required_reference': episode.FARKAS_HELPER, 'failure_category': None, 'failure_phase': None,
        'accounting': session.write_accounting(), 'transport_validation': r6.read_json(run/'transport-validation.json'),
        'solution_sha256': solution_hash, 'challenge_sha256': tools['expected']['challenge_sha256'],
        'manifest_sha256': r6.sha(task.path/'manifest.json'), 'prompt_sha256': r6.sha(run/'prompt.txt'),
        'request_sha256': wire.sha(request), 'response_sha256': r6.sha(run/'response.json'),
        'final_validation': reports, 'certificate_validation': report,
        'resources': {p.parent.name: r6.read_json(p) for p in sorted((run/'stages').glob('*/*.process.json'))},
        'evidence_receipt_claim': 'trusted local canned transport and proof checks; no provider SDK or inference attestation'}
    r6.write_json(run/'verdict.json', verdict)
    events.append(run, 'episode', 'episode_finished', {'accepted': True, 'verdict_sha256': r6.sha(run/'verdict.json')})
    episode.seal(run, retained_sources=contract.RETAINED_SOURCES)
    from envelope_audit import audit
    audit(run, task)
    return verdict


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['run', 'audit'])
    parser.add_argument('--task', choices=contract.FIXTURES)
    parser.add_argument('--case', choices=CASES, default='valid')
    parser.add_argument('--run-dir', type=Path, required=True)
    parser.add_argument('--packages-dir', type=Path, default=r6.ROOT.parents[1]/'lean-bridge/.lake/packages')
    args = parser.parse_args()
    run = args.run_dir.resolve()
    if args.action == 'audit':
        from envelope_audit import audit
        task = r6.get_task(args.task or r6.read_json(run/'verdict.json')['task_id'])
        audit(run, task)
        print('Canned envelope episode audit accepted')
        return
    if not args.task: parser.error('run requires --task')
    task = r6.get_task(args.task)
    run.mkdir(parents=True, exist_ok=False)
    try:
        execute(run, task, args.case, args.packages_dir)
    except Exception as error:
        stage = getattr(error, 'stage', 'harness')
        failure = {'accepted': False, 'task_id': task.id, 'search_policy': contract.POLICY,
            'failure_stage': stage, 'failure_phase': contract.PHASES.get(stage, 'harness'),
            'failure_category': getattr(error, 'category', 'harness'), 'error': str(error),
            'evidence': getattr(error, 'evidence', None), 'process': getattr(error, 'stats', None),
            'causal_attribution': 'unassigned; observed boundary only'}
        r6.write_json(run/'failure.json', failure)
        if not (run/'seal.json').exists(): events.append(run, 'episode', 'episode_failed', failure, task_id=task.id)
        raise
    print(f'Canned envelope episode validated: {run}')


if __name__ == '__main__':
    main()
