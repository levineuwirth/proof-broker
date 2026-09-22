#!/usr/bin/env python3
"""R6-001 fixture proposals behind the existing Farkas/replay boundary."""
import argparse
import difflib
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

import admission
import episode
import events
import instrument
import payload
import proposal_instrument as overlay
import run as r6

POLICY = 'fixture_farkas_v1'
CASES = ('valid', 'invalid_witness', 'malformed', 'wrong_binding', 'timeout', 'exhausted_budget')
FIXTURES = {r6.D1.id: ('hZ', '4'), r6.C8.id: ('hhi', '524288')}


class PolicyFailure(episode.StageFailure):
    pass


def require(condition, message):
    if not condition:
        raise ValueError('Proposal episode: '+message)


def admit_task(task):
    config, cohort = r6.read_json(payload.CONTRACT), admission.verify()
    require(config['admission_sha256'] == r6.sha(admission.FROZEN), 'admission rule/cohort changed')
    require(config['source_lock_sha256'] == r6.sha(overlay.SOURCE_LOCK), 'source lock changed')
    require(task.id in cohort['controls'] and task.id in FIXTURES, 'task is outside the frozen fixture cohort')
    return config


def compile_input(run, name, helper_name, helper_text, task):
    root = run/name
    root.mkdir()
    (root/(helper_name+'.lean')).write_text(helper_text)
    pristine = (task.path/'Pristine.lean').read_text()
    tactic = 'r6_prepare' if helper_name == 'PreparationCapture' else 'r6_capture_proposal'
    source = r6.instrument(pristine, task).replace('import Capture\n', f'import {helper_name}\n').replace('r6_capture_human', tactic)
    (root/'Frozen.lean').write_text(source)
    (root/'source.patch').write_text(''.join(difflib.unified_diff(pristine.splitlines(True), source.splitlines(True),
                                                               fromfile='Pristine.lean', tofile='Frozen.lean')))
    return root


def setup(run, task, packages):
    overlay.verify_live_sources()
    _, expected = r6.frozen_task(task)
    compiler, exporter, checker = r6.build_tools(task=task)
    dest, sources, patch = overlay.build(compiler)
    mounts, lean_path, environment = r6.environment(packages.resolve(), compiler, task)
    with gzip.open(task.path/'environment-inventory.json.gz', 'rt') as f:
        require(environment == expected['environment'] and r6.inventory(mounts, compiler) == json.load(f),
                'frozen environment changed')
    native = dest/'bridge/.lake/build/lib/lean'
    modules = [native/f'r6_x2dproposal_ProofBroker_{name}.so' for name in ['IR', 'Trace', 'Bridge', 'TermMode', 'Alethe', 'Tactic']]
    ffi = dest/'sdk/_build/default/ffi/proof_broker_ffi.so'
    glue = r6.ROOT.parents[1]/'lean-bridge/.lake/build/lib/libpbglue.so'
    driver = dest/'sdk/_build/default/validate/proposal_driver.exe'
    verifier = dest/'sdk/_build/default/validate/verify_certificate.exe'
    fixture = dest/'fixture'
    subprocess.run(['cc', '-O0', str(r6.ROOT/'validate/fixture_responder.c'), '-o', str(fixture)], check=True)
    binaries = [compiler/'bin/lean', exporter, checker, ffi, glue, driver, verifier, fixture, *modules]
    provenance = run/'provenance'
    provenance.mkdir()
    r6.write_json(provenance/'sources.json', sources)
    (provenance/'instrumentation.patch').write_text(patch)
    r6.write_json(provenance/'binaries.json', {str(p): r6.sha(p) for p in binaries})
    for name in overlay.HARNESS_FILES:
        target = provenance/'harness'/name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(r6.ROOT/name, target)
    r6.write_json(run/'runtime.json', r6.runtime_record(checker))
    r6.write_json(provenance/'fixture-runtime.json', [
        {'host': str(p.resolve()), 'guest': str(p), 'sha256': r6.sha(p)} for p in episode.libraries(fixture)])
    bridge_mounts = [(native, '/broker/modules'), (ffi, '/broker/lib/ffi.so'), (glue, '/broker/lib/glue.so')]
    loads = ['--load-dynlib=/broker/lib/glue.so', '--load-dynlib=/broker/lib/ffi.so']
    loads += [f'--load-dynlib=/broker/modules/{p.name}' for p in modules]
    return {'compiler': compiler, 'exporter': exporter, 'checker': checker, 'driver': driver, 'verifier': verifier,
            'fixture': fixture, 'mounts': [*mounts, *bridge_mounts], 'loads': loads,
            'extras': [ffi, glue, *modules], 'lean_path': lean_path+':/broker/modules', 'expected': expected}


def prepare(run, task, tools):
    inputs = compile_input(run, 'preparation-input', 'PreparationCapture', overlay.capture_source(task, True), task)
    compiler = tools['compiler']
    mounts = [*tools['mounts'], (inputs, '/input')]
    built = episode.stage(run, 'preparation-build', compiler/'bin/lean',
        [*tools['loads'], '-R', '/input', '-o', '/out/PreparationCapture.olean', '/input/PreparationCapture.lean'],
        mounts, compiler=compiler, env={'LEAN_PATH': tools['lean_path']+':/out'}, extra_binaries=tools['extras'])
    prepared = episode.stage(run, 'preparation', compiler/'bin/lean',
        [*tools['loads'], '-R', '/input', '-o', '/out/Frozen.olean', '/input/Frozen.lean'],
        [*mounts, (built, '/capture')], compiler=compiler, extra_binaries=tools['extras'],
        env={'LEAN_PATH': tools['lean_path']+':/capture', 'R6_CAPTURE_OUTPUT': '/out/context.json',
             'R6_PREPARE_OUTPUT': '/out/reification.json'})
    context = r6.read_json(prepared/'context.json')
    require(context == r6.read_json(task.path/'context/local-context.json'), 'preparation changed frozen context')
    reified = r6.read_json(prepared/'reification.json')
    r6.write_json(run/'input-ir.json', reified['ir'])
    output = episode.stage(run, 'pipeline-prepare', tools['driver'], ['prepare', '/input-ir.json', '/out/prepared.json'],
                           [(run/'input-ir.json', '/input-ir.json')])
    shutil.copyfile(output/'prepared.json', run/'prepared.json')
    prepared = r6.read_json(run/'prepared.json')
    projection = payload.project_context(context)
    r6.write_json(run/'sanitized-context.json', projection)
    request = payload.request(task, prepared)
    (run/'request.json').write_bytes(events.canonical(request)+b'\n')
    (run/'request.sha256').write_text(r6.sha(run/'request.json')+'  request.json\n')
    r6.write_json(run/'payload-audit.json', {
        'request_sha256': r6.sha(run/'request.json'), 'sanitized_context_sha256': r6.sha(run/'sanitized-context.json'),
        'source_context_sha256': r6.sha(task.path/'context/local-context.json'),
        'context_projection_is_model_visible': False, 'context_policy': 'farkas_rows_only_v1',
        'let_facts_preserved': [r['name'] for r in context['telescope'] if r['kind'] == 'let'],
        'reifier_omissions': reified['skipped_locals'], 'farkas_omissions': prepared['farkas_omissions']})
    events.append(run, 'payload', 'payload_validated', {'request_sha256': r6.sha(run/'request.json'),
        'payload_audit_sha256': r6.sha(run/'payload-audit.json')})
    return prepared


class RequestSession:
    def __init__(self, run, config):
        self.run, self.config, self.used = run, config, 0

    def invoke(self, fixture, witness, case):
        if self.used >= self.config['attempt_limit']:
            events.append(self.run, 'proposal', 'request_budget_exhausted', {'attempts_used': self.used})
            raise PolicyFailure('proposal', 'request_budget_exhaustion', 'Frozen request budget exhausted')
        self.used += 1
        name = f'proposal-{self.used}'
        digest = r6.sha(self.run/'request.json')
        events.append(self.run, 'proposal', 'request_started', {'attempt': self.used, 'request_sha256': digest})
        output = episode.stage(self.run, name, fixture,
            [case, '0'*64 if case == 'wrong_binding' else digest],
            [(self.run/'request.json', '/request.json'), (witness, '/witness.json')],
            wall=self.config['request_wall_seconds'], cpu=self.config['request_cpu_seconds'],
            memory=self.config['request_memory_bytes'], output_limit=self.config['request_output_bytes'])
        raw = output.parent/(name+'.stdout')
        shutil.copyfile(raw, self.run/'response.json')
        events.append(self.run, 'proposal', 'response_received', {'attempt': self.used, 'response_sha256': r6.sha(raw)})
        try:
            return payload.response(raw.read_bytes(), (self.run/'request.json').read_bytes())
        except (ValueError, RecursionError, UnicodeError, r6.jsonschema.ValidationError) as error:
            category = 'proposal_binding' if 'different request' in str(error) else 'proposal_decode'
            raise PolicyFailure('proposal', category, str(error)) from error


def execute(run, task, case, packages):
    config = admit_task(task)
    tools = setup(run, task, packages)
    policy = {**config, 'task_id': task.id, 'parent_task_manifest_sha256': r6.sha(task.path/'manifest.json'),
              'contract_sha256': r6.sha(payload.CONTRACT), 'sdk_base_commit': instrument.BASE,
              'fixture_case': case, 'preparation_closer': 'frozen_human_omega'}
    r6.write_json(run/'search-policy.json', policy)
    events.append(run, 'episode', 'episode_started', {'task_manifest_sha256': policy['parent_task_manifest_sha256'],
        'search_policy_sha256': r6.sha(run/'search-policy.json'), 'challenge_sha256': tools['expected']['challenge_sha256']}, task_id=task.id)
    prepared = prepare(run, task, tools)
    # Deliberately rescale both golden witnesses: this policy must not inherit
    # either control's exact-coefficient or deterministic-route requirement.
    first, coefficient = FIXTURES[task.id]
    witness = {'coefficients': [{'hypothesis': first, 'coefficient': coefficient},
                                {'hypothesis': 'neg_goal', 'coefficient': '2'}]}
    if case == 'invalid_witness':
        witness['coefficients'][0]['coefficient'] = '1'
    r6.write_json(run/'fixture-witness.json', witness)
    events.append(run, 'proposal', 'recovery_started', {'route': POLICY, 'proposer': config['proposer']})
    session = RequestSession(run, config)
    response = session.invoke(tools['fixture'], run/'fixture-witness.json', case)
    if case == 'exhausted_budget':
        session.invoke(tools['fixture'], run/'fixture-witness.json', case)
        raise AssertionError('Second request escaped its budget')
    r6.write_json(run/'validated-response.json', response)
    assembled = episode.stage(run, 'assembly', tools['driver'],
        ['assemble', '/prepared.json', '/response.json', 'sha256:'+r6.sha(payload.CONTRACT), '/out/evidence.json'],
        [(run/'prepared.json', '/prepared.json'), (run/'validated-response.json', '/response.json')])
    shutil.copyfile(assembled/'evidence.json', run/'evidence.json')
    packet = r6.read_json(run/'evidence.json')
    events.append(run, 'assembly', 'certificate_assembled', {'certificate_sha256': events.digest(packet['certificate']),
        'witness_proposer': config['proposer'], 'certificate_assembler': config['certificate_assembler'],
        'response_sha256': r6.sha(run/'validated-response.json')})
    try:
        verified = episode.stage(run, 'certificate-check', tools['verifier'], ['/evidence.json', '/out/verdict.json'],
                                  [(run/'evidence.json', '/evidence.json')])
    except episode.StageFailure as error:
        if error.category != 'stage_rejected':
            raise
        verified = run/'stages/certificate-check/output'
    report = r6.read_json(verified/'verdict.json')
    r6.write_json(run/'certificate-verdict.json', report)
    events.append(run, 'certificate-check', 'independent_certificate_verdict', report)
    events.append(run, 'proposal', 'recovery_finished', {'route': POLICY, 'ok': report['accepted'],
        'witness': response['witness'], 'reason': report.get('reason'), 'proposer': config['proposer']})
    if report['accepted'] is not True:
        raise PolicyFailure('certificate-check', 'certificate_verification', json.dumps(report))
    inputs = compile_input(run, 'input', 'ProposalCapture', overlay.capture_source(task), task)
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
    with tempfile.TemporaryDirectory(prefix='r6-proposal-challenge-') as temp:
        challenge = Path(temp)/'challenge.ndjson'
        r6.unpack(task.path/'challenge.ndjson.gz', challenge)
        require(r6.sha(challenge) == tools['expected']['challenge_sha256'], 'challenge changed')
        reports, delta = episode.final_validation(run, challenge, solution, tools['checker'], tools['expected'], task)
    binaries = r6.read_json(run/'provenance/binaries.json')
    require(all(r6.sha(Path(p)) == digest for p, digest in binaries.items()), 'binary changed during episode')
    r6.frozen_task(task)
    verdict = {'schema_version': 'r6-proposal-episode-1', 'search_policy': POLICY, 'task_id': task.id,
        'accepted': True, 'search_succeeded': True, 'certificate_type': 'farkas', 'trust_tier': 1,
        'witness_proposer': config['proposer'], 'certificate_assembler': config['certificate_assembler'],
        'recovery_route': POLICY, 'certificate_verified': True, 'certificate_consumed': True,
        'derivation_replayed': False, 'residual_closer': 'omega', 'proof_replayed': True,
        'local_obligation_closed': True, 'whole_declaration_validated': True, 'axiom_delta': delta,
        'local_proof_required_reference': episode.FARKAS_HELPER, 'fixture_requests': session.used,
        'model_calls': 0, 'model_tokens': 0, 'model_cost_usd': 0,
        'failure_category': None,
        'solution_sha256': r6.sha(solution), 'challenge_sha256': tools['expected']['challenge_sha256'],
        'manifest_sha256': r6.sha(task.path/'manifest.json'), 'request_sha256': r6.sha(run/'request.json'),
        'response_sha256': r6.sha(run/'response.json'), 'final_validation': reports, 'certificate_validation': report,
        'resources': {p.parent.name: r6.read_json(p) for p in sorted((run/'stages').glob('*/*.process.json'))},
        'evidence_receipt_claim': 'trusted-host observations; fixture transport; no model computation attestation'}
    r6.write_json(run/'verdict.json', verdict)
    events.append(run, 'episode', 'episode_finished', {'accepted': True, 'verdict_sha256': r6.sha(run/'verdict.json')})
    episode.seal(run, retained_sources=overlay.RETAINED_SOURCES)
    from proposal_audit import audit
    audit(run, task)
    return verdict


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--task', choices=r6.TASKS, required=True)
    parser.add_argument('--case', choices=CASES, default='valid')
    parser.add_argument('--run-dir', type=Path, required=True)
    parser.add_argument('--packages-dir', type=Path, default=r6.ROOT.parents[1]/'lean-bridge/.lake/packages')
    args = parser.parse_args()
    run, task = args.run_dir.resolve(), r6.get_task(args.task)
    run.mkdir(parents=True, exist_ok=False)
    try:
        execute(run, task, args.case, args.packages_dir)
    except Exception as error:
        failure = {'accepted': False, 'task_id': task.id, 'search_policy': POLICY,
            'failure_stage': getattr(error, 'stage', 'harness'), 'failure_category': getattr(error, 'category', 'harness'),
            'error': str(error), 'process': getattr(error, 'stats', None),
            'causal_attribution': 'unassigned; observed boundary only'}
        # Even a late publication-audit failure must leave a red marker. A seal
        # and a recorded kernel success alone are not episode acceptance.
        r6.write_json(run/'failure.json', failure)
        if not (run/'seal.json').exists():
            events.append(run, 'episode', 'episode_failed', failure, task_id=task.id)
        raise
    print(f'Fixture proposal independently validated: {run}')


if __name__ == '__main__':
    main()
