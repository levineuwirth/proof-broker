"""Frozen R6-001 proof-path checks, reused verbatim for the new transport.

Only the function boundary is new. These are checks of retained observations,
not a fresh execution or a compilation/inference attestation.
"""
import copy
import difflib
import gzip
import hashlib
import json

import episode
import events
import proposal_instrument as overlay
import run as r6


def require(condition, message):
    if not condition: raise ValueError('Envelope proof audit: '+message)


def audit(task, packet, verdict, rows, path, read, receipt):
    _, expected = r6.frozen_task(task)
    cert = packet['certificate']
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
