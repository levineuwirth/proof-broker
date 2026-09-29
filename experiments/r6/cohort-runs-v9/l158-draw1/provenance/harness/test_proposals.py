#!/usr/bin/env python3
"""R6-001 payload, admission, native transport and resealed audit regressions.

Every run starts red, records each completed case immediately, and compares an
independent expected-name set before its terminal green write. Existing runs
are immutable. No provider credentials or model API are used.
"""
import argparse
import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from unittest import mock

import admission
import episode
import events
import instrument
import payload
import proposal_audit
import proposal_episode
import proposal_instrument as overlay
import run as r6
from test_task_identity import rehash

UNIT_CASES = '''d1_let_facts c8_no_let_control synthetic_leakage_precondition
synthetic_safe_projection unredacted_rejected value_field_rejected placeholder_rejected
proof_string_rejected dropped_let_rejected changed_type_rejected duplicate_index_rejected
strict_ir_request request_proof_field_rejected request_proof_string_rejected altered_sdk_row_rejected
farkas_omission_rejected wrong_response_binding duplicate_json_rejected unknown_support_rejected
repeated_support_rejected oversized_coefficient_rejected wrong_witness_is_well_formed
p6_checked_counterexample p6_source_anchor_required p6_drop_anchor_required p6_bad_assignment
membership_all_conjuncts membership_unknown membership_typed
missing_case_rejected duplicate_case_rejected third_policy_task_rejected'''.split()
NATIVE_CASES = '''d1_valid c8_valid d1_invalid_witness c8_invalid_witness
d1_malformed d1_wrong_binding d1_timeout d1_exhausted_budget'''.split()
AUDIT_CASES = '''d1_retained_only c8_retained_only
wrong_proposer wrong_assembler numeric_boolean missing_request_receipt hidden_fallback
wrong_request_mount unsafe_request_flag wrong_budget leaked_context changed_task_source
wrong_witness wrong_recovery missing_c_source wrong_source_provenance late_failure_marker
wrong_harness_source current_source_independence
legacy_broker_v1 legacy_broker_v2 legacy_broker_v3 legacy_c8_v1 prior_artifacts_preserved'''.split()


def require(condition, detail='test assertion failed'):
    if not condition:
        raise AssertionError(detail)


def rejected(fn, contains=None):
    try:
        fn()
    except (ValueError, AssertionError, r6.jsonschema.ValidationError) as error:
        if contains is not None:
            require(contains in str(error), f'wrong rejection: {error}')
        return {'rejected': True, 'reason': str(error)}
    raise AssertionError('Corruption was accepted')


def assert_complete(names, expected):
    require(len(names) == len(set(names)), 'duplicate case')
    require(set(names) == set(expected), f'missing/extra cases: {set(names)^set(expected)}')


class Suite:
    def __init__(self, output, expected):
        self.output, self.expected, self.results = output, expected, []
        self.write(False)

    def write(self, passed):
        r6.write_json(self.output, {'passed': passed, 'expected_cases': self.expected,
                                   'check_count': len(self.results), 'checks': self.results})

    def case(self, name, fn):
        require(name in self.expected and name not in [r['name'] for r in self.results], 'unknown/duplicate case')
        result = fn()
        self.results.append({'name': name, 'passed': True, 'detail': result})
        self.write(False)
        print(name, 'PASS', flush=True)

    def finish(self):
        assert_complete([r['name'] for r in self.results], self.expected)
        self.write(True)


def units(output):
    suite = Suite(output/'payload-admission.json', UNIT_CASES)
    contexts = {t.id: r6.read_json(t.path/'context/local-context.json') for t in (r6.D1, r6.C8)}
    d1, c8 = contexts[r6.D1.id], contexts[r6.C8.id]
    def d1_lets():
        projection = payload.project_context(d1)
        names = [r['name'] for r in d1['telescope'] if r['kind'] == 'let']
        require(len(names) == 6 and len(projection['hypotheses']) == 17)
        require(set(names) <= {r['name'] for r in projection['hypotheses']})
        return {'kept_let_facts': names, 'genuine_entries': 17}
    suite.case('d1_let_facts', d1_lets)
    def no_lets():
        require(len(payload.project_context(c8)['hypotheses']) == 3)
        require(not [r for r in c8['telescope'] if r['kind'] == 'let'])
        return 'Negative-shape control; does not establish proof-body redaction'
    suite.case('c8_no_let_control', no_lets)
    synthetic = {'target': 'n ≤ 5', 'telescope': [
        {'index': 0, 'name': 'container', 'type': '∀ n, n ≤ 5', 'binder_info': 'default',
         'kind': 'declaration_placeholder', 'value': None},
        {'index': 1, 'name': 'n', 'type': 'Nat', 'binder_info': 'default', 'kind': 'binder', 'value': None},
        {'index': 2, 'name': 'hbound', 'type': 'n ≤ 5', 'binder_info': 'default',
         'kind': 'let', 'value': 'container._proof_1 n'}]}
    def precondition():
        require(sum(r['kind'] == 'declaration_placeholder' for r in synthetic['telescope']) == 1)
        require(sum(r['kind'] == 'let' and '_proof_' in r['value'] for r in synthetic['telescope']) == 1)
        return 'Exactly one placeholder and one proof-bearing let'
    suite.case('synthetic_leakage_precondition', precondition)
    safe = payload.project_context(synthetic)
    suite.case('synthetic_safe_projection', lambda: payload.validate_context(safe, synthetic))
    raw = {'target': synthetic['target'], 'hypotheses': copy.deepcopy(synthetic['telescope'])}
    suite.case('unredacted_rejected', lambda: rejected(lambda: payload.validate_context(raw, synthetic)))
    def context_mutation(name, change, original=synthetic):
        def test():
            projected = payload.project_context(original)
            before = events.canonical(projected)
            change(projected)
            require(events.canonical(projected) != before, 'mutation matched nothing')
            return rejected(lambda: payload.validate_context(projected, original))
        suite.case(name, test)
    context_mutation('value_field_rejected', lambda p: p['hypotheses'][-1].update(value='container._proof_1 n'))
    context_mutation('placeholder_rejected', lambda p: p['hypotheses'][0].update(index=0, name='container', type='∀ n, n ≤ 5'))
    # Validate the string filter on an otherwise identical context projection.
    malicious = copy.deepcopy(synthetic)
    malicious['telescope'][-1]['type'] = 'container._proof_1 = container._proof_1'
    suite.case('proof_string_rejected', lambda: rejected(lambda: payload.project_context(malicious), 'Proof auxiliary'))
    context_mutation('dropped_let_rejected', lambda p: p['hypotheses'].pop())
    context_mutation('changed_type_rejected', lambda p: p['hypotheses'][-1].update(type='n ≤ 6'))
    context_mutation('duplicate_index_rejected', lambda p: p['hypotheses'][-1].update(index=1))
    # This old golden supplies real SDK IR, independently projected here. The
    # two native positives below additionally compare fresh SDK-compiled rows.
    packet = r6.read_json(r6.ROOT/'runs/golden-broker-v3/evidence.json')
    prepared = {**packet, 'fragment': 'LIA', 'rows': payload.arithmetic_rows(packet['final_ir']), 'farkas_omissions': []}
    request = payload.request(r6.D1, prepared)
    request_bytes = events.canonical(request)+b'\n'
    def strict_ir():
        payload.validate_request(request)
        require(set(request['problem']) == {'fragment', 'rows'})
        lets = {r['name'] for r in d1['telescope'] if r['kind'] == 'let'}
        require(len(lets) == 6 and lets <= {r['name'] for r in request['problem']['rows']})
        return {'request_sha256': r6.hashlib.sha256(request_bytes).hexdigest(), 'let_facts_in_rows': sorted(lets)}
    suite.case('strict_ir_request', strict_ir)
    def request_change(name, change):
        value = copy.deepcopy(request)
        change(value)
        suite.case(name, lambda: rejected(lambda: payload.validate_request(value)))
    request_change('request_proof_field_rejected', lambda p: p.update(context=safe))
    request_change('request_proof_string_rejected', lambda p: p['problem']['rows'][0].update(name='lift_cell._proof_1'))
    altered = copy.deepcopy(prepared)
    altered['rows'][0]['constant'] = str(int(altered['rows'][0]['constant'])+1)
    suite.case('altered_sdk_row_rejected', lambda: rejected(lambda: payload.request(r6.D1, altered), 'SDK rows differ'))
    omitted = {**prepared, 'farkas_omissions': ['hZval']}
    suite.case('farkas_omission_rejected', lambda: rejected(lambda: payload.request(r6.D1, omitted), 'omissions'))
    response = {'request_sha256': r6.hashlib.sha256(request_bytes).hexdigest(), 'witness': {'coefficients': [
        {'hypothesis': 'hZ', 'coefficient': '1'}, {'hypothesis': 'neg_goal', 'coefficient': '2'}]}}
    def response_change(name, change):
        value = copy.deepcopy(response)
        change(value)
        suite.case(name, lambda: rejected(lambda: payload.response(events.canonical(value), request_bytes)))
    response_change('wrong_response_binding', lambda r: r.update(request_sha256='0'*64))
    suite.case('duplicate_json_rejected', lambda: rejected(lambda: payload.strict_json('{"a":1,"a":2}'), 'Duplicate'))
    response_change('unknown_support_rejected', lambda r: r['witness']['coefficients'][0].update(hypothesis='not_a_fact'))
    response_change('repeated_support_rejected', lambda r: r['witness']['coefficients'][0].update(hypothesis='neg_goal'))
    response_change('oversized_coefficient_rejected', lambda r: r['witness']['coefficients'][0].update(coefficient='1'*129))
    suite.case('wrong_witness_is_well_formed', lambda: payload.response(events.canonical(response), request_bytes))
    p6 = admission.verify()['P6_hyp_le']['evidence']
    def p6_check():
        require(p6['classification'] == 'translation_loss_diagnostic' and p6['original_true'] is True
                and p6['ir_counterexample_checked'] is True and all(r['satisfied'] for r in p6['row_evaluations']))
        return p6
    suite.case('p6_checked_counterexample', p6_check)
    inputs = {k: instrument.original(v) for k, v in admission.P6_FILES.items()}
    source, log, ir = inputs['source'].decode(), inputs['reification_log'].decode(), payload.strict_json(inputs['final_ir'])
    require(source.count('hhi :') == 1 and log.count('hhi — proposition') == 1)
    suite.case('p6_source_anchor_required', lambda: rejected(lambda: admission.p6_evidence(source.replace('hhi :', 'hle :'), log, ir), 'anchor'))
    suite.case('p6_drop_anchor_required', lambda: rejected(lambda: admission.p6_evidence(source, log.replace('hhi —', 'hle —'), ir), 'anchor'))
    def bad_assignment():
        rows, result = admission.counterexample(payload.arithmetic_rows(ir), {'_pb_atom_0': 0})
        require(result is False and rows[-1]['satisfied'] is False)
        return rows
    suite.case('p6_bad_assignment', bad_assignment)
    def conjuncts():
        require(admission.classify(True, True, True) == 'translation_loss_diagnostic')
        for index in range(3):
            flags = [True]*3
            flags[index] = False
            require(admission.classify(*flags) == 'criterion_not_established')
    suite.case('membership_all_conjuncts', conjuncts)
    def unknown():
        for index in range(3):
            flags = [True]*3
            flags[index] = None
            require(admission.classify(*flags) == 'unresolved')
    suite.case('membership_unknown', unknown)
    suite.case('membership_typed', lambda: rejected(lambda: admission.classify(1, True, True)))
    suite.case('missing_case_rejected', lambda: rejected(lambda: assert_complete(['a'], ['a', 'b']), 'missing'))
    suite.case('duplicate_case_rejected', lambda: rejected(lambda: assert_complete(['a', 'a'], ['a']), 'duplicate'))
    suite.case('third_policy_task_rejected', lambda: rejected(lambda: proposal_episode.admit_task(
        __import__('types').SimpleNamespace(id='third-control')), 'outside the frozen fixture cohort'))
    suite.finish()


def native(output):
    suite = Suite(output/'native-fixtures.json', NATIVE_CASES)
    for name in NATIVE_CASES:
        control, case = name.split('_', 1)
        task = r6.D1 if control == 'd1' else r6.C8
        def test(name=name, case=case, task=task):
            target = output/name
            with (output/(name+'.log')).open('w') as log:
                result = subprocess.run([sys.executable, str(r6.ROOT/'proposal_episode.py'), '--task', task.id,
                    '--case', case, '--run-dir', str(target)], stdout=log, stderr=subprocess.STDOUT)
            rows = events.read(target/'events.ndjson')
            if case == 'valid':
                require(result.returncode == 0, f'{name} failed; see its log')
                verdict = episode.audit(target, task)
                return {'verdict_sha256': r6.sha(target/'verdict.json'), 'seal_sha256': r6.sha(target/'seal.json'),
                        'request_sha256': verdict['request_sha256'], 'solution_sha256': verdict['solution_sha256'],
                        'axiom_delta': verdict['axiom_delta']}
            require(result.returncode != 0, f'{name} corruption accepted')
            failure = r6.read_json(target/'failure.json')
            category = {'invalid_witness': 'certificate_verification', 'malformed': 'proposal_decode',
                'wrong_binding': 'proposal_binding', 'timeout': 'resource_exhaustion',
                'exhausted_budget': 'request_budget_exhaustion'}[case]
            require(failure['failure_category'] == category, f'{name}: {failure}')
            require(rows[-1]['event'] == 'episode_failed' and rows[-1]['payload'] == failure)
            require(not (target/'verdict.json').exists() and not (target/'seal.json').exists()
                    and not any(r['event'] == 'episode_finished' or r['stage'] == 'reconstruct' for r in rows))
            require(sum(r['event'] == 'request_started' for r in rows) == 1)
            if case == 'invalid_witness':
                # Establish format success, healthy verifier execution, and an
                # actual negative arithmetic verdict at the intended boundary.
                payload.response((target/'response.json').read_bytes(), (target/'request.json').read_bytes())
                v = r6.read_json(target/'certificate-verdict.json')
                p = r6.read_json(target/'stages/certificate-check/certificate-check.process.json')
                require(v['accepted'] is False and v['stage'] == 'certificate_verification')
                require(p['exit_code'] != 0 and p['resource_exhausted'] is None and p['monitor_error'] is None
                        and p['workload_empty_after_cleanup'] is True)
            if case == 'timeout':
                p = r6.read_json(target/'stages/proposal-1/proposal-1.process.json')
                require(p['resource_exhausted'] == 'wall_time' and p['workload_empty_after_cleanup'] is True)
            if case == 'exhausted_budget':
                require(not (target/'stages/proposal-2').exists())
            return {'failure_category': category, 'failure_sha256': r6.sha(target/'failure.json'),
                    'completion_event_absent': True, 'failure_marker_preserved': True}
        suite.case(name, test)
    suite.finish()


def retained_copy(source, destination):
    seal = r6.read_json(source/'seal.json')
    for name in ['seal.json', *seal['retained_sha256']]:
        p = destination/name
        p.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source/name, p)


def reseal(root):
    rows = events.read(root/'events.ndjson')
    rows[-1]['payload']['verdict_sha256'] = r6.sha(root/'verdict.json')
    (root/'events.ndjson').write_bytes(rehash(rows))
    episode.seal(root, retained_sources=overlay.RETAINED_SOURCES)


def audits(output):
    suite = Suite(output/'audit-regressions.json', AUDIT_CASES)
    def standalone(control):
        task = r6.D1 if control == 'd1' else r6.C8
        with tempfile.TemporaryDirectory(prefix='r6-proposal-publication-') as directory:
            root = Path(directory)
            retained_copy(output/(control+'_valid'), root)
            verdict = episode.audit(root, task)
            require((root/'provenance/harness/validate/fixture_responder.c').exists())
            return {'accepted': verdict['accepted'], 'retained_files': len(r6.read_json(root/'seal.json')['retained_sha256'])}
    for control in ['d1', 'c8']:
        suite.case(control+'_retained_only', lambda c=control: standalone(c))
    def mutate(name, change, expected):
        def test():
            with tempfile.TemporaryDirectory(prefix='r6-proposal-mutation-') as directory:
                root = Path(directory)
                retained_copy(output/'d1_valid', root)
                before = {str(p.relative_to(root)): r6.sha(p) for p in root.rglob('*') if p.is_file()}
                change(root)
                after = {str(p.relative_to(root)): r6.sha(p) for p in root.rglob('*') if p.is_file()}
                require(before != after, 'corruption matched nothing')
                reseal(root)
                result = rejected(lambda: episode.audit(root, r6.D1), expected)
                result['coherently_resealed'] = True
                result['changed_artifacts'] = sorted(k for k in before.keys()|after.keys() if before.get(k) != after.get(k))
                return result
        suite.case(name, test)
    def edit(root, name, change):
        value = r6.read_json(root/name)
        change(value)
        r6.write_json(root/name, value)
    for field, value, name in [('witness_proposer', 'sdk_synthesis', 'wrong_proposer'),
                                ('certificate_assembler', 'model', 'wrong_assembler'),
                                ('certificate_consumed', 1, 'numeric_boolean')]:
        mutate(name, lambda root, f=field, v=value: edit(root, 'verdict.json', lambda x: x.update({f: v})), None)
    def log_change(root, fn):
        rows = events.read(root/'events.ndjson')
        fn(rows)
        (root/'events.ndjson').write_bytes(rehash(rows))
    def remove_request(rows):
        indices = [i for i, r in enumerate(rows) if r['event'] == 'request_started']
        require(len(indices) == 1)
        rows.pop(indices[0])
    mutate('missing_request_receipt', lambda root: log_change(root, remove_request), 'supervisor receipts')
    mutate('hidden_fallback', lambda root: edit(root, 'search-policy.json', lambda x: x.update(fallback_routes=['cvc4'])), 'fixture policy')
    def wrong_mount(spec):
        argv = spec['argv']
        matches = [i for i, item in enumerate(argv) if item == '/request.json']
        require(len(matches) == 1)
        argv[matches[0]-1] = str(r6.D1.path/'Pristine.lean')
    mutate('wrong_request_mount', lambda root: edit(root, 'stages/proposal-1/command.json', wrong_mount), 'fixture command')
    mutate('unsafe_request_flag', lambda root: edit(root, 'stages/proposal-1/command.json',
        lambda x: x['argv'].remove('--unshare-all')), 'fixture command')
    mutate('wrong_budget', lambda root: edit(root, 'stages/proposal-1/command.json', lambda x: x.update(cpu_seconds=2)), 'limit receipt')
    mutate('leaked_context', lambda root: edit(root, 'sanitized-context.json',
        lambda x: x['hypotheses'][-1].update(value='lift_cell._proof_1_1')), 'allowlist')
    mutate('changed_task_source', lambda root: (root/'input/Frozen.lean').write_text('theorem changed : True := True.intro\n'), 'permitted extraction')
    def wrong_witness(root):
        edit(root, 'evidence.json', lambda x: x['certificate']['payload']['witness_data']['coefficients'][0].update(coefficient='3'))
        shutil.copyfile(root/'evidence.json', root/'stages/assembly/output/evidence.json')
    mutate('wrong_witness', wrong_witness, 'assembled witnesses differ')
    def wrong_route(rows):
        chosen = [r for r in rows if r['source'] == 'supervisor' and r['event'] == 'recovery_finished']
        require(len(chosen) == 1)
        chosen[0]['payload']['route'] = 'bounded_enumeration'
    mutate('wrong_recovery', lambda root: log_change(root, wrong_route), 'recovery attribution')
    mutate('missing_c_source', lambda root: (root/'provenance/harness/validate/fixture_responder.c').unlink(), 'not retained')
    mutate('wrong_source_provenance', lambda root: edit(root, 'provenance/sources.json',
        lambda x: x['sdk/lib/farkas_search.ml'].update(instrumented_sha256='0'*64)), 'overlay provenance')
    mutate('late_failure_marker', lambda root: r6.write_json(root/'failure.json',
        {'accepted': False, 'failure_category': 'publication_audit'}), 'failure marker')
    mutate('wrong_harness_source', lambda root: (root/'provenance/harness/proposal_episode.py').write_text('# changed\n'),
           'harness source differs')
    def current_source_independence():
        original_sha = r6.sha
        live = {r6.ROOT/name for name in overlay.source_lock()}
        def guarded_sha(path):
            require(Path(path) not in live, 'audit consulted mutable working-tree harness sources')
            return original_sha(path)
        with mock.patch.object(r6, 'sha', guarded_sha):
            require(episode.audit(output/'d1_valid', r6.D1)['accepted'])
        return 'Audit uses the frozen source lock and saved source bytes, not working-tree harness bytes'
    suite.case('current_source_independence', current_source_independence)
    for name, directory, task in [('legacy_broker_v1', 'golden-broker-v1', r6.D1),
            ('legacy_broker_v2', 'golden-broker-v2', r6.D1), ('legacy_broker_v3', 'golden-broker-v3', r6.D1),
            ('legacy_c8_v1', 'golden-c8-v1', r6.C8)]:
        suite.case(name, lambda d=directory, t=task: {'accepted': episode.audit(r6.ROOT/'runs'/d, t)['accepted']})
    def preservation():
        records = r6.read_json(output/'prior-artifacts.sha256.json')
        require(all((instrument.REPO/p).is_file() and r6.sha(instrument.REPO/p) == h for p, h in records.items()),
                'a pre-existing artifact changed')
        return {'checked_files': len(records), 'changed': 0, 'missing': 0}
    suite.case('prior_artifacts_preserved', preservation)
    suite.finish()


def snapshot(output):
    records = {}
    # HEAD is the committed R6-000/C1 checkpoint. Compare with Git bytes, not a
    # new snapshot that could silently bless an already changed old artifact.
    base = '25c3b77'
    paths = r6.command(['git', '-C', instrument.REPO, 'ls-tree', '-r', '--name-only', base,
        'experiments/r6/tasks', 'experiments/r6/runs', 'experiments/c1-cert-recovery']).splitlines()
    for path in paths:
        content = subprocess.check_output(['git', '-C', str(instrument.REPO), 'show', base+':'+path])
        records[path] = r6.hashlib.sha256(content).hexdigest()
    r6.write_json(output/'prior-artifacts.sha256.json', records)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir', type=Path, required=True)
    parser.add_argument('--units-only', action='store_true')
    args = parser.parse_args()
    root = args.run_dir.resolve()
    root.mkdir(parents=True, exist_ok=False)
    r6.write_json(root/'checkpoint.json', {'passed': False})
    units(root)
    if args.units_only:
        return
    snapshot(root)
    native(root)
    audits(root)
    r6.write_json(root/'checkpoint.json', {'passed': True, 'model_calls': 0,
        'suites': {name: {'sha256': r6.sha(root/name), 'count': r6.read_json(root/name)['check_count']}
                   for name in ['payload-admission.json', 'native-fixtures.json', 'audit-regressions.json']}})


if __name__ == '__main__':
    main()
