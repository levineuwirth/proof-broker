#!/usr/bin/env python3
"""R6-002: exact-name-gated prompt, transport, native and resealed audit checks.

No live calls. Every suite and checkpoint starts red. Existing run directories
are never reused. Negative episodes retain their failure marker and no seal.
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
import envelope_audit as auditor
import envelope_contract as contract
import envelope_episode as harness
import envelope_payload as wire
import episode
import events
import instrument
import payload as legacy
import proposal_instrument as overlay
import run as r6
from test_proposals import Suite, assert_complete, rejected, require, retained_copy
from test_task_identity import rehash

UNIT_CASES = '''prompt_binding exact_request_suffix no_self_hash same_messages_different_wire
changed_prompt omitted_prompt altered_body_correct_echo messages_extra_field
duplicate_envelope_key duplicate_response_key wrong_prompt_hash noncanonical_request
wrong_echo_neutral malformed_response invalid_witness_format response_limit request_limit
unknown_usage reported_zero partial_usage invalid_usage inconsistent_usage
d1_six_let_facts c8_no_let_control admission_auxiliary_review admission_injected_body
admission_dropped_let admission_placeholder admission_precedes_preparation_request
missing_capture_rejected budget_before_second_stage p6_frozen_criterion
proof_checks_unchanged missing_case_rejected duplicate_case_rejected source_lock_guard'''.split()
NATIVE_CASES = '''d1_valid c8_valid d1_alternate_encoding d1_invalid_witness c8_invalid_witness
d1_malformed d1_wrong_echo d1_altered_prompt d1_omitted_prompt d1_altered_body
d1_timeout d1_transport_error d1_exhausted_budget'''.split()
AUDIT_CASES = '''d1_retained_only c8_retained_only alternate_retained_only
changed_prompt_file changed_prompt_binding altered_body_passing_echo omitted_serialized_prompt
capture_only_mutation wrong_messages wrong_client_arguments wrong_transmission_receipt
missing_transmission_event wrong_request_mount unsafe_receiver_flag wrong_budget
unknown_usage_as_zero hidden_retry hidden_fallback wrong_proposer wrong_assembler
wrong_witness wrong_recovery extra_attestation_claim missing_receiver_source wrong_new_source
wrong_old_source late_failure_marker current_source_independence
legacy_broker_v1 legacy_broker_v2 legacy_broker_v3 legacy_c8_v1 legacy_d1_fixture legacy_c8_fixture
prior_artifacts_preserved'''.split()


def failure(fn, category, phase, stage=None):
    try:
        fn()
    except wire.BoundaryFailure as error:
        require(error.category == category and error.phase == phase, f'wrong boundary: {error.category}/{error.phase}: {error}')
        if stage is not None: require(error.stage == stage, 'wrong detector stage')
        return {'category': error.category, 'phase': error.phase, 'stage': error.stage, 'error': str(error), 'evidence': error.evidence}
    raise AssertionError('Corruption was accepted')


def units(root):
    suite = Suite(root/'prompt-transport.json', UNIT_CASES)
    prior = r6.ROOT/'runs/proposal-checkpoint-v2/d1_valid'
    prepared = r6.read_json(prior/'prepared.json')
    request = wire.request(r6.D1, prepared)
    value, args = legacy.strict_json(request), wire.arguments(request)
    raw = harness.canned_response(r6.D1, request, 'valid')
    def prompt_binding():
        require(value['binding']['prompt_sha256'] == r6.sha(contract.PROMPT))
        require(args['messages'][0] == {'role': 'system', 'content': contract.PROMPT.read_text()})
        return {'prompt_sha256': r6.sha(contract.PROMPT), 'request_sha256': wire.sha(request)}
    suite.case('prompt_binding', prompt_binding)
    def suffix():
        require(args['messages'][1]['content'].encode() == (wire.PREFIX+wire.sha(request)+wire.SEPARATOR).encode()+request)
        return 'Exact canonical UTF-8 request bytes occur as the user message suffix'
    suite.case('exact_request_suffix', suffix)
    def no_self():
        require(wire.sha(request).encode() not in request and 'request_sha256' not in value)
        require(args['messages'][1]['content'].count(wire.sha(request)) == 1)
    suite.case('no_self_hash', no_self)
    def serialization():
        a, b = wire.serialize(args), wire.serialize(args, variant='alternate')
        require(a != b and b'\\u03a3' in a and 'Σ'.encode() in b)
        require(legacy.strict_json(a) == legacy.strict_json(b) == args)
        for envelope in [a, b]: require(wire.audit_envelope(envelope, request)['accepted'])
        return {'standard_sha256': wire.sha(a), 'alternate_sha256': wire.sha(b), 'decoded_messages_equal': True}
    suite.case('same_messages_different_wire', serialization)
    for name, case in [('changed_prompt', 'altered_prompt'), ('omitted_prompt', 'omitted_prompt'),
                        ('altered_body_correct_echo', 'altered_body')]:
        def check(case=case):
            require(wire.echo(raw, request)['accepted'] is True)
            changed = harness.serialized_arguments(args, request, case)
            require(changed != wire.serialize(args), 'mutation matched nothing')
            result = failure(lambda: wire.audit_envelope(changed, request), 'outbound_envelope_binding', 'proposal')
            return {**result, 'echo_accepted': True, 'well_formed_response': wire.response(raw, request) is not None}
        suite.case(name, check)
    extra = copy.deepcopy(args); extra['messages'][0]['proof'] = 'secret'
    suite.case('messages_extra_field', lambda: failure(lambda: wire.audit_envelope(wire.serialize(extra), request), 'outbound_envelope_binding', 'proposal'))
    duplicate = wire.serialize(args).replace(b'"schema_version":', b'"schema_version":"wrong","schema_version":', 1)
    suite.case('duplicate_envelope_key', lambda: failure(lambda: wire.audit_envelope(duplicate, request), 'outbound_envelope_binding', 'proposal'))
    suite.case('duplicate_response_key', lambda: failure(lambda: wire.response(raw.replace(b'{', b'{"request_sha256":"duplicate",', 1), request), 'response_decode', 'proposal'))
    changed = copy.deepcopy(value); changed['binding']['prompt_sha256'] = '0'*64
    suite.case('wrong_prompt_hash', lambda: failure(lambda: wire.validate_request(changed), 'request_binding_failure', 'preparation'))
    suite.case('noncanonical_request', lambda: failure(lambda: wire.arguments(json.dumps(value).encode()), 'request_binding_failure', 'preparation'))
    def neutral():
        result = failure(lambda: wire.response(harness.canned_response(r6.D1, request, 'wrong_echo'), request), 'transport_binding_failure', 'proposal')
        require(result['error'] == 'Response request digest does not match the recorded request bytes')
        return result
    suite.case('wrong_echo_neutral', neutral)
    suite.case('malformed_response', lambda: failure(lambda: wire.response(b'{', request), 'response_decode', 'proposal'))
    suite.case('invalid_witness_format', lambda: wire.response(harness.canned_response(r6.D1, request, 'invalid_witness'), request))
    suite.case('response_limit', lambda: failure(lambda: wire.response(b' '*131073, request), 'response_decode', 'proposal'))
    suite.case('request_limit', lambda: failure(lambda: wire.audit_envelope(b' '*(1024**2+1), request), 'outbound_envelope_binding', 'proposal'))
    def unknown():
        report = wire.usage()
        require(all(report[k] is None for k in ['input_tokens', 'output_tokens', 'total_tokens', 'cost_usd']))
        require(report['status'] == 'unreported')
        return report
    suite.case('unknown_usage', unknown)
    def zero():
        report = wire.usage({'input_tokens': 0, 'output_tokens': 0, 'total_tokens': 0})
        require(report['status'] == 'provider_reported' and report['total_tokens'] == 0 and report['cost_usd'] is None)
        return report
    suite.case('reported_zero', zero)
    def partial():
        report = wire.usage({'input_tokens': 3})
        require(report['output_tokens'] is None and report['total_tokens'] is None and report['cost_usd'] is None)
        return report
    suite.case('partial_usage', partial)
    suite.case('invalid_usage', lambda: [failure(lambda v=v: wire.usage({'total_tokens': v}), 'usage_decode', 'proposal') for v in [-1, True, 1.5, '1']])
    suite.case('inconsistent_usage', lambda: failure(lambda: wire.usage({'input_tokens': 1, 'output_tokens': 2, 'total_tokens': 4}), 'usage_decode', 'proposal'))

    d1, c8 = [r6.read_json(t.path/'context/local-context.json') for t in (r6.D1, r6.C8)]
    def lets():
        names = [r['name'] for r in d1['telescope'] if r['kind'] == 'let']
        projected = wire.context(d1)
        require(len(names) == 6 and len(projected['hypotheses']) == 17)
        require(set(names) <= {r['name'] for r in projected['hypotheses']})
        require(set(names) <= {r['name'] for r in value['problem']['rows']})
        return names
    suite.case('d1_six_let_facts', lets)
    def nolets():
        require(len(wire.context(c8)['hypotheses']) == 3 and not any(r['kind'] == 'let' for r in c8['telescope']))
        return 'C8 contains no let bodies; the redaction controls use D1'
    suite.case('c8_no_let_control', nolets)
    auxiliary = copy.deepcopy(d1)
    auxiliary['telescope'][-1]['type'] = 'Eq Foo._proof_1 Foo._proof_1'
    def guarded(original, projected, category):
        with tempfile.TemporaryDirectory(prefix='r6-admission-control-') as directory:
            session = harness.Session(Path(directory))
            with mock.patch.object(session, 'invoke') as invoke:
                def pipeline():
                    wire.context(original, projected)
                    session.invoke(Path('/unused'), 'valid')
                result = failure(pipeline, category, 'admission', 'context-admission')
                require(not invoke.called and session.reserved == 0 and session.transmitted == 0)
            return {**result, 'requests': 0, 'source_changed_for_control': original != d1}
    suite.case('admission_auxiliary_review', lambda: guarded(auxiliary, None, 'context_admission_review_required'))
    injected = wire.context(d1); injected['hypotheses'][-1]['value'] = d1['telescope'][-1]['value']
    require('_proof_' in injected['hypotheses'][-1]['value'], 'body injection precondition absent')
    suite.case('admission_injected_body', lambda: guarded(d1, injected, 'payload_integrity_failure'))
    dropped = wire.context(d1); dropped['hypotheses'].pop()
    suite.case('admission_dropped_let', lambda: guarded(d1, dropped, 'payload_integrity_failure'))
    placeholder = wire.context(d1); placeholder['hypotheses'].insert(0, copy.deepcopy(d1['telescope'][0]))
    suite.case('admission_placeholder', lambda: guarded(d1, placeholder, 'payload_integrity_failure'))
    def preparation_order():
        # Exercise production prepare(), not just a reproduction of its order.
        with tempfile.TemporaryDirectory(prefix='r6-admission-prepare-') as directory:
            root = Path(directory)
            capture = root/'capture'; capture.mkdir()
            r6.write_json(capture/'context.json', auxiliary)
            original_read = r6.read_json
            def read(path):
                return auxiliary if Path(path) == r6.D1.path/'context/local-context.json' else original_read(path)
            tools = {'compiler': Path('/compiler'), 'mounts': [], 'loads': [], 'lean_path': '', 'extras': []}
            with mock.patch.object(harness.downstream, 'compile_input', return_value=root/'input'), \
                 mock.patch.object(episode, 'stage', side_effect=[root/'built', capture]) as stage, \
                 mock.patch.object(r6, 'read_json', side_effect=read), \
                 mock.patch.object(wire, 'request') as request_builder:
                result = failure(lambda: harness.prepare(root, r6.D1, tools), 'context_admission_review_required', 'admission')
                require(stage.call_count == 2 and not request_builder.called and not (root/'request.json').exists())
            return {**result, 'requests_constructed': 0}
    suite.case('admission_precedes_preparation_request', preparation_order)
    def missing_capture():
        with tempfile.TemporaryDirectory(prefix='r6-capture-control-') as directory:
            root = Path(directory)
            events.append(root, 'episode', 'episode_started', {}, task_id=r6.D1.id)
            (root/'request.json').write_bytes(request); shutil.copyfile(contract.PROMPT, root/'prompt.txt')
            r6.write_json(root/'client-arguments.json', args)
            output = root/'output'; output.mkdir()
            session = harness.Session(root)
            with mock.patch.object(episode, 'stage', return_value=output):
                result = failure(lambda: session.invoke(Path('/unused'), 'valid'), 'transport_capture_failure', 'proposal')
            require(session.reserved == 1 and session.transmitted == 0)
            return result
    suite.case('missing_capture_rejected', missing_capture)
    def budget():
        with tempfile.TemporaryDirectory(prefix='r6-budget-control-') as directory:
            root = Path(directory)
            events.append(root, 'episode', 'episode_started', {}, task_id=r6.D1.id)
            session = harness.Session(root); session.reserved = 1
            with mock.patch.object(episode, 'stage') as stage:
                result = failure(lambda: session.invoke(Path('/unused'), 'valid'), 'request_budget_exhaustion', 'proposal')
                require(not stage.called)
            return result
    suite.case('budget_before_second_stage', budget)
    suite.case('p6_frozen_criterion', lambda: admission.verify()['P6_hyp_le'])
    def same_proof_checks():
        old = (r6.ROOT/'proposal_audit.py').read_text()
        old = old[old.index('    child_names ='):old.index('    flags =')]
        new = (r6.ROOT/'envelope_proof_audit.py').read_text()
        require(new[new.index('    child_names ='):] == old)
        return {'unchanged_proof_checks_sha256': wire.sha(old.encode())}
    suite.case('proof_checks_unchanged', same_proof_checks)
    suite.case('missing_case_rejected', lambda: rejected(lambda: assert_complete(['a'], ['a', 'b']), 'missing'))
    suite.case('duplicate_case_rejected', lambda: rejected(lambda: assert_complete(['a', 'a'], ['a']), 'duplicate'))
    def source_guard():
        original_sha = r6.sha
        def changed(path): return '0'*64 if Path(path) == r6.ROOT/'envelope_episode.py' else original_sha(path)
        with mock.patch.object(r6, 'sha', side_effect=changed):
            return rejected(contract.verify_live_sources, 'frozen source revision')
    suite.case('source_lock_guard', source_guard)
    suite.finish()


def native(root):
    suite = Suite(root/'native-envelopes.json', NATIVE_CASES)
    boundaries = {'invalid_witness': ('certificate_verification', 'certificate-check', 'certificate_verification'),
        'malformed': ('response_decode', 'response-decode', 'proposal'),
        'wrong_echo': ('transport_binding_failure', 'response-binding', 'proposal'),
        'altered_prompt': ('outbound_envelope_binding', 'envelope-audit', 'proposal'),
        'omitted_prompt': ('outbound_envelope_binding', 'envelope-audit', 'proposal'),
        'altered_body': ('outbound_envelope_binding', 'envelope-audit', 'proposal'),
        'timeout': ('resource_exhaustion', 'proposal-1', 'proposal'),
        'transport_error': ('transport_failure', 'proposal-1', 'proposal'),
        'exhausted_budget': ('request_budget_exhaustion', 'proposal', 'proposal')}
    for name in NATIVE_CASES:
        control, case = name.split('_', 1)
        task = r6.D1 if control == 'd1' else r6.C8
        def test(name=name, case=case, task=task):
            target = root/name
            with (root/(name+'.log')).open('w') as log:
                result = subprocess.run([sys.executable, str(r6.ROOT/'envelope_episode.py'), 'run', '--task', task.id,
                    '--case', case, '--run-dir', str(target)], stdout=log, stderr=subprocess.STDOUT)
            require((target/'events.ndjson').exists(), f'{name} failed before an episode; see its log')
            rows = events.read(target/'events.ndjson')
            if case in {'valid', 'alternate_encoding'}:
                require(result.returncode == 0, f'{name} failed; see its log')
                verdict = auditor.audit(target, task)
                require(all(not d['added'] and not d['removed'] for d in verdict['axiom_delta'].values()))
                return {'verdict_sha256': r6.sha(target/'verdict.json'), 'seal_sha256': r6.sha(target/'seal.json'),
                    'prompt_sha256': verdict['prompt_sha256'], 'request_sha256': verdict['request_sha256'],
                    'solution_sha256': verdict['solution_sha256'], 'axiom_delta': verdict['axiom_delta'],
                    'accounting': verdict['accounting']}
            require(result.returncode != 0, f'{name} corruption accepted')
            record = r6.read_json(target/'failure.json')
            expected = boundaries[case]
            require(tuple(record[k] for k in ['failure_category', 'failure_stage', 'failure_phase']) == expected, f'{name}: {record}')
            require(rows[-1]['event'] == 'episode_failed' and rows[-1]['payload'] == record)
            require(not (target/'verdict.json').exists() and not (target/'seal.json').exists()
                and not any(r['event'] == 'episode_finished' or r['stage'] == 'reconstruct' for r in rows))
            require(sum(r['event'] == 'request_reserved' for r in rows) == 1)
            require(sum(r['event'] == 'transmission_observed' for r in rows) == 1)
            accounting = r6.read_json(target/'accounting.json')
            require(accounting['attempts_reserved'] == accounting['transmissions_observed'] == 1)
            require(accounting['reported_usage'] == wire.usage() and accounting['live_model_calls'] == 0)
            stats = r6.read_json(target/'stages/proposal-1/proposal-1.process.json')
            require(stats['workload_empty_after_cleanup'] is True)
            if case in {'altered_prompt', 'omitted_prompt', 'altered_body'}:
                transport = r6.read_json(target/'transport-validation.json')
                require(transport['response_request_binding']['accepted'] is True and transport['response_validated'] is True
                    and transport['outbound_envelope']['accepted'] is False)
                require(not (target/'stages/assembly').exists())
            if case == 'invalid_witness':
                transport = r6.read_json(target/'transport-validation.json')
                require(transport['response_request_binding']['accepted'] is True and transport['outbound_envelope']['accepted'] is True)
                report = r6.read_json(target/'certificate-verdict.json')
                checked = r6.read_json(target/'stages/certificate-check/certificate-check.process.json')
                require(report['accepted'] is False and report['stage'] == 'certificate_verification')
                require(checked['exit_code'] != 0 and checked['resource_exhausted'] is None and checked['monitor_error'] is None
                    and checked['workload_empty_after_cleanup'] is True)
            if case == 'timeout': require(stats['resource_exhausted'] == 'wall_time')
            else: require(stats['resource_exhausted'] is None and stats['monitor_error'] is None)
            if case == 'transport_error': require(stats['exit_code'] == 17)
            if case == 'exhausted_budget': require(not (target/'stages/proposal-2').exists())
            return {'failure_category': expected[0], 'failure_stage': expected[1], 'failure_phase': expected[2],
                'failure_sha256': r6.sha(target/'failure.json'), 'completion_event_absent': True,
                'failure_marker_preserved': True, 'accounting': accounting}
        suite.case(name, test)
    suite.finish()


def audits(root):
    suite = Suite(root/'envelope-audits.json', AUDIT_CASES)
    for name, source, task in [('d1_retained_only', 'd1_valid', r6.D1), ('c8_retained_only', 'c8_valid', r6.C8),
                               ('alternate_retained_only', 'd1_alternate_encoding', r6.D1)]:
        def standalone(source=source, task=task):
            with tempfile.TemporaryDirectory(prefix='r6-envelope-publication-') as directory:
                target = Path(directory); retained_copy(root/source, target)
                require(auditor.audit(target, task)['accepted'])
                return {'retained_files': len(r6.read_json(target/'seal.json')['retained_sha256'])}
        suite.case(name, standalone)
    def edit(target, name, change):
        value = r6.read_json(target/name); change(value); r6.write_json(target/name, value)
    def log_change(target, change):
        rows = events.read(target/'events.ndjson'); change(rows); (target/'events.ndjson').write_bytes(rehash(rows))
    def mutate(name, change, expected):
        def test():
            with tempfile.TemporaryDirectory(prefix='r6-envelope-mutation-') as directory:
                target = Path(directory); retained_copy(root/'d1_valid', target)
                before = {str(p.relative_to(target)): r6.sha(p) for p in target.rglob('*') if p.is_file()}
                change(target)
                after = {str(p.relative_to(target)): r6.sha(p) for p in target.rglob('*') if p.is_file()}
                require(before != after, 'mutation matched nothing')
                rows = events.read(target/'events.ndjson')
                rows[-1]['payload']['verdict_sha256'] = r6.sha(target/'verdict.json')
                (target/'events.ndjson').write_bytes(rehash(rows))
                episode.seal(target, retained_sources=contract.RETAINED_SOURCES)
                result = rejected(lambda: auditor.audit(target, r6.D1), expected)
                return {**result, 'coherently_resealed': True,
                    'changed_artifacts': sorted(k for k in before.keys()|after.keys() if before.get(k) != after.get(k))}
        suite.case(name, test)
    mutate('changed_prompt_file', lambda p: (p/'prompt.txt').write_text('Return JSON.\n'), 'semantic prompt changed')
    mutate('changed_prompt_binding', lambda p: edit(p, 'request.json', lambda x: x['binding'].update(prompt_sha256='0'*64)), 'request differs')
    def wire_mutation(target, case):
        request = (target/'request.json').read_bytes()
        raw = (target/'response.json').read_bytes()
        require(wire.echo(raw, request)['accepted'] is True)
        outbound = harness.serialized_arguments(wire.arguments(request), request, case)
        for name in ['serialized-envelope.json', 'stages/proposal-1/output/received-envelope.json']:
            (target/name).write_bytes(outbound)
        # Update transport hashes/counts too: rejection must be about semantic
        # content, not a stale hash, changed length, or broken receipt chain.
        edit(target, 'stages/proposal-1/output/transmission.json', lambda x: x.update(bytes=len(outbound)))
        def changed(rows):
            for row in rows:
                if row['event'] == 'envelope_serialized': row['payload'].update(serialized_envelope_sha256=wire.sha(outbound), bytes=len(outbound))
                if row['event'] == 'transmission_observed': row['payload'].update(captured_envelope_sha256=wire.sha(outbound), bytes=len(outbound))
                if row['event'] == 'transport_validated': row['payload']['outbound_envelope']['captured_envelope_sha256'] = wire.sha(outbound)
        log_change(target, changed)
        edit(target, 'transport-validation.json', lambda x: x['outbound_envelope'].update(captured_envelope_sha256=wire.sha(outbound)))
        edit(target, 'verdict.json', lambda x: x['transport_validation']['outbound_envelope'].update(captured_envelope_sha256=wire.sha(outbound)))
    mutate('altered_body_passing_echo', lambda p: wire_mutation(p, 'altered_body'), 'Serialized messages differ')
    mutate('omitted_serialized_prompt', lambda p: wire_mutation(p, 'omitted_prompt'), 'Serialized messages differ')
    mutate('capture_only_mutation', lambda p: (p/'stages/proposal-1/output/received-envelope.json').write_bytes(b'{}\n'), 'capture differs')
    mutate('wrong_messages', lambda p: edit(p, 'messages.json', lambda x: x[0].update(content='Changed')), 'recorded messages differ')
    mutate('wrong_client_arguments', lambda p: edit(p, 'client-arguments.json', lambda x: x['messages'].pop(0)), 'client arguments differ')
    mutate('wrong_transmission_receipt', lambda p: edit(p, 'stages/proposal-1/output/transmission.json', lambda x: x.update(completed=False)), 'transmission receipt mismatch')
    def remove_transmission(rows):
        indices = [i for i, row in enumerate(rows) if row['event'] == 'transmission_observed']
        require(len(indices) == 1); rows.pop(indices[0])
    mutate('missing_transmission_event', lambda p: log_change(p, remove_transmission), 'supervisor receipts')
    def wrong_mount(spec):
        indices = [i for i, arg in enumerate(spec['argv']) if arg == '/wire.json']
        require(len(indices) == 1); spec['argv'][indices[0]-1] = str(r6.D1.path/'Pristine.lean')
    mutate('wrong_request_mount', lambda p: edit(p, 'stages/proposal-1/command.json', wrong_mount), 'receiver command')
    mutate('unsafe_receiver_flag', lambda p: edit(p, 'stages/proposal-1/command.json', lambda x: x['argv'].remove('--unshare-all')), 'receiver command')
    mutate('wrong_budget', lambda p: edit(p, 'stages/proposal-1/command.json', lambda x: x.update(cpu_seconds=2)), 'limit receipt mismatch')
    mutate('unknown_usage_as_zero', lambda p: edit(p, 'accounting.json', lambda x: x['reported_usage'].update(total_tokens=0)), 'accounting differs')
    mutate('hidden_retry', lambda p: edit(p, 'accounting.json', lambda x: x.update(attempts_reserved=2)), 'accounting differs')
    mutate('hidden_fallback', lambda p: edit(p, 'search-policy.json', lambda x: x.update(fallback_routes=['cvc4'])), 'frozen envelope policy')
    mutate('wrong_proposer', lambda p: edit(p, 'verdict.json', lambda x: x.update(witness_proposer='sdk_synthesis')), None)
    mutate('wrong_assembler', lambda p: edit(p, 'verdict.json', lambda x: x.update(certificate_assembler='model')), None)
    def witness(target):
        edit(target, 'evidence.json', lambda x: x['certificate']['payload']['witness_data']['coefficients'][0].update(coefficient='5'))
        shutil.copyfile(target/'evidence.json', target/'stages/assembly/output/evidence.json')
    mutate('wrong_witness', witness, 'assembled witnesses differ')
    def route(rows):
        selected = [row for row in rows if row['source'] == 'supervisor' and row['event'] == 'recovery_finished']
        require(len(selected) == 1); selected[0]['payload']['route'] = 'bounded_enumeration'
    mutate('wrong_recovery', lambda p: log_change(p, route), 'recovery finish attribution')
    mutate('extra_attestation_claim', lambda p: edit(p, 'transport-validation.json', lambda x: x.update(model_input_verified=True)), 'transport checks differ')
    mutate('missing_receiver_source', lambda p: (p/'provenance/envelope-harness/validate/envelope_receiver.c').unlink(), 'artifact not retained')
    mutate('wrong_new_source', lambda p: (p/'provenance/envelope-harness/envelope_payload.py').write_text('# changed\n'), 'envelope harness source differs')
    mutate('wrong_old_source', lambda p: (p/'provenance/harness/proposal_episode.py').write_text('# changed\n'), 'downstream harness source differs')
    mutate('late_failure_marker', lambda p: r6.write_json(p/'failure.json', {'accepted': False}), 'failure marker')
    def current_independence():
        original_sha = r6.sha
        # Frozen prompt/policy/schema are protocol inputs, not mutable launcher code.
        live = {r6.ROOT/name for name in (*overlay.source_lock(), *contract.source_lock()) if name.endswith(('.py', '.c', '.ml', '.lean'))}
        def guarded(path):
            require(Path(path) not in live, 'audit consulted mutable launcher source bytes')
            return original_sha(path)
        with mock.patch.object(r6, 'sha', side_effect=guarded):
            require(auditor.audit(root/'d1_valid', r6.D1)['accepted'])
        return 'Source identity uses frozen locks and saved bytes; protocol inputs and audit implementation remain trusted'
    suite.case('current_source_independence', current_independence)
    for name, source, task in [('legacy_broker_v1', 'golden-broker-v1', r6.D1), ('legacy_broker_v2', 'golden-broker-v2', r6.D1),
        ('legacy_broker_v3', 'golden-broker-v3', r6.D1), ('legacy_c8_v1', 'golden-c8-v1', r6.C8),
        ('legacy_d1_fixture', 'proposal-checkpoint-v2/d1_valid', r6.D1), ('legacy_c8_fixture', 'proposal-checkpoint-v2/c8_valid', r6.C8)]:
        suite.case(name, lambda s=source, t=task: {'accepted': episode.audit(r6.ROOT/'runs'/s, t)['accepted']})
    def preservation():
        records = r6.read_json(root/'prior-artifacts.sha256.json')
        require(all((instrument.REPO/p).is_file() and r6.sha(instrument.REPO/p) == h for p, h in records.items()), 'prior artifacts changed')
        return {'checked_files': len(records), 'changed': 0, 'missing': 0, 'git_base': '79a4a07'}
    suite.case('prior_artifacts_preserved', preservation)
    suite.finish()


def snapshot(root):
    # Compare with committed bytes, including R6-001. Never bless an already
    # modified working tree. Excludes documentation that this checkpoint appends.
    base = '79a4a07'
    paths = ['experiments/r6/tasks', 'experiments/r6/runs', 'experiments/c1-cert-recovery',
             'experiments/r6/policies', 'experiments/r6/schema', *['experiments/r6/'+p for p in overlay.source_lock()]]
    entries = subprocess.check_output(['git', '-C', str(instrument.REPO), 'ls-tree', '-rz', base, '--', *paths])
    records, blobs = {}, {}
    process = subprocess.Popen(['git', '-C', str(instrument.REPO), 'cat-file', '--batch'], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    try:
        for entry in entries.split(b'\0'):
            if not entry: continue
            info, name = entry.split(b'\t', 1)
            _, kind, oid = info.split()
            require(kind == b'blob', 'non-file in artifact snapshot')
            if oid not in blobs:
                process.stdin.write(oid+b'\n'); process.stdin.flush()
                header = process.stdout.readline().split()
                require(header[0] == oid and header[1] == b'blob')
                content = process.stdout.read(int(header[2])); require(process.stdout.read(1) == b'\n')
                blobs[oid] = wire.sha(content)
            records[name.decode()] = blobs[oid]
    finally:
        process.stdin.close(); process.stdout.close(); require(process.wait() == 0)
    r6.write_json(root/'prior-artifacts.sha256.json', records)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir', type=Path, required=True)
    parser.add_argument('--units-only', action='store_true')
    args = parser.parse_args()
    root = args.run_dir.resolve(); root.mkdir(parents=True, exist_ok=False)
    r6.write_json(root/'checkpoint.json', {'passed': False})
    contract.verify_live_sources()
    units(root)
    if args.units_only: return
    snapshot(root)
    native(root)
    audits(root)
    suites = ['prompt-transport.json', 'native-envelopes.json', 'envelope-audits.json']
    r6.write_json(root/'checkpoint.json', {'passed': True, 'live_model_calls': 0,
        'scope': 'local canned transport; no provider SDK, remote receipt, compilation or inference attestation',
        'prompt_sha256': r6.sha(contract.PROMPT), 'policy_sha256': r6.sha(contract.CONFIG), 'source_lock_sha256': r6.sha(contract.LOCK),
        'suites': {name: {'sha256': r6.sha(root/name), 'count': r6.read_json(root/name)['check_count']} for name in suites}})


if __name__ == '__main__':
    main()
