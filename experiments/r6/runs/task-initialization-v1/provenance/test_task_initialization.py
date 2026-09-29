#!/usr/bin/env python3
"""Task admission regressions; no Lean, solver, or model execution.

Temporary freeze tests use recorded environments and a mocked Git-object read
for the configurable VerInf reference. Two native positive controls exercise
the actual task receipt -> systemd/bubblewrap -> resource monitor path.
"""
import argparse
from collections import Counter
from contextlib import redirect_stderr
from dataclasses import replace
import importlib.util
import inspect
import io
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from unittest.mock import patch

import audit_episode
import c8_control
import episode
import events
import instrument
import run as r6

EXPECTED_CASES = frozenset({
    'first_missing', 'first_empty', 'first_unknown', 'archived_silent_default',
    'd1_receipt_identity', 'c8_receipt_identity',
    'stage_missing_log', 'stage_empty_log', 'stage_unknown_task', 'stage_closed_log',
    'internal_task_arguments_required', 'third_task_freeze_rejected',
    'd1_freeze_dispatch', 'c8_freeze_dispatch', 'c8_explicit_checkout',
    'c8_wrong_model_definition', 'c8_missing_checkout_argument', 'c8_frozen_cli_guard',
    'd1_native_stage', 'c8_native_stage',
})


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def rejected(action, fragment, exception=ValueError):
    try:
        action()
    except exception as error:
        require(fragment in str(error), f'Wrong rejection: {error}')
        return str(error)
    raise AssertionError('Invalid operation was accepted')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir', type=Path, required=True)
    args = parser.parse_args()
    out = args.run_dir.resolve()
    out.mkdir(parents=True, exist_ok=False)
    report = {'suite_version': 'r6-task-initialization-1', 'passed': False,
              'expected_cases': sorted(EXPECTED_CASES), 'checks': [],
              'scope': 'task initialization, temporary freeze plumbing, two native positive stages; no kernel replay'}
    r6.write_json(out/'tests.json', report)

    def record(name, observed):
        require(name in EXPECTED_CASES and not any(r['case'] == name for r in report['checks']),
                f'Unexpected or duplicate case: {name}')
        report['checks'].append({'case': name, 'passed': True, 'observed': observed})
        r6.write_json(out/'tests.json', report)

    with tempfile.TemporaryDirectory(prefix='r6-task-init-') as temp:
        temp = Path(temp)
        for name, supplied, message in [
            ('first_missing', {}, 'First event requires an explicit task_id'),
            ('first_empty', {'task_id': ''}, 'Unregistered R6 task'),
            ('first_unknown', {'task_id': 'unregistered-control'}, 'Unregistered R6 task'),
        ]:
            run = temp/name
            run.mkdir()
            error = rejected(lambda: events.append(run, 'tests', 'tests_started', {}, **supplied), message)
            require(not list(run.iterdir()), 'Rejected initialization wrote files')
            record(name, {'error': error, 'no_files_written': True})

        # Demonstrate the reported defect against the preserved implementation.
        old_path = r6.ROOT/'reviews/2026-09-08/before/events.py'
        spec = importlib.util.spec_from_file_location('archived_events', old_path)
        old = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(old)
        run = temp/'archived'
        run.mkdir()
        old.append(run, 'tests', 'tests_started', {})
        row = old.read(run/'events.ndjson')[0]
        require(row['task_id'] == r6.D1.id, 'Archived default regression did not reproduce')
        record('archived_silent_default', {'implicit_task_id': row['task_id'], 'source_sha256': r6.sha(old_path)})

        for label, task, other in [('d1', r6.D1, r6.C8), ('c8', r6.C8, r6.D1)]:
            run = temp/label
            run.mkdir()
            events.append(run, 'tests', 'tests_started', {}, task_id=task.id)
            events.append(run, 'tests', 'observation', {})
            before = (run/'events.ndjson').read_bytes()
            error = rejected(lambda: events.append(run, 'tests', 'observation', {}, task_id=other.id),
                             'Cannot change task identity')
            require((run/'events.ndjson').read_bytes() == before, 'Identity rejection appended a receipt')
            rows = events.read(run/'events.ndjson')
            require(len(rows) == 2 and all(r['task_id'] == task.id for r in rows), 'Identity was not inherited')
            record(label+'_receipt_identity', {'explicit_then_inherited': task.id, 'conflict': error,
                                               'rejection_preserved_log': True})

        for name, message in [('stage_missing_log', 'initialized task receipt log'),
                              ('stage_empty_log', 'initialized task receipt log'),
                              ('stage_unknown_task', 'Unregistered R6 task'),
                              ('stage_closed_log', 'Episode is already closed')]:
            run = temp/name
            run.mkdir()
            if name == 'stage_empty_log':
                (run/'events.ndjson').touch()
            elif name in {'stage_unknown_task', 'stage_closed_log'}:
                events.append(run, 'tests', 'tests_started', {}, task_id=r6.C8.id)
                if name == 'stage_unknown_task':
                    row = events.read(run/'events.ndjson')[0]
                    row['task_id'] = 'unregistered-control'
                    del row['event_hash']
                    row['event_hash'] = events.digest(row)
                    (run/'events.ndjson').write_bytes(events.canonical(row)+b'\n')
                else:
                    events.append(run, 'tests', 'tests_finished', {})
            with patch.object(episode, 'libraries', side_effect=AssertionError('Launch preparation was entered')):
                error = rejected(lambda: episode.stage(run, 'unused', Path('/unused'), [], []), message)
            require(not (run/'stages').exists(), 'Invalid stage created records')
            record(name, {'error': error, 'rejected_before_stage_creation': True})

        functions = [r6.policy, r6.instrument, r6.trusted_sources, r6.build_tools,
                     r6.environment, r6.finalize_freeze, r6.frozen_task, r6.compile_and_export,
                     episode.local_policy, episode.final_validation, episode.golden,
                     instrument.build, instrument.broker_capture_source, audit_episode.verify]
        checked = []
        for function in functions:
            params = inspect.signature(function).parameters
            supplied = {name: None for name, p in params.items()
                        if name != 'task' and p.default is inspect.Parameter.empty}
            rejected(lambda: function(**supplied), 'task', TypeError)
            checked.append(function.__module__+'.'+function.__name__)
        record('internal_task_arguments_required', checked)

        third = replace(r6.C8, id='third-control', path=temp/'third')
        with patch.object(r6, 'toolchain', side_effect=AssertionError('Toolchain was entered')), \
             patch.object(c8_control, 'enrich_manifest', side_effect=AssertionError('C8 enrichment was entered')):
            error = rejected(lambda: r6.finalize_freeze(temp, third), 'No freeze implementation')
        require(not third.path.exists(), 'Unknown freeze task wrote files')
        record('third_task_freeze_rejected', error)

        # Exercise actual manifest construction/validation on disposable copies.
        # Inventory/build observations are fixed fixtures, not fresh Lean evidence.
        for label, task in [('d1', r6.D1), ('c8', r6.C8)]:
            root = temp/(label+'-freeze')
            shutil.copytree(task.path, root, ignore=shutil.ignore_patterns('manifest.json', '__pycache__'))
            candidate = replace(task, path=root, capture=root/'Capture.lean' if task == r6.C8 else task.capture)
            expected = r6.read_json(root/'expected.json')
            with patch.object(r6, 'toolchain', return_value=Path('/fixture-toolchain')), \
                 patch.object(r6, 'environment', return_value=([], '', expected['environment'])), \
                 patch.object(r6, 'inventory', return_value={}), \
                 patch.object(c8_control, 'C8', candidate if task == r6.C8 else r6.C8), \
                 patch.object(c8_control, 'enrich_manifest', wraps=c8_control.enrich_manifest) as enrich:
                r6.finalize_freeze(temp, candidate)
                require(enrich.call_count == int(task == r6.C8), 'Wrong enrichment dispatch')
            manifest, _ = r6.frozen_task(candidate)
            record(label+'_freeze_dispatch', {'task_id': manifest['task_id'], 'schema': manifest['schema_version'],
                                             'c8_enrichment_calls': enrich.call_count, 'inventory_is_fixture': True})

        root = temp/'unfrozen-c8'
        root.mkdir()
        shutil.copyfile(r6.C8.path/'Pristine.lean', root/'Pristine.lean')
        candidate = replace(r6.C8, path=root, capture=root/'Capture.lean')
        checkout = temp/'chosen VerInf checkout'
        model = (r6.C8.path/'source/Model.lean').read_bytes()
        requested = ['git', '-C', str(checkout), 'show', f'{c8_control.MODEL_COMMIT}:{c8_control.MODEL_PATH}']
        real_check_output = subprocess.check_output
        calls = []

        def git_object(argv, **kwargs):
            if argv[:3] == requested[:3]:
                require(argv == requested, 'Model read was not pinned to the expected commit and path')
                calls.append(argv)
                return model
            return real_check_output(argv, **kwargs)

        with patch.object(c8_control, 'C8', candidate), patch.object(subprocess, 'check_output', git_object):
            c8_control.prepare(model_repo=checkout)
        require(calls == [requested] and (root/'source/Model.lean').read_bytes() == model,
                'Preparation did not use the requested checkout')
        provenance = r6.read_json(root/'source-provenance.json')
        require(provenance == r6.read_json(r6.C8.path/'source-provenance.json'), 'Portable preparation changed source provenance')
        record('c8_explicit_checkout', {'git_argv': requested, 'git_model_read_mocked': True,
                                       'model_sha256': r6.sha(root/'source/Model.lean'), 'provenance_unchanged': True})
        with patch.object(subprocess, 'check_output', return_value=b'def P : Nat := 0\n'):
            error = rejected(lambda: c8_control.read_model_reference(checkout), 'Original field definition differs')
        record('c8_wrong_model_definition', error)

        stderr = io.StringIO()
        with patch.object(sys, 'argv', ['run.py', 'freeze', '--task', r6.C8.id]), \
             patch.object(r6, 'get_task', return_value=candidate), \
             patch.object(c8_control, 'prepare', side_effect=AssertionError('Preparation was entered')), \
             patch.object(r6, 'build_tools', side_effect=AssertionError('Build was entered')), redirect_stderr(stderr):
            error = rejected(r6.main, '2', SystemExit)
        require('requires --verinf-repo' in stderr.getvalue(), 'CLI rejected for the wrong reason')
        record('c8_missing_checkout_argument', {'exit_code': error, 'diagnostic': stderr.getvalue()})
        with patch.object(sys, 'argv', ['run.py', 'freeze', '--task', r6.C8.id]), \
             patch.object(r6, 'build_tools', side_effect=AssertionError('Build was entered')):
            error = rejected(r6.main, 'Task is already frozen')
        record('c8_frozen_cli_guard', error)

    # Both identities must survive actual monitor appends without task arguments.
    fixture = out/'fixture'
    fixture_source = out/'resource_fixture.c'
    shutil.copyfile(r6.ROOT/'validate/resource_fixture.c', fixture_source)
    subprocess.run(['cc', '-O0', str(fixture_source), '-o', str(fixture)], check=True)
    for label, task in [('d1', r6.D1), ('c8', r6.C8)]:
        run = out/(label+'-native')
        run.mkdir()
        events.append(run, 'tests', 'tests_started', {}, task_id=task.id)
        episode.stage(run, 'normal', fixture, ['normal'], [], wall=5, cpu=1, memory=192*1024**2)
        stats = r6.read_json(run/'stages/normal/normal.process.json')
        require(stats['exit_code'] == 0 and stats['resource_exhausted'] is None
                and stats['monitor_error'] is None and stats['observation_error'] is None
                and stats['workload_empty_after_cleanup'] is True, 'Native positive control failed')
        rows = events.read(run/'events.ndjson')
        require([r['event'] for r in rows] == ['tests_started', 'stage_started', 'stage_finished']
                and all(r['task_id'] == task.id for r in rows), 'Monitor lost the task identity')
        events.append(run, 'tests', 'tests_finished', {'passed': True})
        record(label+'_native_stage', {'task_id': task.id, 'process': stats})

    counts = Counter(r['case'] for r in report['checks'])
    require(set(counts) == EXPECTED_CASES and all(n == 1 for n in counts.values())
            and all(r['passed'] is True for r in report['checks']), 'Incomplete or failed initialization suite')
    sources = ['test_task_initialization.py', 'run.py', 'task_spec.py', 'c8_control.py',
               'events.py', 'episode.py', 'supervise.py', 'instrument.py', 'audit_episode.py',
               'reviews/2026-09-08/before/events.py',
               *['schema/'+p.name for p in sorted((r6.ROOT/'schema').glob('*.json'))],
               'tasks/c1-c8-2p18/source-provenance.json']
    for name in sources:
        target = out/'provenance'/name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(r6.ROOT/name, target)
    report['fixture_sha256'] = r6.sha(fixture)
    report['artifact_sha256'] = {str(p.relative_to(out)): r6.sha(p) for p in sorted(out.rglob('*'))
                                if p.is_file() and p.name not in {'fixture', 'tests.json'}}
    report['passed'] = True
    r6.write_json(out/'tests.json', report)
    print(f'{len(report["checks"])} task initialization checks passed: {out}/tests.json')


if __name__ == '__main__':
    main()
