#!/usr/bin/env python3
"""Independent component controls for R6-004 outer-gate closeout.

Contract observations come from a passing original-tree recount. Each mutation
changes one relationship at a time on a disposable copy. These are additional
artifact controls, not native episodes or additions to the frozen 67 checks.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path.cwd() / 'experiments/r6'
sys.path.insert(0, str(ROOT))
import credential_audit
import run as r6
import test_credentials as tests
from test_proposals import Suite, rejected, require

CHECKPOINT = ROOT / 'runs/credential-checkpoint-v3'
CASES = '''contract_baseline source_lock_binding derivation_binding
representations_binding encoded_forms_binding live_calls_binding
native_disclosure_binding native_log_binding native_coverage_binding
preservation_substitution preservation_content preservation_suite_count
preservation_suite_base retained_only_scope'''.split()


def read(path):
    return json.loads(path.read_bytes())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def controls(output):
    gate = tests.load_recount()
    observations = gate.recount(CHECKPOINT)
    require(observations['passed'] is True and observations['total_checks'] == 61,
            'original content checkpoint did not pass')
    require(gate.gate_suite(CHECKPOINT)['count'] == 6, 'original gate suite did not pass')
    suite = Suite(output, CASES)

    def contract(copied):
        return gate.case_contract(copied, read(copied / 'checkpoint.json'), observations['episodes'])

    def rebind(copied, file):
        index = read(copied / 'checkpoint.json')
        index['suites'][file]['sha256'] = sha(copied / file)
        write(copied / 'checkpoint.json', index)

    def edit_record(copied, file, case, change):
        value = read(copied / file)
        selected = [c for c in value['checks'] if c['name'] == case]
        require(len(selected) == 1, 'mutation must select exactly one case')
        before = json.dumps(selected[0]['detail'], sort_keys=True)
        change(selected[0]['detail'])
        require(json.dumps(selected[0]['detail'], sort_keys=True) != before, 'mutation changed nothing')
        write(copied / file, value)
        rebind(copied, file)

    def probe(name, change, error, check=contract):
        def run():
            with tempfile.TemporaryDirectory(prefix='r6-closeout-component-') as td:
                copied = Path(td) / 'checkpoint'
                shutil.copytree(CHECKPOINT, copied)
                check(copied)
                change(copied)
                result = rejected(lambda: check(copied), error)
                return {**result, 'unmutated_component_passes': True}
        suite.case(name, run)

    def baseline():
        _, count, _ = contract(CHECKPOINT)
        require(count == 61)
        return {'content_checks': count, 'gate_checks': 6,
                'observation_scope': 'original trees independently re-audited before component mutations'}
    suite.case('contract_baseline', baseline)

    for name, field, value, message in [
            ('source_lock_binding', 'source_lock_sha256', '1' * 64, 'source-lock digest differs'),
            ('derivation_binding', 'canary_derivation', 'unregistered', 'authority: canary_derivation'),
            ('representations_binding', 'publication_representations', [], 'authority: publication_representations'),
            ('encoded_forms_binding', 'publication_encoded_forms', [], 'authority: publication_encoded_forms'),
            ('live_calls_binding', 'live_model_calls', 1, 'authority: live_model_calls')]:
        def alter(copied, field=field, value=value):
            index = read(copied / 'checkpoint.json')
            require(index[field] != value, 'declaration mutation matched nothing')
            index[field] = value
            write(copied / 'checkpoint.json', index)
        probe(name, alter, message)

    for name, field, value, message in [
            ('native_disclosure_binding', 'disclosures', 999, 'disclosure count differs'),
            ('native_log_binding', 'outer_log_clean', False, 'log result differs'),
            ('native_coverage_binding', 'coverage', {'recomputed': 0, 'recorded_not_recomputed': 0,
                                                    'files_scanned': 0}, 'coverage differs')]:
        def alter(copied, field=field, value=value):
            edit_record(copied, 'credential-native.json', 'd1_valid', lambda d: d.update({field: value}))
        probe(name, alter, message)

    def substituted(copied):
        file = copied / 'prior-artifacts.sha256.json'
        values = read(file)
        before = len(values)
        original = next(iter(values))
        replacement = 'experiments/r6/not-a-pinned-artifact.json'
        require(replacement not in values)
        values[replacement] = values.pop(original)
        require(len(values) == before, 'substitution changed the count')
        write(file, values)
    probe('preservation_substitution', substituted, 'pinned commit population', gate.verify_preservation)

    def wrong_content(copied):
        file = copied / 'prior-artifacts.sha256.json'
        values = read(file)
        original = next(iter(values))
        require(values[original] != '0' * 64)
        values[original] = '0' * 64
        write(file, values)
    probe('preservation_content', wrong_content, 'pinned commit content', gate.verify_preservation)

    for name, field, value in [('preservation_suite_count', 'checked_files', 0),
                               ('preservation_suite_base', 'git_base', '0000000')]:
        def alter(copied, field=field, value=value):
            edit_record(copied, 'credential-audits.json', 'prior_artifacts_preserved',
                        lambda d: d.update({field: value}))
        probe(name, alter, 'preservation suite record differs', gate.recount)

    def retained_scope():
        with tempfile.TemporaryDirectory(prefix='r6-closeout-retained-scope-') as td:
            copied = Path(td) / 'checkpoint'
            shutil.copytree(CHECKPOINT, copied)
            contract(copied)
            target = copied / 'd1_valid'
            shutil.rmtree(target)
            tests.retained_copy(CHECKPOINT / 'd1_valid', target)
            result = credential_audit.audit(target, r6.D1)
            require(result['accepted'] is True)
            require(result['coverage']['recorded_not_recomputed'] > 0,
                    'retained-only control omitted no original build product')
            publication = gate.publication_gate(copied)
            rejection = rejected(lambda: gate.case_contract(copied, read(copied / 'checkpoint.json'),
                                                              publication['episodes']), 'coverage differs')
            return {'retained_only_episode_accepted': True,
                    'original_coverage': observations['episodes']['d1_valid']['scan_coverage'],
                    'retained_only_coverage': result['coverage'],
                    'original_tree_contract_rejection': rejection,
                    'scope': 'complete checkpoint requires original-tree coverage; retained-only episode audit remains usable'}
    suite.case('retained_only_scope', retained_scope)
    suite.finish()


if __name__ == '__main__':
    output = Path(sys.argv[1])
    require(not output.exists(), 'refusing to overwrite an earlier review record')
    controls(output)
    print(json.dumps({'passed': True, 'cases': len(CASES),
                      'source_sha256': sha(Path(__file__)), 'output': str(output)}))
