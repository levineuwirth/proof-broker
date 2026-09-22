#!/usr/bin/env python3
"""Controls for the R6-010 census auditor: one relationship per mutation, on copies of the census and its retained freeze.

Every mutation is applied to a fresh copy that first passes the unmutated audit, and must be rejected at exactly the named
case. Records that commit to a mutated file by digest (manifest artifact and shared digests, census results) are rebound so
the rejection is the intended relationship, not an incidental hash mismatch. The control population is fixed and asserted.
Carried in: the review's three corrupted copies (R6-010-REVIEW-PROBES.json), each previously accepted by all eleven
non-native census controls, and the follow-up review's four (R6-010-FOLLOWUP-PROBES.json), each previously accepted by this
auditor at 127 cases.
"""
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import run as r6

spec = importlib.util.spec_from_file_location('r6_census_audit', Path(__file__).with_name('census_audit.py'))
audit = importlib.util.module_from_spec(spec); spec.loader.exec_module(audit)
J = lambda p: json.loads(Path(p).read_bytes())
W = lambda p, v: Path(p).write_text(json.dumps(v, sort_keys=True, indent=2, ensure_ascii=False)+'\n')
SHA = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
S = 'bracket-l069'
EXPECTED = {
    # the review's corrupted copies
    'wrong_challenge_export': f'{S}:challenge_export_bound',
    'false_local_type': f'{S}:replays_derived_from_raw_reports',
    'missing_required_artifact_binding': f'{S}:inventory_exact',
    # the review's narrower observations, as rejection boundaries
    'helper_added_logic': 'helper:exact_transformation',
    # one per remaining relationship
    'freeze_site_removed': 'population:exact_freeze_directory',
    'extra_file_in_census': 'population:exact_census_directory',
    'extra_file_in_site': f'{S}:inventory_exact',
    'retained_normalized_type_altered_coherently': f'{S}:replays_derived_from_raw_reports',
    'baseline_export_substituted': f'{S}:baseline_bound',
    'captured_context_altered_coherently': f'{S}:capture_inputs_and_context',
    'instrumented_source_altered': f'{S}:capture_inputs_and_context',
    'stage_exit_nonzero': f'{S}:stages_returned',
    'membership_site_dropped': 'membership:bound_to_census_and_decision',
    'exposure_premise_dropped': 'exposure:addendum_recomputed',
    'audit_case_removed': 'cases:population',
    # the follow-up review's corrupted copies (R6-010-FOLLOWUP-PROBES.json), each previously accepted
    'source_binding_other_family': f'{S}:replays_derived_from_raw_reports',
    'replay_wrong_solution_mount': f'{S}:commands_bound_to_roles',
    'replay_command_missing': f'{S}:evidence_inventory_exact',
    'extra_freeze_output': f'{S}:evidence_inventory_exact',
    # the remaining new boundaries
    'optional_export_differs': f'{S}:evidence_inventory_exact',
    'export_declarations_altered': f'{S}:commands_bound_to_roles',
    'checker_program_foreign': f'{S}:commands_bound_to_roles',
    'baseline_report_incomplete_coherently': 'baselines:family_exports_replayed',
}
CONTROLS = ('baseline', *EXPECTED)


def run_audit(census_dir, freeze_dir, capture=None):
    try: result = audit.audit(census_dir, freeze_dir, **({'capture': capture} if capture else {}))
    except audit.Rejection as rejection: return {'accepted': False, 'rejected_case': rejection.case}
    return {'accepted': result['accepted'], 'case_count': result['case_count']}


def rebind_manifest(census_dir, site, name):
    m = J(census_dir/site/'manifest.json'); m['artifacts_sha256'][name] = SHA(census_dir/site/name); W(census_dir/site/'manifest.json', m)


def mutate(name, census_dir, freeze_dir, temp):
    d = census_dir/S; w = freeze_dir/S
    if name == 'wrong_challenge_export':
        shutil.copyfile(census_dir/'bracket-l099/challenge.ndjson.gz', d/'challenge.ndjson.gz'); rebind_manifest(census_dir, S, 'challenge.ndjson.gz')
    elif name == 'false_local_type':
        e = J(d/'expected.json'); e['targets'][0]['type_sha256'] = '0'*64; W(d/'expected.json', e); rebind_manifest(census_dir, S, 'expected.json')
        c = J(census_dir/'census.json'); next(r for r in c['results'] if r['site_id'] == S)['local_type_sha256'] = '0'*64; W(census_dir/'census.json', c)
    elif name == 'missing_required_artifact_binding':
        m = J(d/'manifest.json'); del m['artifacts_sha256']['challenge.ndjson.gz']
        m['artifacts_sha256']['context/../expected.json'] = SHA(d/'expected.json'); W(d/'manifest.json', m)
    elif name == 'helper_added_logic':
        capture = temp/'CaptureSite.lean'; text = audit.site_freeze.CAPTURE.read_text()
        capture.write_text(text.replace('  setGoals []\n', '  setGoals []\n  logInfo "extra"\n', 1)); return capture
    elif name == 'freeze_site_removed': shutil.rmtree(freeze_dir/'bracket-l204')
    elif name == 'extra_file_in_census': (census_dir/'notes.txt').write_text('added\n')
    elif name == 'extra_file_in_site': (d/'context/extra.json').write_text('{}\n')
    elif name == 'retained_normalized_type_altered_coherently':  # the retained normalized report, expected and census agree; the raw report does not
        v = J(w/'challenge-validation/verdict.json'); v['targets'][0]['type_sha256'] = '1'*64; W(w/'challenge-validation/verdict.json', v)
        e = J(d/'expected.json'); e['targets'][0]['type_sha256'] = '1'*64; W(d/'expected.json', e); rebind_manifest(census_dir, S, 'expected.json')
        c = J(census_dir/'census.json'); next(r for r in c['results'] if r['site_id'] == S)['local_type_sha256'] = '1'*64; W(census_dir/'census.json', c)
    elif name == 'baseline_export_substituted':  # the lift_cell baseline replaced by another family's, every digest that names it rebound
        target = census_dir/'baseline-Bracket.lift_cell.ndjson.gz'
        shutil.copyfile(census_dir/'baseline-Bracket.threshold_unique.ndjson.gz', target)
        c = J(census_dir/'census.json'); c['baselines_sha256']['Bracket.lift_cell'] = SHA(target); W(census_dir/'census.json', c)
        for site in ('bracket-l069', 'bracket-l070', 'bracket-l071', 'bracket-l078'):
            m = J(census_dir/site/'manifest.json'); m['shared_artifacts_sha256']['baseline-Bracket.lift_cell.ndjson.gz'] = SHA(target); W(census_dir/site/'manifest.json', m)
    elif name == 'captured_context_altered_coherently':  # the site context, manifest and census result agree on a different target
        ctx = J(d/'context/local-context.json'); ctx['target'] = 'x.val + z.val ≤ 2 ^ 24 + 2 * Zmax'; W(d/'context/local-context.json', ctx)
        rebind_manifest(census_dir, S, 'context/local-context.json')
        m = J(d/'manifest.json'); m['captured_target'] = ctx['target']; W(d/'manifest.json', m)
        c = J(census_dir/'census.json'); next(r for r in c['results'] if r['site_id'] == S)['captured_target'] = ctx['target']; W(census_dir/'census.json', c)
    elif name == 'instrumented_source_altered':
        p = w/'challenge/input/Frozen.lean'; p.write_bytes(p.read_bytes().replace(b'by omega', b'by linarith', 1))
    elif name == 'stage_exit_nonzero':
        p = w/'challenge/export/export.process.json'; v = J(p); v['exit_code'] = 7; W(p, v)
    elif name == 'membership_site_dropped':
        m = J(census_dir/'membership.json'); m['primary'].remove('bracket-l204'); W(census_dir/'membership.json', m)
    elif name == 'exposure_premise_dropped':
        x = J(census_dir/'exposure-addendum.json'); x['sites'][S]['class'] = 'none_recorded'; x['sites'][S]['prior_input_premise'] = []
        W(census_dir/'exposure-addendum.json', x)
    elif name == 'source_binding_other_family':  # another family's accepted baseline report, raw and normalized together
        other = freeze_dir/'baseline-Bracket.threshold_unique/baseline-validation'
        for f in ('verdict.raw.json.gz', 'verdict.json'): shutil.copyfile(other/f, w/'source-binding-validation'/f)
    elif name == 'replay_wrong_solution_mount':
        def alter(argv):
            i = argv.index('/solution.ndjson'); assert argv[i-2] == '--ro-bind'; argv[i-1] = argv[i-1].replace('/bracket-l069/', '/bracket-l099/')
        command_edit(w/'challenge-validation/replay.command.json', alter)
    elif name == 'replay_command_missing': (w/'challenge-validation/replay.command.json').unlink()
    elif name == 'extra_freeze_output': (w/'challenge/output/unlisted.json').write_text('{}\n')
    elif name == 'optional_export_differs': (w/'challenge/output/proof.ndjson').write_bytes(b'{"not": "the frozen export"}\n')
    elif name == 'export_declarations_altered':
        def alter(argv):
            i = argv.index('Bracket.lift_cell.r6_site_l069'); argv[i] = 'Bracket.lift_cell.r6_site_l070'
        command_edit(w/'challenge/export/export.command.json', alter)
    elif name == 'checker_program_foreign':
        def alter(argv):
            i = argv.index('/runner/bin/program'); assert argv[i-2] == '--ro-bind'; argv[i-1] = '/tmp/r6-foreign/r6-replay'
        command_edit(w/'challenge-validation/replay.command.json', alter)
    elif name == 'baseline_report_incomplete_coherently':  # raw and normalized agree on an incomplete replay that still says accepted
        d = freeze_dir/'baseline-Bracket.lift_cell/baseline-validation'
        raw = json.loads(gzip.decompress((d/'verdict.raw.json.gz').read_bytes())); raw['stage'] = 'incomplete'
        (d/'verdict.raw.json.gz').write_bytes(gzip.compress(json.dumps(raw).encode()))
        v = J(d/'verdict.json'); v['stage'] = 'incomplete'; W(d/'verdict.json', v)
    else: raise AssertionError(name)
    return None


def command_edit(path, alter):
    record = J(path); before = list(record['argv']); alter(record['argv']); assert record['argv'] != before, 'vacuous mutation'
    W(path, record)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    results = {}
    for name in CONTROLS:
        with tempfile.TemporaryDirectory(prefix='r6-010-audit-controls-') as temp:
            temp = Path(temp); census_dir = temp/'census-v1'; freeze_dir = temp/'freeze-v1'
            shutil.copytree(audit.site_freeze.CENSUS_DIR, census_dir); shutil.copytree(ROOT/'census-runs/freeze-v1', freeze_dir)
            baseline = run_audit(census_dir, freeze_dir); assert baseline['accepted'] is True, baseline
            if name == 'baseline': results[name] = baseline; continue
            if name == 'audit_case_removed':
                original = audit.Audit.require
                def omit(self, ok, case, detail=''):
                    if case == f'{S}:challenge_export_bound': return
                    return original(self, ok, case, detail)
                with patch.object(audit.Audit, 'require', omit): observed = run_audit(census_dir, freeze_dir)
            else:
                capture = mutate(name, census_dir, freeze_dir, temp); observed = run_audit(census_dir, freeze_dir, capture)
            assert observed['accepted'] is False and observed['rejected_case'] == EXPECTED[name], (name, observed)
            results[name] = {'rejected': True, 'rejected_case': observed['rejected_case']}
            print(name, observed['rejected_case'], flush=True)
    assert tuple(results) == CONTROLS
    r6.write_json(args.output, {'passed': True, 'controls': len(results), 'expected_controls': list(CONTROLS), 'results': results,
                                'auditor_sha256': SHA(Path(__file__).with_name('census_audit.py')), 'program_sha256': SHA(Path(__file__)),
                                'live_model_calls': 0, 'credentials_read': 0, 'scope': 'temporary copies; one relationship per mutation; exact control population'})
    print(json.dumps({'passed': True, 'controls': len(results), 'baseline_cases': results['baseline']['case_count']}, indent=1))


if __name__ == '__main__':
    main()
