#!/usr/bin/env python3
"""Controls for the R6-011/R6-012 site tasks, request policy C and representability classification (revision 2). No provider call; no Lean compilation except
the retained classification runs being read.

Each case rejects at the intended relationship: the site stage differs from the frozen stage by exactly the supervisor line;
the supervisor shim runs the frozen supervisor; only verified, reviewed primary sites enter the registry and the controls keep
theirs; the site instrumentation is the census form renamed as the frozen compile step renames it; the preparation helper is
the frozen overlay applied to the site helper; the site environment equals the D1 control's; the exact Farkas solver finds
known certificates and none for feasible systems; every recorded classification is recomputed from its retained run; the
denominator is the reviewed fifteen; line 70's prepared problem is the D1 control's, byte for byte. Revision 2 adds: rows
addressed by index, with distinct rows sharing a name found arithmetically and refused by name; every nonexistence claim
backed by an exhibited point; policy C's negation, derived omissions, row comparison, unique references and single neg_goal;
the exposure addendum bound by its bytes; and revision 1 retained, differing only in l178's arithmetic verdict.
"""
import argparse
import copy
import difflib
import inspect
import json
from pathlib import Path
import shutil
import tempfile
from unittest.mock import patch

import census
import episode
import events
import payload
import proposal_instrument as overlay
import run as r6
import site_freeze
import site_representability as rep
import site_request
import site_stage
import site_task
import supervise
import task_spec
from test_proposals import Suite, rejected, require

CASES = '''site_stage_differs_by_the_supervisor_line supervisor_shim_runs_frozen_main registry_admits_only_verified_primary_sites
registered_controls_unchanged instrumentation_is_the_census_form_renamed preparation_helper_is_the_frozen_overlay
site_environment_equals_d1 farkas_solver_exact classification_recomputed_from_retained_runs denominator_preserved
policy_c_admission certificates_and_points_checked_against_retained_rows line70_prepared_problem_is_the_d1_control
revision_one_retained_and_corrected'''.split()
RUNS = rep.RUNS
OLD_RUNS = r6.ROOT/'census-runs/representability-v1'
DECISION = r6.ROOT/'reviews/2026-09-22/R6-011-CONTRACT-DECISION.json'
D1_RUN = r6.ROOT/'cohort-runs-v3/r1-d1-draw1'


def controls(output):
    suite = Suite(output, CASES); summary = r6.read_json(RUNS/'representability.json')

    def one_line():
        base = inspect.getsource(episode.stage).splitlines(); site = inspect.getsource(site_stage.stage).splitlines()
        diff = [l for l in difflib.unified_diff(base, site, lineterm='', n=0) if l[:1] in '+-' and not l.startswith(('+++', '---'))]
        require(diff == ["-             sys.executable, str(ROOT/'supervise.py'), str(records/'command.json')]",
                         "+             sys.executable, str(ROOT/'site_supervise.py'), str(records/'command.json')]"], str(diff))
        require(site_stage.ROOT == episode.ROOT and site_stage.libraries is episode.libraries and site_stage.StageFailure is episode.StageFailure)
        return {'changed_lines': 1}
    suite.case('site_stage_differs_by_the_supervisor_line', one_line)

    def shim():
        text = (r6.ROOT/'site_supervise.py').read_text()
        require(text.count('sys.exit(supervise.main(sys.argv[1]))') == 1 and text.count('site_task.register_primary()') == 1)
        body = [l.strip() for l in text.split("if __name__ == '__main__':")[1].strip().splitlines()]
        require(body == ['site_task.register_primary()', 'sys.exit(supervise.main(sys.argv[1]))'], str(body))
        require(r6.sha(r6.ROOT/'supervise.py') == r6.read_json(r6.ROOT/'policies/fixture-harness-v1.sha256.json')['supervise.py'], 'frozen supervisor changed')
        return {'shim': 'register verified primary sites, then the frozen supervise.main'}
    suite.case('supervisor_shim_runs_frozen_main', shim)

    def registry():
        rejected(lambda: site_task.get('bracket-l999'), 'Unknown census site')
        with tempfile.TemporaryDirectory() as temp:  # a tampered site copy is refused before registration
            copy = Path(temp)/'census-v1'; shutil.copytree(site_task.CENSUS_DIR, copy)
            m = json.loads((copy/'bracket-l069/manifest.json').read_bytes()); m['captured_target'] = 'altered'
            (copy/'bracket-l069/manifest.json').write_text(json.dumps(m))
            with patch.object(site_task, 'CENSUS_DIR', copy), patch.object(site_task, 'ADDENDUM', copy/'exposure-addendum.json'):
                task = site_task.SiteTask(next(s for s in census.census()['sites'] if s['site_id'] == 'bracket-l069'))
                rejected(lambda: site_task.frozen_site(task), 'manifest differs from the reviewed one')
            c = json.loads((copy/'exposure-addendum.json').read_bytes()); c['decision_sha256'] = '0'*64
            (copy/'exposure-addendum.json').write_text(json.dumps(c))
            (copy/'bracket-l069/manifest.json').write_bytes((site_task.CENSUS_DIR/'bracket-l069/manifest.json').read_bytes())
            with patch.object(site_task, 'CENSUS_DIR', copy), patch.object(site_task, 'ADDENDUM', copy/'exposure-addendum.json'):
                rejected(lambda: site_task.frozen_site(task), 'exposure addendum bytes differ')
            x = json.loads((site_task.CENSUS_DIR/'exposure-addendum.json').read_bytes()); x['sites']['bracket-l069']['class'] = 'none_recorded'
            (copy/'exposure-addendum.json').write_text(json.dumps(x))  # a coherent-looking addendum whose classifications changed
            with patch.object(site_task, 'CENSUS_DIR', copy), patch.object(site_task, 'ADDENDUM', copy/'exposure-addendum.json'):
                rejected(lambda: site_task.frozen_site(task), 'exposure addendum bytes differ')
        with patch.object(site_task, 'MEMBERSHIP_DECISION_SHA256', '0'*64):
            rejected(lambda: site_task.frozen_site(site_task.SiteTask(census.census()['sites'][0])), 'reviewed membership decision changed')
        before = dict(task_spec.TASKS)
        try:
            registered = site_task.register_primary()
            require([t.id for t in registered] == list(site_task.primary()) and all(task_spec.get(t.id) is t for t in registered))
            require(events.get_task('bracket-l204') is registered[-1], 'the event log sees the registration')
            imposter = site_task.SiteTask({**registered[0].entry, 'declaration': 'Bracket.other'})
            task_spec.TASKS['bracket-l069'] = imposter
            rejected(lambda: site_task.get('bracket-l069'), 'registry already holds a different task')
        finally:
            task_spec.TASKS.clear(); task_spec.TASKS.update(before)
        return {'unknown': 'rejected', 'tampered_manifest': 'rejected', 'unbound_addendum': 'rejected', 'changed_decision': 'rejected', 'registered': 15}
    suite.case('registry_admits_only_verified_primary_sites', registry)

    def controls_kept():
        before = {k: v for k, v in task_spec.TASKS.items()}
        require(site_task.get(r6.D1.id) is r6.D1 and site_task.get(r6.C8.id) is r6.C8)
        site_task.get('bracket-l070')
        require(task_spec.TASKS[r6.D1.id] is before[r6.D1.id] and task_spec.TASKS[r6.C8.id] is before[r6.C8.id])
        require((r6.ROOT/'task_spec.py').read_bytes() and r6.sha(r6.ROOT/'task_spec.py') == r6.read_json(r6.ROOT/'policies/fixture-harness-v1.sha256.json')['task_spec.py'])
        return {'controls': [r6.D1.id, r6.C8.id], 'registry_file': 'unchanged'}
    suite.case('registered_controls_unchanged', controls_kept)

    def instrumentation():
        data = census.pristine()
        for site_id in site_task.primary():
            task = site_task.get(site_id)
            for helper, tactic in (('PreparationCapture', 'r6_prepare'), ('ProposalCapture', 'r6_capture_proposal')):
                source = site_task.instrumented(task, helper, tactic)
                expected = site_freeze.instrument(data, task.site).decode().replace('import Capture\n', f'import {helper}\n').replace('r6_capture_human', tactic)
                require(source == expected and source.count(f'{tactic} "{task.local}" "{task.id}"') == 1 and source.count(f'import {helper}\n') == 1)
                diff = [l for l in difflib.unified_diff(data.decode().splitlines(), source.splitlines(), lineterm='', n=0) if l.startswith('@@')]
                require(len(diff) == 2, f'{site_id}: {len(diff)} hunks')
        with tempfile.TemporaryDirectory() as temp:
            root = site_task.compile_input(Path(temp), 'preparation-input', 'PreparationCapture', site_task.capture_source(site_task.get('bracket-l098'), True), site_task.get('bracket-l098'))
            retained = RUNS/'bracket-l098/preparation-input'
            require(sorted(p.name for p in root.iterdir()) == sorted(p.name for p in retained.iterdir())
                    and all((root/p.name).read_bytes() == p.read_bytes() for p in retained.iterdir()), 'recompiled input differs from the retained run input')
        return {'sites': 15, 'helpers': 2, 'hunks': 2, 'retained_input_reproduced': 'bracket-l098'}
    suite.case('instrumentation_is_the_census_form_renamed', instrumentation)

    def overlay_helper():
        task = site_task.get('bracket-l166')
        for preparation in (True, False):
            text = site_task.capture_source(task, preparation)
            require(text == overlay.capture_source(task, preparation) and task.capture == site_freeze.CAPTURE)
            tactic = 'r6_prepare' if preparation else 'r6_capture_proposal'
            require(f'elab "{tactic}" savedName:str siteId:str : tactic' in text and 'r6_capture_human' not in text)
            require(('R6_PREPARE_OUTPUT' in text) is preparation and ('proof_broker_term' in text) is (not preparation))
        return {'preparation': 'reifies then runs the human closer', 'proposal': 'proof_broker_term with the fixture adapter'}
    suite.case('preparation_helper_is_the_frozen_overlay', overlay_helper)

    def environment():
        site_task.same_environment()
        with tempfile.TemporaryDirectory() as temp:
            copy = Path(temp)/'census-v1'; shutil.copytree(site_task.CENSUS_DIR, copy)
            (copy/'lean-toolchain').write_text('leanprover/lean4:v0.0.0\n')
            with patch.object(site_task, 'CENSUS_DIR', copy): rejected(lambda: site_task.same_environment(), 'environment differs from D1')
        return {'files': ['upstream-lake-manifest.json', 'upstream-lakefile.toml', 'lean-toolchain', 'Pristine.lean', 'environment-inventory'], 'tampered': 'rejected'}
    suite.case('site_environment_equals_d1', environment)

    def solver():
        d1 = r6.read_json(D1_RUN/'prepared.json')['rows']; known = r6.read_json(D1_RUN/'validated-response.json')['witness']['coefficients']
        require(rep.check_certificate(d1, {c['hypothesis']: int(c['coefficient']) for c in known}))
        found = rep.primitive(rep.farkas(d1)); require(rep.check_indexed(d1, found))
        x = lambda n, rel, c, *terms: {'name': n, 'relation': rel, 'constant': str(c), 'terms': [{'variable': v, 'coefficient': str(k)} for v, k in terms]}
        feasible = [x('a', 'le', -1, ('x', 1)), x('neg_goal', 'le', 0, ('x', -1))]
        point = rep.feasible_point(feasible)
        require(rep.farkas(feasible) is None and point is not None and rep.check_point(feasible, point), 'a feasible system: no certificate, an exhibited point')
        with_eq = [x('e', 'eq', -3, ('x', -1), ('y', 1)), x('a', 'le', 0, ('y', 1)), x('neg_goal', 'le', 0, ('x', -1))]
        w = rep.primitive(rep.farkas(with_eq)); require(rep.check_indexed(with_eq, w) and w[0] < 0 and rep.feasible_point(with_eq) is None, str(w))
        require(not rep.check_certificate(feasible, {'a': 1, 'neg_goal': 1}) and not rep.check_certificate(with_eq, {'e': 1, 'a': -1, 'neg_goal': 1}))
        # the revision-1 defect: two distinct rows sharing a name. By index the contradiction is found; by name it is refused.
        shared = [x('this', 'le', 0, ('Zmax', 1), ('v', -1)), x('this', 'le', 0, ('Zmax', -1), ('v0', 1)), x('neg_goal', 'le', 1, ('v', 1), ('v0', -1))]
        ws = rep.primitive(rep.farkas(shared)); require(ws == {0: 1, 1: 1, 2: 1} and rep.check_indexed(shared, ws), str(ws))
        rejected(lambda: rep.check_certificate(shared, {'this': 1, 'neg_goal': 1}), 'ambiguous row names')
        return {'d1_known_witness': 'accepted', 'd1_found': found, 'feasible_point': {k: str(v) for k, v in point.items()},
                'equality_negative_multiplier': w, 'shared_name_by_index': ws, 'shared_name_by_name': 'refused'}
    suite.case('farkas_solver_exact', solver)

    def policy_c():
        x = lambda n, rel, c, *terms: {'name': n, 'relation': rel, 'constant': str(c), 'terms': [{'variable': v, 'coefficient': str(k)} for v, k in terms]}
        var = lambda n: {'node': 'Var', 'name': n}; app = lambda s, a, b: {'node': 'App', 'symbol': s, 'type_args': [], 'args': [a, b]}
        # negation: strictness and direction
        require(site_request.row('h', {'node': 'Not', 'operand': app('LE.le', var('a'), var('b'))}) == x('h', 'le', 1, ('a', -1), ('b', 1)), '¬ a ≤ b is b + 1 ≤ a')
        require(site_request.row('h', {'node': 'Not', 'operand': app('LT.lt', var('a'), var('b'))}) == x('h', 'le', 0, ('a', -1), ('b', 1)), '¬ a < b is b ≤ a')
        require(site_request.row('h', {'node': 'Not', 'operand': app('GE.ge', var('a'), var('b'))}) == x('h', 'le', 1, ('a', 1), ('b', -1)), '¬ a ≥ b is a + 1 ≤ b')
        require(site_request.row('neg_goal', {'node': 'Not', 'operand': app('LT.lt', var('a'), var('b'))}, True) == x('neg_goal', 'le', 1, ('a', 1), ('b', -1)), 'negated ¬ a < b is a < b')
        rejected(lambda: site_request.row('h', {'node': 'Not', 'operand': {'node': 'Eq', 'type': 'Int', 'left': var('a'), 'right': var('b')}}), 'Unsupported proposition')
        rejected(lambda: site_request.row('h', {'node': 'Not', 'operand': {'node': 'Not', 'operand': app('LE.le', var('a'), var('b'))}}), 'Unsupported proposition')
        # the frozen projection agrees wherever it applies
        for s in ('bracket-l069', 'bracket-l070', 'bracket-l071', 'bracket-l078', 'bracket-l204'):
            prepared = r6.read_json(RUNS/s/'prepared.json'); require(site_request.project(prepared['final_ir'])[0] == payload.arithmetic_rows(prepared['final_ir']), s)
        # omissions derived, not trusted; rows compared; references unique; one final neg_goal; canonical rows
        base = r6.read_json(RUNS/'bracket-l175/prepared.json'); refused = {}
        def attempt(label, change, code):
            p = copy.deepcopy(base); change(p)
            try: site_request.admit(p)
            except site_request.Refusal as refusal: require(refusal.code == code, f'{label}: {refusal.code}'); refused[label] = refusal.code; return
            raise AssertionError(label+' was admitted')
        attempt('sdk_omission_list_trusted', lambda p: p['farkas_omissions'].append('hrec'), 'policy_omissions_differ')
        attempt('omission_list_emptied', lambda p: p['farkas_omissions'].clear(), 'policy_omissions_differ')
        attempt('row_removed', lambda p: p['rows'].pop(2), 'policy_rows_differ')
        attempt('row_replaced', lambda p: p['rows'][2]['terms'][0].__setitem__('coefficient', '-2'), 'policy_rows_differ')
        attempt('negation_direction_flipped', lambda p: p['rows'][-1].__setitem__('constant', str(int(p['rows'][-1]['constant'])-1)), 'policy_rows_differ')
        def duplicate(p):
            p['final_ir']['context']['hypotheses'][2]['name'] = 'hz'; p['rows'] = site_request.project(p['final_ir'])[0]
        attempt('shared_name', duplicate, 'policy_ambiguous_reference')
        attempt('ambiguous_l178_as_emitted', lambda p: p.update(r6.read_json(RUNS/'bracket-l178/prepared.json')), 'policy_ambiguous_reference')
        def goal_named(p):
            p['final_ir']['context']['hypotheses'][0]['name'] = 'neg_goal'; p['rows'] = site_request.project(p['final_ir'])[0]
        attempt('second_neg_goal', goal_named, 'policy_ambiguous_reference')
        def zero_term(p):
            h = p['final_ir']['context']['hypotheses'][0]; h['shell'] = app('LE.le', {'node': 'NumLit', 'value': '0', 'type': 'Int'}, {'node': 'NumLit', 'value': '1', 'type': 'Int'})
            p['rows'] = site_request.project(p['final_ir'])[0]; p['rows'][0]['terms'] = [{'variable': 'z', 'coefficient': '0'}]
        attempt('zero_coefficient', zero_term, 'policy_rows_differ')
        rows, evidence = site_request.admit(base)
        require(rows == base['rows'] and evidence['omitted_names'] == ['hzh'] and evidence['source_fragment'] == 'LIA' and evidence['posed_fragment'] == 'LIA')
        require(site_request.admit(r6.read_json(RUNS/'bracket-l096/prepared.json'))[1]['source_fragment'] == 'UF')
        return {'negation': 'strictness and direction', 'frozen_projection_agrees': 5, 'refused': refused}
    suite.case('policy_c_admission', policy_c)

    def recomputed():
        results = {}
        for recorded in summary['results']:
            s = recorded['site_id']; run = RUNS/s
            seal = r6.read_json(run/'seal.json'); rows = events.read(run/'events.ndjson')
            require(seal['event_count'] == len(rows) and seal['last_event_hash'] == rows[-1]['event_hash'] and rows[-1]['event'] == 'episode_finished')
            require(all(r6.sha(run/k) == v for k, v in seal['retained_sha256'].items()) and summary['runs_sha256'][s] == r6.sha(run/'seal.json'))
            require(r6.read_json(run/'representability.json') == recorded)
            prepared_dir = run/'stages/preparation/output'
            if recorded['class'] in ('interface_refused', 'preparation_failed'):
                again = rep.failure_record(run)
                require(again == recorded['reason'] and not (run/'prepared.json').exists())
                require((recorded['class'] == 'interface_refused') == (again['stage'] == 'pipeline-prepare' and again['stderr_head'].startswith('Failure(')))
            else:
                require(r6.read_json(prepared_dir/'context.json') == r6.read_json(site_task.CENSUS_DIR/s/'context/local-context.json'))
                again = rep.classify(r6.read_json(run/'prepared.json'), r6.read_json(prepared_dir/'reification.json'))
                require({k: v for k, v in recorded.items() if k not in ('site_id', 'family', 'exposure_class', 'seconds')} == again, s)
            require(recorded['exposure_class'] == r6.read_json(site_task.ADDENDUM)['sites'][s]['class'] and recorded['family'] == site_task.get(s).family)
            results[s] = recorded['class']
        return results
    suite.case('classification_recomputed_from_retained_runs', recomputed)

    def denominator():
        require(summary['population'] == list(site_task.primary()) and summary['denominator'] == 15 == len(summary['results']))
        require(sorted(s for v in summary['classes'].values() for s in v) == sorted(summary['population']) and tuple(summary['classes']) == rep.CLASSES)
        decision = r6.read_json(DECISION)
        posable = sorted(summary['classes']['posable_certificate'] + summary['classes']['posable_negative_control'])
        require(posable == sorted(decision['candidate_learned_sites']) and summary['classes']['posable_negative_control'] == decision['arithmetic_feasible_negative_control']
                and summary['classes']['ambiguous_reference'] == decision['ambiguous_reference_unposable']
                and summary['classes']['interface_refused'] == decision['sdk_goal_form_unposable'], 'classes differ from the reviewed decision')
        return {c: len(v) for c, v in summary['classes'].items()}
    suite.case('denominator_preserved', denominator)

    def certificates():
        checked, points = [], []
        for r in summary['results']:
            path = RUNS/r['site_id']/'prepared.json'
            if not path.exists(): continue
            rows = r6.read_json(path)['rows']
            if r['arithmetic_certificate']:
                require(rep.check_indexed(rows, {c['index']: int(c['coefficient']) for c in r['certificate_rows']})
                        and all(rows[c['index']]['name'] == c['name'] for c in r['certificate_rows']), r['site_id'])
                if r['names_unique']: require(rep.check_certificate(rows, {c['hypothesis']: int(c['coefficient']) for c in r['certificate']}), r['site_id'])
                else: rejected(lambda: rep.check_certificate(rows, {c['name']: int(c['coefficient']) for c in r['certificate_rows']}), 'ambiguous row names')
                checked.append(r['site_id'])
            else:
                point = {k: rep.Fraction(v) for k, v in r['feasible_point'].items()}
                require(rep.check_point(rows, point) and rep.farkas(rows) is None, r['site_id']); points.append(r['site_id'])
        return {'certificates_checked_by_index': checked, 'feasible_points_checked': points}
    suite.case('certificates_and_points_checked_against_retained_rows', certificates)

    def line70():
        require(r6.read_json(RUNS/'bracket-l070/prepared.json') == r6.read_json(D1_RUN/'prepared.json'))
        require(r6.read_json(RUNS/'bracket-l070/input-ir.json') == r6.read_json(D1_RUN/'input-ir.json'))
        return {'prepared': 'equal', 'input_ir': 'equal', 'd1_run': str(D1_RUN.relative_to(r6.ROOT))}
    suite.case('line70_prepared_problem_is_the_d1_control', line70)

    def revision_one_retained():
        """Revision 1's runs are history: their prepared problems equal revision 2's, and only l178's arithmetic verdict changes."""
        old = r6.read_json(OLD_RUNS/'representability.json'); changed = []
        for r in old['results']:
            s = r['site_id']; p1, p2 = OLD_RUNS/s/'prepared.json', RUNS/s/'prepared.json'
            require(p1.exists() == p2.exists() and (not p1.exists() or p1.read_bytes() == p2.read_bytes()), s)
            new = next(x for x in summary['results'] if x['site_id'] == s)
            if p1.exists() and bool(r.get('sdk_rows_rational_certificate')) != new['arithmetic_certificate']: changed.append(s)
        require(changed == ['bracket-l178'], str(changed))
        return {'prepared_problems_equal': True, 'arithmetic_verdict_changed': changed}
    suite.case('revision_one_retained_and_corrected', revision_one_retained)
    suite.finish()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    controls(args.output)
    print(json.dumps({'passed': True, 'cases': len(CASES)}, indent=1))


if __name__ == '__main__':
    main()
