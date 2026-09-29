#!/usr/bin/env python3
"""Controls for the R6-010 census and site freeze. Read-only over the frozen census; one native negative through the real
freeze path (a site whose saved declaration name already exists) shows the exclusion record; no provider call.

Each case rejects at the intended relationship: the census is reproduced from the pristine bytes and nothing else; sites
are identified by byte span, never by line text; every form is classified by exactly one frozen pattern; the site helper
differs from the R6-000 helper only in its parameterization; the permitted modification is one token and one import;
every frozen site manifest binds its artifacts, its capture and its saved declaration; the generalized capture at line
70 reproduces the R6-000 control's obligation; families and exposure are recorded; the membership record partitions the
census and hash-binds it.
"""
import argparse
import difflib
import json
from pathlib import Path
import sys

import jsonschema

import census
import run as r6
import site_freeze
from test_proposals import Suite, rejected, require

CASES = '''census_reproduced_from_pristine_bytes comments_and_strings_are_not_sites site_identity_is_the_byte_span forms_classified_exactly_once
capture_helper_differs_only_by_parameterization permitted_modification_is_one_token_and_one_import site_manifests_bound
line70_reproduces_the_r6_000_control families_and_exposure_recorded membership_partitions_and_binds_the_census
exclusion_records_failing_stage_and_stderr freeze_bound_to_its_sources'''.split()
D1_CONTEXT = r6.D1.path/'context/local-context.json'


def controls(output):
    suite = Suite(output, CASES); record = census.census(); data = census.pristine()
    frozen = r6.read_json(site_freeze.CENSUS_DIR/'census.json')

    def reproduced():
        require(record['site_count'] == 15 and len(record['sites']) == 15 and record['pristine_sha256'] == census.SOURCE_HASH)
        require([(s['line'], s['column'], s['declaration'], s['form']) for s in record['sites']] == list(census.EXPECTED_SITES))
        require([s['site_id'] for s in record['sites']] == [f'bracket-l{l:03d}' for l, *_ in census.EXPECTED_SITES])
        # the same table from the same bytes, and a rejection when a site is removed or added
        require(census.census(data) == record)
        without = data.replace(b'    have hzh1 : 1 \xe2\x89\xa4 zhigh := by omega\n', b'    have hzh1 : 1 \xe2\x89\xa4 zhigh := by simp\n', 1); require(without != data)
        rejected(lambda: census.census(without), 'census population changed')
        added = data.replace(b'  intro a b hab\n', b'  intro a b hab\n  have : a \xe2\x89\xa4 b := by omega\n', 1); require(added != data)
        rejected(lambda: census.census(added), 'census population changed')
        return {'sites': 15, 'removed_site_rejected': True, 'added_site_rejected': True}
    suite.case('census_reproduced_from_pristine_bytes', reproduced)

    def masked():
        commented = data.replace(b'  intro a b hab\n', b'  intro a b hab\n  -- omega would close this\n  /- omega -/\n', 1)
        require(commented != data)
        require(len(census.extract(commented)) == 15, 'a commented omega became a site')
        quoted = data.replace(b'  intro a b hab\n', b'  intro a b hab\n  have _s : "omega" = "omega" := rfl\n', 1)
        require(len(census.extract(quoted)) == 15, 'a quoted omega became a site')
        # `omega` as part of a longer identifier is not the tactic
        named = data.replace(b'  intro a b hab\n', b'  intro a b hab\n  have omega_like : True := trivial\n', 1)
        require(len(census.extract(named)) == 15, 'an identifier containing omega became a site')
        return {'comment': 'masked', 'block_comment': 'masked', 'string': 'masked', 'identifier': 'not a token'}
    suite.case('comments_and_strings_are_not_sites', masked)

    def spans():
        bare = [s for s in record['sites'] if s['form'] == 'bare_goal']
        require(len(bare) == 4 and len({s['line_text'] for s in bare}) <= 2, 'bare omega lines repeat verbatim')
        require(len({(s['byte_span']['start'], s['byte_span']['end_exclusive']) for s in record['sites']}) == 15, 'spans are distinct')
        for s in record['sites']:
            require(data[s['byte_span']['start']:s['byte_span']['end_exclusive']] == b'omega')
            site = site_freeze.Site(s); out = site_freeze.instrument(data, site)
            require(out.count(b'r6_capture_human "') == 1 and out.count(b'omega') == data.count(b'omega')-1)
        wrong = site_freeze.Site({**record['sites'][0], 'byte_span': {'start': record['sites'][0]['byte_span']['start']+1, 'end_exclusive': record['sites'][0]['byte_span']['end_exclusive']+1}})
        rejected(lambda: site_freeze.instrument(data, wrong), 'span is not the token')
        return {'distinct_spans': 15, 'repeated_bare_lines': [s['line'] for s in bare], 'wrong_span_rejected': True}
    suite.case('site_identity_is_the_byte_span', spans)

    def forms():
        counts = {}
        for s in record['sites']:
            matches = [name for name, pattern in census.FORMS if pattern.match(s['line_text'])]
            require(matches and matches[0] == s['form'] and s['form'] != 'unclassified', f"{s['site_id']}: {matches}")
            counts[s['form']] = counts.get(s['form'], 0)+1
        require(counts == {'named_have': 5, 'bare_goal': 4, 'term_by': 1, 'have_post_simp': 1, 'inline_term': 2, 'post_simp': 1, 'anonymous_have': 1}, str(counts))
        return counts
    suite.case('forms_classified_exactly_once', forms)

    def helper():
        base = (r6.ROOT/'capture/Capture.lean').read_text().splitlines(); site = site_freeze.CAPTURE.read_text().splitlines()
        changed = [l for l in difflib.unified_diff(base, site, lineterm='', n=0) if l[:1] in '+-' and not l.startswith(('+++', '---'))]
        removed = [l[1:] for l in changed if l.startswith('-')]; added = [l[1:] for l in changed if l.startswith('+')]
        require(any('elab "r6_capture_human" : tactic' in l for l in removed) and any('elab "r6_capture_human" savedName:str siteId:str : tactic' in l for l in added))
        require(any('let name := `Bracket.lift_cell.r6_d1_70' in l for l in removed) and any('let name := savedName.getString.toName' in l for l in added))
        require(any('("task_id", "verinf-d1-70")' in l for l in removed) and any('("task_id", toJson siteId.getString)' in l for l in added))
        kept = [l for l in removed if not any(k in l for k in ('elab "r6_capture_human"', 'let name := `Bracket', '("task_id", "verinf-d1-70")')) and l.strip() and not l.strip().startswith(('/-', '--', 'Keep', 'from the task'))]
        require(kept == [], 'the site helper removed capture logic: '+str(kept))
        require(r6.sha(site_freeze.CAPTURE) == frozen['capture_sha256'])
        return {'signature': 'parameterized by saved name and site id', 'removed_logic_lines': 0, 'added_lines': len(added)}
    suite.case('capture_helper_differs_only_by_parameterization', helper)

    def one_token():
        for s in record['sites']:
            site = site_freeze.Site(s); out = site_freeze.instrument(data, site)
            diff = list(difflib.unified_diff(data.decode().splitlines(), out.decode().splitlines(), lineterm='', n=0))
            hunks = [l for l in diff if l.startswith('@@')]; minus = [l for l in diff if l.startswith('-') and not l.startswith('---')]
            plus = [l for l in diff if l.startswith('+') and not l.startswith('+++')]
            replaced = s['line_text'][:s['column']]+f'r6_capture_human "{s["saved_local_declaration"]}" "{s["site_id"]}"'+s['line_text'][s['column']+5:]
            require(len(hunks) == 2 and minus == ['-'+s['line_text']] and plus == ['+import Capture', '+'+replaced], s['site_id']+': '+str(diff[2:]))
            if (site_freeze.CENSUS_DIR/s['site_id']/'permitted.patch').exists():
                require((site_freeze.CENSUS_DIR/s['site_id']/'permitted.patch').read_text() == ''.join(difflib.unified_diff(
                    data.decode().splitlines(True), out.decode().splitlines(True), fromfile='Pristine.lean', tofile='Frozen.lean')), s['site_id']+': retained patch differs')
        return {'hunks_per_site': 2, 'retained_patches_match': True}
    suite.case('permitted_modification_is_one_token_and_one_import', one_token)

    def manifests():
        schema = r6.read_json(site_freeze.SCHEMA); admitted = frozen['admitted']; results = {}
        require(sorted(admitted+frozen['excluded']) == sorted(s['site_id'] for s in record['sites']) and not set(admitted) & set(frozen['excluded']))
        require({s['site_id']: {k: s[k] for k in s} for s in frozen['sites']} == {s['site_id']: s for s in record['sites']}, 'frozen site table differs from the census')
        for site_id in admitted:
            d = site_freeze.CENSUS_DIR/site_id; m = r6.read_json(d/'manifest.json'); jsonschema.validate(m, schema)
            entry = next(s for s in record['sites'] if s['site_id'] == site_id)
            require(m['task_id'] == site_id and m['saved_local_declaration'] == entry['saved_local_declaration'] and m['original_declaration'] == m['family'] == entry['declaration'])
            require(m['upstream']['proof_byte_span'] == entry['byte_span'] and m['upstream']['line'] == entry['line'] and m['site']['form'] == entry['form'] and m['exposure'] == entry['exposure'])
            for name, digest in m['artifacts_sha256'].items(): require((d/name).resolve().is_relative_to(d) and r6.sha(d/name) == digest, f'{site_id}: {name}')
            for name, digest in m['shared_artifacts_sha256'].items(): require(r6.sha(site_freeze.CENSUS_DIR/name) == digest, f'{site_id}: shared {name}')
            require(m['capture_sha256'] == r6.sha(site_freeze.CAPTURE) == frozen['capture_sha256'] and m['vendor_lock_sha256'] == r6.sha(r6.ROOT/'vendor/sources.lock.json'))
            context = r6.read_json(d/'context/local-context.json'); expected = r6.read_json(d/'expected.json')
            require(context['task_id'] == site_id and context['local_declaration'] == m['saved_local_declaration'] and context['target'] == m['captured_target'])
            require(expected['task_id'] == site_id and expected['policy'] == r6.policy([m['saved_local_declaration'], m['original_declaration']], True, task=site_freeze.Site(entry)))
            require([t['name'] for t in expected['targets']] == [m['saved_local_declaration'], m['original_declaration']] and all(t['kernel_accepted'] and t['statement_and_dependencies_match'] for t in expected['targets']))
            require(expected['source_binding_validated'] is True and expected['baseline_sha256'] == frozen['baseline_exports_sha256'][m['family']])
            require(r6.sha(site_freeze.CENSUS_DIR/f"baseline-{m['family']}.ndjson.gz") == frozen['baselines_sha256'][m['family']] == m['shared_artifacts_sha256'][f"baseline-{m['family']}.ndjson.gz"])
            require(set(m['baseline_axioms']) == {m['saved_local_declaration'], m['original_declaration']} and all(set(a) <= set(r6.AXIOMS) for a in m['baseline_axioms'].values()))
            result = next(x for x in frozen['results'] if x['site_id'] == site_id)
            require(result['status'] == 'admitted' and result['challenge_sha256'] == expected['challenge_sha256'])
            results[site_id] = {'form': m['site']['form'], 'target': m['captured_target'], 'telescope': len(context['telescope'])}
        for site_id in frozen['excluded']:
            result = next(x for x in frozen['results'] if x['site_id'] == site_id)
            require(result['status'] == 'excluded' and result['reason']['stage'] in ('capture-build', 'task-build', 'export', 'replay', 'unknown') and 'error' in result['reason'] and 'stdout_sha256' in result['reason'])
            require(not (site_freeze.CENSUS_DIR/site_id/'manifest.json').exists())
            results[site_id] = {'excluded': result['reason']['stage']}
        return results
    suite.case('site_manifests_bound', manifests)

    def line70():
        require('bracket-l070' in frozen['admitted'], 'line 70 was not admitted')
        d1 = r6.read_json(D1_CONTEXT); site = r6.read_json(site_freeze.CENSUS_DIR/'bracket-l070/context/local-context.json')
        require(d1['task_id'] == 'verinf-d1-70' and site['task_id'] == 'bracket-l070')
        require(d1['local_declaration'] == 'Bracket.lift_cell.r6_d1_70' and site['local_declaration'] == 'Bracket.lift_cell.r6_site_l070')
        require({k: v for k, v in d1.items() if k not in ('task_id', 'local_declaration')} == {k: v for k, v in site.items() if k not in ('task_id', 'local_declaration')},
                'the generalized capture at line 70 differs from the R6-000 extraction')
        d1_expected = r6.read_json(r6.D1.path/'expected.json'); site_expected = r6.read_json(site_freeze.CENSUS_DIR/'bracket-l070/expected.json')
        d1_type = next(t['type_sha256'] for t in d1_expected['targets'] if t['name'] == 'Bracket.lift_cell.r6_d1_70')
        site_type = next(t['type_sha256'] for t in site_expected['targets'] if t['name'] == 'Bracket.lift_cell.r6_site_l070')
        require(d1_type == site_type, 'closed local type differs from the R6-000 control')
        whole_d1 = next(t for t in d1_expected['targets'] if t['name'] == 'Bracket.lift_cell'); whole_site = next(t for t in site_expected['targets'] if t['name'] == 'Bracket.lift_cell')
        require(whole_d1['type_sha256'] == whole_site['type_sha256'] and whole_d1['axioms'] == whole_site['axioms'])
        m = r6.read_json(site_freeze.CENSUS_DIR/'bracket-l070/manifest.json'); d1m = r6.read_json(r6.D1.path/'manifest.json')
        require(m['upstream']['proof_byte_span'] == d1m['upstream']['proof_byte_span'] and m['local_goal_source'] == d1m['local_goal_source'] and m['exposure']['as_task'] == 'verinf-d1-70')
        return {'context_equal_modulo_identity': True, 'local_type_sha256': d1_type, 'span_equal': True}
    suite.case('line70_reproduces_the_r6_000_control', line70)

    def families():
        require(record['families'] == {'Bracket.lift_cell': [69, 70, 71, 78], 'Bracket.threshold_unique': [96, 98, 99, 101],
                                       'Bracket.cell_value_neutral': [158, 166, 170, 175, 178, 180], 'Bracket.Row.s1_noninc': [204]})
        exposed = [s['site_id'] for s in record['sites'] if s['exposure']['exposed']]
        require(exposed == ['bracket-l070'] and record['sites'][1]['exposure']['as_task'] == 'verinf-d1-70' and len(record['sites'][1]['exposure']['model_visible_in']) == 2)
        require(all(s['exposure'] == {'exposed': False, 'as_task': None, 'model_visible_in': []} for s in record['sites'] if s['site_id'] != 'bracket-l070'))
        return {'families': 4, 'exposed': exposed}
    suite.case('families_and_exposure_recorded', families)

    def membership():
        m = r6.read_json(site_freeze.CENSUS_DIR/'membership.json')
        require(m['census_sha256'] == r6.sha(site_freeze.CENSUS_DIR/'census.json') and m['census_id'] == census.CENSUS_ID)
        require(sorted(m['primary']+list(m['excluded'])) == sorted(s['site_id'] for s in record['sites']) and not set(m['primary']) & set(m['excluded']))
        require(m['primary'] == frozen['admitted'] and set(m['excluded']) == set(frozen['excluded']))
        require(m['exposed'] == [s for s in m['primary'] if next(x for x in record['sites'] if x['site_id'] == s)['exposure']['exposed']])
        require(all(m['families'][f] == [s for s in m['primary'] if next(x for x in record['sites'] if x['site_id'] == s)['declaration'] == f] for f in record['families']))
        require(all(m['excluded'][s]['stage'] for s in m['excluded']) and m['status'].startswith('proposed'))
        require(m['manifests_sha256'] == {s: r6.sha(site_freeze.CENSUS_DIR/s/'manifest.json') for s in m['primary']})
        return {'primary': len(m['primary']), 'excluded': len(m['excluded']), 'exposed': m['exposed'], 'families': {f: len(v) for f, v in m['families'].items()}}
    suite.case('membership_partitions_and_binds_the_census', membership)

    def exclusion():
        """The real freeze path on a site that cannot be captured: nothing is written to the census, and the result names the failing
        sandbox stage with its stderr digest and the error, exactly as an excluded census site would be recorded."""
        import tempfile
        compiler, exporter, checker = r6.build_tools(task=r6.D1)
        mounts, lean_path, env = site_freeze.prepare_shared((r6.ROOT.parents[1]/'lean-bridge/.lake/packages').resolve(), compiler)
        entry = dict(record['sites'][0]); entry['saved_local_declaration'] = entry['declaration']  # a name the environment already holds
        site = site_freeze.Site(entry); before = sorted(p.name for p in site_freeze.CENSUS_DIR.iterdir())
        with tempfile.TemporaryDirectory(prefix='r6-census-exclusion-') as temp:
            result = site_freeze.freeze_site(Path(temp), site, Path(temp)/'absent-baseline', {'targets': []}, compiler, exporter, mounts, lean_path, env, checker, None)
            stdout = (Path(temp)/site.id/'challenge/output/task-build.stdout').read_bytes()
        require(result['status'] == 'excluded' and result['reason']['stage'] == 'task-build' and result['reason']['exit_code'] != 0
                and result['reason']['stdout_sha256'] == r6.hashlib.sha256(stdout).hexdigest() and result['reason']['stdout_head'] == stdout[:2000].decode())
        require('already' in stdout.decode('utf-8', 'replace') and result['reason']['error'].startswith('RuntimeError'), stdout[:300])
        require(sorted(p.name for p in site_freeze.CENSUS_DIR.iterdir()) == before, 'the failed site wrote into the census')
        return {'status': result['status'], 'stage': result['reason']['stage'], 'census_untouched': True}
    suite.case('exclusion_records_failing_stage_and_stderr', exclusion)

    def bound():
        require(frozen['census_module_sha256'] == r6.sha(r6.ROOT/'census.py') and frozen['site_freeze_sha256'] == r6.sha(r6.ROOT/'site_freeze.py'))
        require(frozen['capture_sha256'] == r6.sha(site_freeze.CAPTURE) and frozen['schema_sha256'] == r6.sha(site_freeze.SCHEMA))
        require(frozen['shared_artifacts_sha256'] == {n: r6.sha(site_freeze.CENSUS_DIR/n) for n in site_freeze.SHARED} and frozen['pristine_sha256'] == census.SOURCE_HASH)
        require(r6.sha(site_freeze.CENSUS_DIR/'Pristine.lean') == census.SOURCE_HASH == r6.sha(r6.D1.path/'Pristine.lean'))
        require(frozen['runtime']['validator_libraries_sha256'] and frozen['site_count'] == 15 and len(frozen['results']) == 15)
        return {'census_module': frozen['census_module_sha256'][:16], 'site_freeze': frozen['site_freeze_sha256'][:16], 'capture': frozen['capture_sha256'][:16]}
    suite.case('freeze_bound_to_its_sources', bound)
    suite.finish()
    return suite


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    controls(args.output)
    print(json.dumps({'passed': True, 'cases': len(CASES)}, indent=1))


if __name__ == '__main__':
    main()
