#!/usr/bin/env python3
"""R6-010 historical census auditor. Non-locked; read-only over the frozen census and its retained freeze.

The census controls check supplied manifest hashes; this auditor derives what those hashes should be. Populations are exact
(census directory, freeze directory, per-site files, artifact keys); challenge and family-baseline exports are decompressed
and digested; the expected declarations, types, axioms and admission results are derived from the raw replay reports by the
frozen normalization; capture contexts, instrumented sources and helper bytes are bound to the retained freeze inputs and
outputs; every sandbox stage of the freeze must have returned; the site helper must differ from the R6-000 helper by exactly
the documented transformation; membership, the review's population decision and the exposure addendum must be recomputed.
After the follow-up review: every replay report (baseline, source binding, local) meets the full report contract, and the
source-binding target equals its family baseline's and the containing target; each site's and family's retained evidence is
an exact inventory of required files plus optional ignored build products, which must equal their frozen exports when
present; and every recorded build, export and replay command is bound to its role — challenge and solution mounts, input,
objects and output directories, checker, exporter, toolchain, environment and libraries — under one recorded layout.
The named case population is fixed: the audit fails unless exactly those cases were evaluated.
"""
import argparse
import difflib
import gzip
import hashlib
import importlib.util
import json
import re
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import jsonschema

import census
import run as r6
import site_freeze

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('r6_census_exposure', HERE/'census_exposure.py')
exposure = importlib.util.module_from_spec(spec); spec.loader.exec_module(exposure)

SITE_DIR_FILES = sorted([*site_freeze.SITE_FILES, 'manifest.json'])
CENSUS_TOP = sorted([*site_freeze.SHARED, 'census.json', 'membership.json', exposure.ADDENDUM])
SITE_STAGES = sorted(['challenge/output/capture-build.process.json', 'challenge/output/task-build.process.json', 'challenge/export/export.process.json',
                      'source-binding-validation/replay.process.json', 'challenge-validation/replay.process.json'])
BASELINE_STAGES = sorted(['baseline/output/task-build.process.json', 'baseline/export/export.process.json', 'baseline-validation/replay.process.json'])
# The exact helper transformation, reviewed line by line: the comment is rewritten, the tactic takes the saved name and the site
# id as string literals, the fixed name becomes the parameter with a guard against an anonymous or existing name, and the fixed
# task id becomes the parameter. Nothing else may be added or removed.
HELPER_REMOVED = ['/- Trusted extraction instrumentation, compiled separately from the task.',
                  'elab "r6_capture_human" : tactic => withMainContext do',
                  '  let name := `Bracket.lift_cell.r6_d1_70',
                  '    ("task_id", "verinf-d1-70"),']
HELPER_ADDED = ['/- Trusted extraction instrumentation for any `omega` site, compiled separately',
                '   from the task. The R6-000 helper (`Capture.lean`) fixed one saved-declaration',
                '   name and one task identity in its body; this helper takes both as string',
                '   literals, so the same bytes capture a named `have`, a bare goal-closing',
                '   `omega`, a post-`simp` closer, an inline `(by omega)` term or a `calc` step:',
                '   the capture is of the goal state at the site, whatever syntax surrounds it.',
                'elab "r6_capture_human" savedName:str siteId:str : tactic => withMainContext do',
                '  let name := savedName.getString.toName',
                '  if name.isAnonymous || (← getEnv).contains name then',
                '    throwError "R6 saved declaration name is unusable: {savedName.getString}"',
                '    ("task_id", toJson siteId.getString),']


class Rejection(AssertionError):
    def __init__(self, case, detail=''):
        super().__init__(case+(': '+detail if detail else '')); self.case = case


class Audit:
    def __init__(self): self.cases = {}
    def require(self, ok, case, detail=''):
        if case in self.cases: raise Rejection(case, 'duplicate case name')
        self.cases[case] = bool(ok)
        if not ok: raise Rejection(case, detail)


def sha(data): return hashlib.sha256(data).hexdigest()
def load(path): return json.loads(Path(path).read_bytes())
def gunzip_sha(path): return sha(gzip.decompress(Path(path).read_bytes()))


def listing(directory):
    return sorted(str(p.relative_to(directory)) for p in directory.rglob('*') if p.is_file())


def normalized(raw_path):
    """The frozen normalization of `run.check`: the raw type representation becomes its UTF-8 digest."""
    raw = json.loads(gzip.decompress(Path(raw_path).read_bytes()))
    for t in raw.get('targets', []):
        t['type_sha256'] = sha(t.pop('type_repr').encode()); t['type_hash_format'] = 'Lean-4.32.2-reprStr-Expr-UTF8'
    return raw


# Per-stage retained evidence: required files (committed), and optional build products (ignored by Git; compared when present).
SITE_REQUIRED = sorted(['challenge/export/export.command.json', 'challenge/export/export.process.json', 'challenge/export/export.stderr',
    'challenge/input/Capture.lean', 'challenge/input/Frozen.lean',
    *[f'challenge/output/{s}.{x}' for s in ('capture-build', 'task-build') for x in ('command.json', 'process.json', 'stderr', 'stdout')],
    'challenge/output/context.json',
    *[f'{v}/{x}' for v in ('challenge-validation', 'source-binding-validation') for x in ('replay.command.json', 'replay.process.json', 'replay.stderr', 'replay.stdout', 'verdict.json', 'verdict.raw.json.gz')]])
SITE_OPTIONAL = sorted(['challenge/output/Capture.olean', 'challenge/output/Frozen.olean', 'challenge/output/proof.ndjson'])
BASELINE_REQUIRED = sorted(['baseline/export/export.command.json', 'baseline/export/export.process.json', 'baseline/export/export.stderr',
    'baseline/input/Capture.lean', 'baseline/input/Frozen.lean',
    *[f'baseline/output/task-build.{x}' for x in ('command.json', 'process.json', 'stderr', 'stdout')],
    *[f'baseline-validation/{x}' for x in ('replay.command.json', 'replay.process.json', 'replay.stderr', 'replay.stdout', 'verdict.json', 'verdict.raw.json.gz')]])
BASELINE_OPTIONAL = sorted(['baseline/output/Frozen.olean', 'baseline/output/proof.ndjson'])
SANDBOX_PREFIX = ['bwrap', '--unshare-all', '--die-with-parent', '--new-session', '--cap-drop', 'ALL', '--clearenv', '--setenv', 'PATH', '/no-programs',
                  '--setenv', 'LEAN_ABORT_ON_PANIC', '1', '--symlink', 'usr/lib', '/lib', '--symlink', 'usr/lib64', '/lib64', '--proc', '/proc',
                  '--dev', '/dev', '--tmpfs', '/tmp', '--dir', '/work', '--chdir', '/work']
SANDBOX_LIMITS = {'timeout_seconds': 150, 'address_space_bytes': 32*1024**3, 'cpu_seconds': 120, 'max_output_file_bytes': 256*1024**2}


def inventory_ok(directory, required, optional, exports):
    """Required evidence present, nothing unlisted, and an optional export, when present, equal to the frozen one."""
    present = listing(directory)
    if not (set(required) <= set(present) <= set(required) | set(optional)): return False, f'present {sorted(set(present) ^ set(required))}'
    for name, digest in exports.items():
        if (directory/name).exists() and sha((directory/name).read_bytes()) != digest: return False, f'{name} differs from its frozen export'
    return True, ''


def parse_command(path):
    """A recorded sandbox command, split into its fixed prefix, its bind/setenv operations and the program arguments."""
    record = load(path); argv = record['argv']; limits = {k: v for k, v in record.items() if k != 'argv'}
    if argv[:len(SANDBOX_PREFIX)] != SANDBOX_PREFIX or limits != SANDBOX_LIMITS: return None
    i = len(SANDBOX_PREFIX); ops = []
    while i < len(argv) and argv[i] in ('--ro-bind', '--bind', '--setenv'):
        ops.append(tuple(argv[i:i+3])); i += 3
    libraries = [o for o in ops if o[0] == '--ro-bind' and o[2].startswith(('/usr/lib/', '/usr/lib64/'))]
    environment = [o for o in ops if o[0] == '--ro-bind' and o[2].startswith('/env/')]
    rest = [o for o in ops if o not in libraries and o not in environment]
    return {'libraries': libraries, 'environment': environment, 'ops': rest, 'program': argv[i:]}


class Layout:
    """The recorded freeze layout, derived from the records and required to be the same for every command: the freeze root, the
    repository root under it, the elaboration toolchain, the environment mounts, and the two library sets."""
    def __init__(self, freeze_root, runtime):
        self.F = freeze_root; self.R = freeze_root[:-len('census-runs/freeze-v1')]; self.runtime = runtime; self.seen = {}

    def same(self, key, value):
        return self.seen.setdefault(key, value) == value

    def check(self, path, kind, directory, **role):
        """`kind` in capture-build, task-build, export, replay; `directory` is the recorded stage parent (site or baseline dir)."""
        c = parse_command(path)
        if c is None: return False
        F, R = self.F, self.R
        if kind == 'replay':
            ok = self.same('replay-libraries', c['libraries']) and sorted(g for _, _, g in c['libraries']) == sorted(self.runtime['validator_libraries_sha256']) and c['environment'] == []
            policy = c['ops'][2][1] if len(c['ops']) > 2 else ''
            ok = ok and Path(policy).name == 'policy.json' and Path(policy).parent.name.startswith('r6-policy-') and not policy.startswith((F, R))
            return ok and c['ops'] == [('--ro-bind', role['challenge'], '/challenge.ndjson'), ('--ro-bind', role['solution'], '/solution.ndjson'),
                                        ('--ro-bind', policy, '/policy.json'), ('--ro-bind', R+'.cache/checker/.lake/build/bin/r6-replay', '/runner/bin/program'),
                                        ('--bind', role['out'], '/out')] \
                and c['program'] == ['/runner/bin/program', '/challenge.ndjson', '/solution.ndjson', '/policy.json', '/out/verdict.json']
        T = c['ops'][0][1][:-len('/lib')] if c['ops'] and c['ops'][0][2] == '/toolchain/lib' else ''
        E = ':'.join(g for _, _, g in c['environment'])
        ok = self.same('toolchain', T) and T.endswith('leanprover--lean4---v4.32.0') and self.same('lean-libraries', c['libraries']) and self.same('environment', c['environment'])
        ok = ok and bool(c['environment']) and all(g.startswith('/env/') for _, _, g in c['environment'])
        head = [('--ro-bind', T+'/lib', '/toolchain/lib'), ('--ro-bind', T+'/bin/lean', '/toolchain/bin/lean'),
                ('--setenv', 'LEAN_SYSROOT', '/toolchain'), ('--setenv', 'LD_LIBRARY_PATH', '/toolchain/lib/lean:/toolchain/lib')]
        if kind in ('capture-build', 'task-build'):
            env = [] if kind == 'capture-build' else [('--setenv', 'LEAN_PATH', E+':/out'), ('--setenv', 'R6_CAPTURE_OUTPUT', '/out/context.json')]
            target = 'Capture' if kind == 'capture-build' else 'Frozen'
            return ok and c['ops'] == [*head, ('--ro-bind', directory+'/input', '/input'), *env, ('--ro-bind', T+'/bin/lean', '/toolchain/bin/program'),
                                       ('--bind', directory+'/output', '/out')] \
                and c['program'] == ['/toolchain/bin/program', '-R', '/input', '-o', f'/out/{target}.olean', f'/input/{target}.lean']
        return ok and c['ops'] == [*head, ('--ro-bind', directory+'/output', '/objects'), ('--setenv', 'LEAN_PATH', E+':/objects'),
                                   ('--ro-bind', R+'.cache/exporter/.lake/build/bin/lean4export', '/toolchain/bin/program'), ('--bind', directory+'/export', '/out')] \
            and c['program'] == ['/toolchain/bin/program', 'Frozen', '--', *role['declarations'], *r6.EXPORT_TARGETS]


def report_ok(report, names, binding):
    """The full replay-report contract, not `accepted` alone: completion, kernel, exact targets and every per-target predicate."""
    return (report.get('accepted') is True and report.get('stage') == 'complete' and report.get('kernel_version') == '4.32.2'
            and report.get('local_proof_binding_checked') is binding and isinstance(report.get('checked_declarations'), int) and report['checked_declarations'] > 0
            and [t['name'] for t in report['targets']] == names
            and all(t['declaration_exists'] is True and t['kernel_accepted'] is True and t['statement_and_dependencies_match'] is True
                    and set(t['axioms']) <= set(r6.AXIOMS) and t['type_hash_format'] == 'Lean-4.32.2-reprStr-Expr-UTF8' for t in report['targets']))


def expected_cases(site_ids):
    names = ['population:exact_census_directory', 'population:exact_freeze_directory', 'helper:exact_transformation',
             'sources:lock_and_recorded_digests', 'baselines:family_exports_replayed']
    for s in site_ids:
        names += [f'{s}:census_entry_reproduced', f'{s}:inventory_exact', f'{s}:challenge_export_bound', f'{s}:baseline_bound',
                  f'{s}:replays_derived_from_raw_reports', f'{s}:capture_inputs_and_context', f'{s}:stages_returned',
                  f'{s}:evidence_inventory_exact', f'{s}:commands_bound_to_roles', f'{s}:manifest_derived']
    names += ['membership:bound_to_census_and_decision', 'exposure:addendum_recomputed']
    return tuple(names)


def audit(census_dir, freeze_dir, capture=site_freeze.CAPTURE, decision=exposure.DECISION):
    a = Audit(); record = census.census(); data = census.pristine(); ids = [s['site_id'] for s in record['sites']]
    families = list(record['families'])
    frozen = load(census_dir/'census.json')
    a.require(sorted(p.name for p in census_dir.iterdir()) == sorted([*CENSUS_TOP, *ids, *[f'baseline-{f}.ndjson.gz' for f in families]])
              and all((census_dir/s).is_dir() for s in ids), 'population:exact_census_directory', str(sorted(p.name for p in census_dir.iterdir())))
    a.require(sorted(p.name for p in freeze_dir.iterdir()) == sorted(['runtime.json', *ids, *[f'baseline-{f}' for f in families]]),
              'population:exact_freeze_directory', str(sorted(p.name for p in freeze_dir.iterdir())))
    base = (ROOT/'capture/Capture.lean').read_text().splitlines(); site = capture.read_text().splitlines()
    diff = [l for l in difflib.unified_diff(base, site, lineterm='', n=0) if l[:1] in '+-' and not l.startswith(('+++', '---'))]
    a.require([l[1:] for l in diff if l[0] == '-'] == HELPER_REMOVED and [l[1:] for l in diff if l[0] == '+'] == HELPER_ADDED,
              'helper:exact_transformation', str(diff))
    try: census.verify_lock(); locked = True
    except ValueError: locked = False
    a.require(locked and frozen['census_module_sha256'] == r6.sha(ROOT/'census.py') and frozen['site_freeze_sha256'] == r6.sha(ROOT/'site_freeze.py')
              and frozen['capture_sha256'] == sha(capture.read_bytes()) and frozen['schema_sha256'] == r6.sha(site_freeze.SCHEMA)
              and frozen['pristine_sha256'] == census.SOURCE_HASH == sha((census_dir/'Pristine.lean').read_bytes())
              and frozen['shared_artifacts_sha256'] == {n: sha((census_dir/n).read_bytes()) for n in site_freeze.SHARED}
              and frozen['runtime'] == load(freeze_dir/'runtime.json'), 'sources:lock_and_recorded_digests')
    # the recorded layout, taken from one record and then required of every command
    tail = f'/baseline-{families[0]}/baseline-validation'
    try: out = (parse_command(freeze_dir/f'baseline-{families[0]}/baseline-validation/replay.command.json') or {'ops': [('', '', '')]})['ops'][-1][1]
    except (OSError, ValueError, KeyError, IndexError, TypeError): out = ''
    recorded_root = out[:-len(tail)] if out.endswith(tail) else ''
    layout = Layout(recorded_root, load(freeze_dir/'runtime.json')); F = recorded_root
    baseline_reports = {}; ok = recorded_root.endswith('/census-runs/freeze-v1'); detail = ''
    for f in families:
        d = freeze_dir/f'baseline-{f}'; rd = f'{F}/baseline-{f}'; export = f'{rd}/baseline/output/proof.ndjson'
        report = normalized(d/'baseline-validation/verdict.raw.json.gz'); baseline_reports[f] = report
        ok = ok and report == load(d/'baseline-validation/verdict.json') and report_ok(report, [f], False)
        inventory, why = inventory_ok(d, BASELINE_REQUIRED, BASELINE_OPTIONAL, {'baseline/output/proof.ndjson': frozen['baseline_exports_sha256'][f]})
        ok = ok and inventory and layout.check(d/'baseline/output/task-build.command.json', 'task-build', rd+'/baseline') \
             and layout.check(d/'baseline/export/export.command.json', 'export', rd+'/baseline', declarations=[f]) \
             and layout.check(d/'baseline-validation/replay.command.json', 'replay', rd, challenge=export, solution=export, out=rd+'/baseline-validation')
        detail = detail or why
        ok = ok and (d/'baseline/input/Frozen.lean').read_bytes() == data and sorted(str(p.relative_to(d)) for p in d.rglob('*.process.json')) == BASELINE_STAGES
        ok = ok and all(load(p)['exit_code'] == 0 and not load(p).get('timed_out') for p in d.rglob('*.process.json'))
    a.require(ok, 'baselines:family_exports_replayed', detail)
    results = {r['site_id']: r for r in frozen['results']}; schema = load(site_freeze.SCHEMA)
    for entry in record['sites']:
        s = entry['site_id']; d = census_dir/s; w = freeze_dir/s; st = site_freeze.Site(entry)
        a.require(next(x for x in frozen['sites'] if x['site_id'] == s) == entry and results[s]['status'] == 'admitted', f'{s}:census_entry_reproduced')
        m = load(d/'manifest.json')
        shared_keys = sorted([*site_freeze.SHARED, f'baseline-{entry["declaration"]}.ndjson.gz'])
        a.require(listing(d) == SITE_DIR_FILES and sorted(m['artifacts_sha256']) == sorted(site_freeze.SITE_FILES) and sorted(m['shared_artifacts_sha256']) == shared_keys
                  and all(sha((d/k).read_bytes()) == v for k, v in m['artifacts_sha256'].items())
                  and all(sha((census_dir/k).read_bytes()) == v for k, v in m['shared_artifacts_sha256'].items()), f'{s}:inventory_exact',
                  f'files {listing(d)}, keys {sorted(m["artifacts_sha256"])}')
        expected = load(d/'expected.json'); challenge = gzip.decompress((d/'challenge.ndjson.gz').read_bytes())
        # the export names declarations by components: the saved local's last component, and no other site's, must be present
        components = set(re.findall(rb'"str":"(r6_site_l[0-9]{3})"', challenge))
        a.require(sha(challenge) == expected['challenge_sha256'] == results[s]['challenge_sha256']
                  and components == {st.local.rsplit('.', 1)[1].encode()}, f'{s}:challenge_export_bound', str(components))
        baseline_gz = census_dir/f'baseline-{st.whole}.ndjson.gz'
        a.require(gunzip_sha(baseline_gz) == expected['baseline_sha256'] == frozen['baseline_exports_sha256'][st.whole]
                  and sha(baseline_gz.read_bytes()) == frozen['baselines_sha256'][st.whole]
                  and expected['baseline_whole_declaration'] == baseline_reports[st.whole]['targets'][0], f'{s}:baseline_bound')
        binding = normalized(w/'source-binding-validation/verdict.raw.json.gz'); local = normalized(w/'challenge-validation/verdict.raw.json.gz')
        local_type = next((t['type_sha256'] for t in local['targets'] if t['name'] == st.local), None)
        a.require(binding == load(w/'source-binding-validation/verdict.json') and local == load(w/'challenge-validation/verdict.json')
                  and report_ok(binding, [st.whole], False) and report_ok(local, [st.local, st.whole], True)
                  and binding['targets'][0] == baseline_reports[st.whole]['targets'][0] == local['targets'][1]
                  and expected['source_binding_validated'] is True and expected['targets'] == local['targets']
                  and [t['name'] for t in local['targets']] == [st.local, st.whole] and all(t['kernel_accepted'] and t['statement_and_dependencies_match'] for t in local['targets'])
                  and all(set(t['axioms']) <= set(r6.AXIOMS) for t in local['targets']) and results[s]['local_type_sha256'] == local_type
                  and expected['policy'] == r6.policy([st.local, st.whole], True, task=st) and expected['task_id'] == s,
                  f'{s}:replays_derived_from_raw_reports')
        context = load(d/'context/local-context.json'); instrumented = site_freeze.instrument(data, st)
        patch = ''.join(difflib.unified_diff(data.decode().splitlines(True), instrumented.decode().splitlines(True), fromfile='Pristine.lean', tofile='Frozen.lean'))
        a.require((w/'challenge/input/Frozen.lean').read_bytes() == instrumented and (w/'challenge/input/Capture.lean').read_bytes() == capture.read_bytes()
                  and load(w/'challenge/output/context.json') == context and context['task_id'] == s and context['local_declaration'] == st.local
                  and context['target'] == m['captured_target'] == results[s]['captured_target'] and (d/'permitted.patch').read_text() == patch,
                  f'{s}:capture_inputs_and_context')
        processes = sorted(str(p.relative_to(w)) for p in w.rglob('*.process.json'))
        a.require(processes == SITE_STAGES and all(load(w/p)['exit_code'] == 0 and not load(w/p).get('timed_out') for p in processes),
                  f'{s}:stages_returned', str(processes))
        inventory, why = inventory_ok(w, SITE_REQUIRED, SITE_OPTIONAL, {'challenge/output/proof.ndjson': expected['challenge_sha256']})
        a.require(inventory, f'{s}:evidence_inventory_exact', why)
        sd = f'{F}/{s}'; site_export = f'{sd}/challenge/output/proof.ndjson'; family_export = f'{F}/baseline-{st.whole}/baseline/output/proof.ndjson'
        a.require(layout.check(w/'challenge/output/capture-build.command.json', 'capture-build', sd+'/challenge')
                  and layout.check(w/'challenge/output/task-build.command.json', 'task-build', sd+'/challenge')
                  and layout.check(w/'challenge/export/export.command.json', 'export', sd+'/challenge', declarations=[st.whole, st.local])
                  and layout.check(w/'source-binding-validation/replay.command.json', 'replay', sd, challenge=family_export, solution=site_export, out=sd+'/source-binding-validation')
                  and layout.check(w/'challenge-validation/replay.command.json', 'replay', sd, challenge=site_export, solution=site_export, out=sd+'/challenge-validation'),
                  f'{s}:commands_bound_to_roles')
        try: jsonschema.validate(m, schema); valid = True
        except jsonschema.ValidationError: valid = False
        a.require(valid and m['task_id'] == s and m['census_id'] == census.CENSUS_ID and m['upstream'] == {**census.UPSTREAM, 'line': entry['line'],
                  'pristine_sha256': census.SOURCE_HASH, 'proof_byte_span': entry['byte_span']}
                  and m['site'] == {'line': entry['line'], 'column': entry['column'], 'form': entry['form'], 'line_text': entry['line_text']}
                  and m['original_declaration'] == m['family'] == entry['declaration'] and m['saved_local_declaration'] == entry['saved_local_declaration']
                  and m['local_goal_source'] == site_freeze.goal_source(entry) and m['exposure'] == entry['exposure']
                  and m['baseline_axioms'] == {t['name']: t['axioms'] for t in local['targets']} and m['capture_sha256'] == sha(capture.read_bytes())
                  and m['vendor_lock_sha256'] == r6.sha(ROOT/'vendor/sources.lock.json'), f'{s}:manifest_derived')
    membership_bytes = (census_dir/'membership.json').read_bytes(); dec = load(decision)
    a.require(json.loads(membership_bytes) == census.membership(census_dir) and sha(membership_bytes) == dec['membership_proposal_sha256']
              and sha((census_dir/'census.json').read_bytes()) == dec['census_sha256'] and dec['primary'] == ids
              and dec['manifests_sha256'] == {s: sha((census_dir/s/'manifest.json').read_bytes()) for s in ids}
              and dec['decision'] == 'retain_complete_fifteen_site_primary_population' and dec['live_model_calls_authorized'] == 0,
              'membership:bound_to_census_and_decision')
    try: derived = exposure.derive(census_dir, decision); detail = ''
    except (ValueError, KeyError) as error: derived = None; detail = str(error)
    a.require(derived is not None and load(census_dir/exposure.ADDENDUM) == derived, 'exposure:addendum_recomputed', detail)
    expected_names = expected_cases(ids)
    missing = sorted(set(expected_names)-set(a.cases)); extra = sorted(set(a.cases)-set(expected_names))
    if missing or extra or len(a.cases) != len(expected_names): raise Rejection('cases:population', f'missing {missing} extra {extra}')
    return {'accepted': all(a.cases.values()), 'case_count': len(a.cases), 'cases': a.cases, 'census_sha256': sha((census_dir/'census.json').read_bytes()),
            'addendum_sha256': sha((census_dir/exposure.ADDENDUM).read_bytes()), 'program_sha256': sha(Path(__file__).read_bytes()),
            'scope': 'retained freeze bytes; no Lean compilation, no replay rerun, no provider call'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--census', type=Path, default=site_freeze.CENSUS_DIR)
    parser.add_argument('--freeze', type=Path, default=ROOT/'census-runs/freeze-v1')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output and args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    try: result = audit(args.census.resolve(), args.freeze.resolve())
    except Rejection as rejection:
        print(json.dumps({'accepted': False, 'rejected_case': rejection.case, 'detail': str(rejection)[:2000]}, indent=1)); sys.exit(1)
    if args.output: r6.write_json(args.output, result)
    print(json.dumps({k: result[k] for k in ('accepted', 'case_count', 'census_sha256', 'addendum_sha256')}, indent=1))
    sys.exit(0 if result['accepted'] else 1)


if __name__ == '__main__':
    main()
