"""R6-010 site freeze: capture and freeze every census site with the generalized anchor, recording admission or exclusion.

For each site the pristine bytes are instrumented at the site's byte span only — `omega` becomes
`r6_capture_human "<saved declaration>" "<site id>"` — plus the trusted `import Capture` line; the site helper
(`capture/CaptureSite.lean`) is compiled separately and captures the goal state at the site, saves the closed local
obligation as a named theorem, and writes the elaborated context. The instrumented file is compiled and exported, and
three kernel replays run as for the R6-000 control: the family's baseline export against itself, the baseline against
the site's export (source binding), and the site's export against itself with the local/whole dependency required.
A site whose capture, compilation, export or replay fails is excluded with the failing stage and the sandbox's stderr
digest as the reason; nothing is retried or hand-adjusted. The frozen R6-000 machinery (`run.py`, `task_spec.py`) is
reused for the sandbox, environment, export targets, replay and policies and is not modified.
"""
import argparse
from datetime import datetime, timezone
import difflib
import json
from pathlib import Path
import shutil
import tempfile
import time

import jsonschema

import census
import run as r6

CENSUS_DIR = r6.ROOT/'tasks/census-v1'
CAPTURE = r6.ROOT/'capture/CaptureSite.lean'
SCHEMA = r6.ROOT/'schema/task-site.schema.json'
SHARED = ('Pristine.lean', 'pristine.sha256', 'upstream-lake-manifest.json', 'upstream-lakefile.toml', 'lean-toolchain', 'environment-inventory.json.gz')
SITE_FILES = ('challenge.ndjson.gz', 'context/local-context.json', 'expected.json', 'permitted.patch')


class Site:
    """The duck-typed task the frozen R6-000 helpers expect: identity, containing declaration, saved local declaration, paths."""
    def __init__(self, entry):
        self.entry = entry; self.id = entry['site_id']; self.whole = entry['declaration']; self.local = entry['saved_local_declaration']
        self.path = CENSUS_DIR; self.capture = CAPTURE; self.source_hash = census.SOURCE_HASH
        self.line = entry['line']; self.span = entry['byte_span']


def instrument(data, site):
    """The one permitted modification: the site's `omega` token becomes the parameterized capture, and the trusted import is added."""
    s, e = site.span['start'], site.span['end_exclusive']
    if data[s:e] != census.TOKEN: raise ValueError(f'{site.id}: span is not the token')
    replaced = data[:s]+f'r6_capture_human "{site.local}" "{site.id}"'.encode()+data[e:]
    if not replaced.startswith(b'import Mathlib\n'): raise ValueError('Unexpected imports')
    return replaced.replace(b'import Mathlib\n', b'import Mathlib\nimport Capture\n', 1)


def prepare_shared(packages_dir, compiler):
    """The census directory shares the pristine source, the environment lock files and the compiled-environment inventory."""
    CENSUS_DIR.mkdir(parents=True, exist_ok=True)
    d1 = r6.D1.path
    for name in ('Pristine.lean', 'upstream-lake-manifest.json', 'upstream-lakefile.toml', 'lean-toolchain'):
        if not (CENSUS_DIR/name).exists(): shutil.copyfile(d1/name, CENSUS_DIR/name)
    if r6.sha(CENSUS_DIR/'Pristine.lean') != census.SOURCE_HASH: raise ValueError('census pristine differs')
    (CENSUS_DIR/'pristine.sha256').write_text(f'{census.SOURCE_HASH}  Pristine.lean\n')
    mounts, lean_path, env = r6.environment(packages_dir, compiler, r6.D1)
    if not (CENSUS_DIR/'environment-inventory.json.gz').exists():
        with tempfile.TemporaryDirectory(prefix='r6-inventory-') as temp:
            inv = Path(temp)/'inventory.json'; r6.write_json(inv, r6.inventory(mounts, compiler)); r6.pack(inv, CENSUS_DIR/'environment-inventory.json.gz')
    return mounts, lean_path, env


def compile_and_export(work, compiler, exporter, mounts, lean_path, site, *, original=False):
    """As `run.compile_and_export`, with the byte-span instrumentation and the site helper."""
    inputs, outputs = work/'input', work/'output'; inputs.mkdir(parents=True); outputs.mkdir()
    data = census.pristine()
    (inputs/'Frozen.lean').write_bytes(data if original else instrument(data, site))
    shutil.copyfile(site.capture, inputs/'Capture.lean')
    all_mounts = [*mounts, (inputs, '/input')]
    if not original:
        r6.sandbox(compiler/'bin/lean', ['-R', '/input', '-o', '/out/Capture.olean', '/input/Capture.lean'], all_mounts, outputs, 'capture-build', compiler=compiler)
    r6.sandbox(compiler/'bin/lean', ['-R', '/input', '-o', '/out/Frozen.olean', '/input/Frozen.lean'], all_mounts, outputs, 'task-build', compiler=compiler,
               env={'LEAN_PATH': lean_path+':/out', 'R6_CAPTURE_OUTPUT': '/out/context.json'})
    export_file = outputs/'proof.ndjson'; export_out = work/'export'
    r6.sandbox(exporter, ['Frozen', '--', site.whole, *([] if original else [site.local]), *r6.EXPORT_TARGETS],
               [*mounts, (outputs, '/objects')], export_out, 'export', compiler=compiler, env={'LEAN_PATH': lean_path+':/objects'}, stdout_path=export_file)
    return export_file, outputs


def failure_digest(work):
    """Which sandboxed stage failed, with the digests and first lines of its stdout and stderr (Lean reports diagnostics on stdout):
    the reason is retained, never paraphrased."""
    for label in ('capture-build', 'task-build', 'export', 'replay'):
        for path in sorted(work.rglob(label+'.process.json')):
            if r6.read_json(path)['exit_code'] != 0:
                streams = {}
                for stream in ('stdout', 'stderr'):
                    text = path.with_name(f'{label}.{stream}').read_bytes() if path.with_name(f'{label}.{stream}').exists() else b''
                    streams[stream+'_sha256'] = r6.hashlib.sha256(text).hexdigest(); streams[stream+'_head'] = text[:2000].decode('utf-8', 'replace')
                return {'stage': label, 'exit_code': r6.read_json(path)['exit_code'], **streams}
    return {'stage': 'unknown', 'exit_code': None}


def freeze_family_baseline(run, family, compiler, exporter, mounts, lean_path, checker):
    """One original export per family, validated against itself; shared by every site of that family."""
    site = Site({'site_id': 'baseline', 'declaration': family, 'saved_local_declaration': family+'.none', 'line': 0, 'byte_span': {'start': 0, 'end_exclusive': 0}})
    baseline, _ = compile_and_export(run/'baseline', compiler, exporter, mounts, lean_path, site, original=True)
    report = r6.accepted(r6.check(baseline, baseline, checker, r6.policy([family], task=site), run/'baseline-validation'))
    target = CENSUS_DIR/f'baseline-{family}.ndjson.gz'
    if target.exists(): raise ValueError('baseline already frozen: '+target.name)
    r6.pack(baseline, target)
    return baseline, report


def freeze_site(run, site, baseline, baseline_report, compiler, exporter, mounts, lean_path, env, checker, packages_dir):
    work = run/site.id; work.mkdir()
    try:
        challenge, captured = compile_and_export(work/'challenge', compiler, exporter, mounts, lean_path, site)
        binding = r6.accepted(r6.check(baseline, challenge, checker, r6.policy([site.whole], task=site), work/'source-binding-validation'))
        local = r6.accepted(r6.check(challenge, challenge, checker, r6.policy([site.local, site.whole], True, task=site), work/'challenge-validation'))
    except (RuntimeError, ValueError) as error:
        reason = failure_digest(work); reason.update(error=type(error).__name__+': '+str(error)[:500])
        return {'site_id': site.id, 'status': 'excluded', 'reason': reason}
    context = r6.read_json(captured/'context.json')
    if context['task_id'] != site.id or context['local_declaration'] != site.local: raise ValueError(f'{site.id}: capture identity differs')
    directory = CENSUS_DIR/site.id
    if directory.exists(): raise ValueError('site already frozen: '+site.id)
    (directory/'context').mkdir(parents=True)
    r6.pack(challenge, directory/'challenge.ndjson.gz'); shutil.copyfile(captured/'context.json', directory/'context/local-context.json')
    data = census.pristine()
    patch = ''.join(difflib.unified_diff(data.decode().splitlines(True), instrument(data, site).decode().splitlines(True), fromfile='Pristine.lean', tofile='Frozen.lean'))
    (directory/'permitted.patch').write_text(patch)
    r6.write_json(directory/'expected.json', {'task_id': site.id, 'challenge_sha256': r6.sha(challenge), 'baseline_sha256': r6.sha(baseline), 'environment': env,
                                              'baseline_whole_declaration': baseline_report['targets'][0], 'source_binding_validated': binding['accepted'],
                                              'targets': local['targets'], 'policy': r6.policy([site.local, site.whole], True, task=site)})
    entry = site.entry; shared = {n: r6.sha(CENSUS_DIR/n) for n in SHARED}; shared[f'baseline-{site.whole}.ndjson.gz'] = r6.sha(CENSUS_DIR/f'baseline-{site.whole}.ndjson.gz')
    manifest = {'schema_version': 'r6-task-site-1', 'task_id': site.id, 'census_id': census.CENSUS_ID, 'revision': 1,
                'frozen_at': datetime.now(timezone.utc).isoformat(), 'task_unit': 'local_obligation',
                'upstream': {**census.UPSTREAM, 'line': site.line, 'pristine_sha256': census.SOURCE_HASH, 'proof_byte_span': dict(site.span)},
                'site': {'line': site.line, 'column': entry['column'], 'form': entry['form'], 'line_text': entry['line_text']},
                'original_declaration': site.whole, 'family': entry['family'], 'saved_local_declaration': site.local,
                'local_goal_source': goal_source(entry), 'captured_target': context['target'], 'exposure': entry['exposure'],
                'elaborated_context': 'context/local-context.json', 'expected_declarations': 'expected.json',
                'allowed_imports': ['Mathlib'], 'trusted_instrumentation_imports': ['Capture'],
                'environment_lock': '../upstream-lake-manifest.json', 'compiled_environment_inventory': '../environment-inventory.json.gz',
                'allowed_axioms': r6.AXIOMS, 'baseline_axioms': {t['name']: t['axioms'] for t in local['targets']},
                'axiom_policy': 'transitive_allowlist; report added and removed relative to each baseline',
                'context_policy': 'complete_elaborated_context; auxiliary declaration placeholders recorded but excluded',
                'model_context_policy': 'undecided; reference human proofs are evaluator-only',
                'permitted_modifications': 'permitted.patch; the site token and the trusted import only',
                'acceptance': {'local_obligation_closed': 'expected local theorem/type/definitions/axioms/kernel replay',
                               'whole_declaration_validated': 'original containing theorem/type/definitions/axioms/kernel replay and local-proof reference',
                               'episode_accepted': 'local_obligation_closed AND whole_declaration_validated'},
                'artifacts_sha256': {n: r6.sha(directory/n) for n in SITE_FILES}, 'shared_artifacts_sha256': shared,
                'capture_sha256': r6.sha(CAPTURE), 'vendor_lock_sha256': r6.sha(r6.ROOT/'vendor/sources.lock.json')}
    jsonschema.validate(manifest, r6.read_json(SCHEMA))
    r6.write_json(directory/'manifest.json', manifest)
    return {'site_id': site.id, 'status': 'admitted', 'challenge_sha256': r6.sha(challenge), 'captured_target': context['target'],
            'telescope_entries': len(context['telescope']), 'local_type_sha256': next(t['type_sha256'] for t in local['targets'] if t['name'] == site.local)}


def goal_source(entry):
    """The goal text when the site states it (`have … : G := by omega`); None for bare closers, whose goal is the captured target."""
    text = entry['line_text']
    if entry['form'] in ('named_have', 'anonymous_have', 'have_post_simp'):
        head = text.split(':=', 1)[0]; return head.split(':', 1)[1].strip()
    if entry['form'] == 'term_by': return text.split(':=', 1)[0].strip()
    return None


def freeze_all(run, packages_dir):
    if CENSUS_DIR.joinpath('census.json').exists(): raise ValueError('census is already frozen; introduce a new census revision')
    record = census.census(); compiler, exporter, checker = r6.build_tools(task=r6.D1)
    mounts, lean_path, env = prepare_shared(packages_dir, compiler)
    r6.write_json(run/'runtime.json', r6.runtime_record(checker))
    baselines = {}
    for family in record['families']:
        baselines[family] = freeze_family_baseline(run/('baseline-'+family), family, compiler, exporter, mounts, lean_path, checker)
    results = []
    for entry in record['sites']:
        site = Site(entry); baseline, report = baselines[site.whole]
        started = time.monotonic()
        result = freeze_site(run, site, baseline, report, compiler, exporter, mounts, lean_path, env, checker, packages_dir)
        result['seconds'] = round(time.monotonic()-started, 1); results.append(result); print(json.dumps(result)[:300], flush=True)
    frozen = {**record, 'frozen_at': datetime.now(timezone.utc).isoformat(), 'results': results,
              'admitted': [r['site_id'] for r in results if r['status'] == 'admitted'], 'excluded': [r['site_id'] for r in results if r['status'] != 'admitted'],
              'capture_sha256': r6.sha(CAPTURE), 'schema_sha256': r6.sha(SCHEMA), 'census_module_sha256': r6.sha(r6.ROOT/'census.py'),
              'site_freeze_sha256': r6.sha(Path(__file__)), 'runtime': r6.read_json(run/'runtime.json'),
              'shared_artifacts_sha256': {n: r6.sha(CENSUS_DIR/n) for n in SHARED}, 'baselines_sha256': {f: r6.sha(CENSUS_DIR/f'baseline-{f}.ndjson.gz') for f in record['families']},
              'baseline_exports_sha256': {f: r6.sha(baselines[f][0]) for f in record['families']}}
    r6.write_json(CENSUS_DIR/'census.json', frozen)
    return frozen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packages-dir', type=Path, default=r6.ROOT.parents[1]/'lean-bridge/.lake/packages')
    parser.add_argument('--run-dir', type=Path, required=True)
    args = parser.parse_args()
    run = args.run_dir.resolve(); run.mkdir(parents=True, exist_ok=False)
    frozen = freeze_all(run, args.packages_dir.resolve())
    print(json.dumps({'admitted': frozen['admitted'], 'excluded': frozen['excluded']}, indent=1))


if __name__ == '__main__':
    main()
