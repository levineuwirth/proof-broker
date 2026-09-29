"""R6-014 deterministic comparison arm on the fifteen census sites: the Proof Broker's own certificate-consuming route, credential-free.

The route is R6-000's reviewed golden route (`episode.golden`, policy `cvc4_term_mode_v1`), carried to the census sites without editing it:
`proof_broker_term [cvc4]` in the site capture helper, one manifest (CVC4 1.8, from the pinned base commit), one attempt, CVC4 with
`--tlimit-per 5000`, the SDK's own Farkas synthesis on `unsat` (bounded enumeration, then exact support, with its compiled caps), the
in-process bridge verifier, term-mode consumption, then the independent certificate check, export and both kernel replays. Budgets are
the frozen stage defaults. Everything is frozen in `POLICY` before any site runs; `freeze()` writes it and `LOCK` once.

The bridge is built from `instrument.lean_edits` (the R6-000 overlay, which keeps real dispatch and adds the SDK observations) plus the
R6-013 closer observations (`consumption_overlay.EDITS`, which apply unchanged to this text: `closer_selected` before each closer,
`reconstruction_finished` after the core ℤ closer, `closer_returned` after an extension closer) and one more observation for the
reference route: `broker_closer_returned`, the closer `proof_broker` reports after `closeOrFail`. Observation only; built into its own
directory.

The separately identified reference (`REFERENCE`) runs plain `proof_broker [cvc4]` on the same sites, whose certified-and-accepted
extraction may close the goal through `gated_omega` (`omega` re-proving the original goal once a certificate is accepted). Its closer is
recorded, and the result is validated by the same replays; it is not the certificate-consuming arm and is never pooled with it.

Outcomes are derived from each run's own evidence, as the first boundary the run did not pass (`classify`); the learned interface's
categories are not assigned. No model, no provider, no credential.
"""
import argparse
import difflib
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

import consumption_overlay
import events
import instrument
import run as r6
import site_freeze
import site_network
import site_stage
import site_task

POLICY = r6.ROOT/'policies/site-broker-v1.json'
LOCK = r6.ROOT/'policies/site-broker-harness-v1.sha256.json'
FILES = ('site_broker.py', 'test_site_broker.py')
DEST = r6.ROOT/'.cache/broker-instrumented-site-r1'
RUNS = r6.ROOT/'census-runs/deterministic-v1'
ARM, REFERENCE = 'site_cvc4_term_mode_v1', 'site_cvc4_default_closer_v1'
ROUTES = {ARM: ('r6_capture_broker', 'proof_broker_term'), REFERENCE: ('r6_capture_reference', 'proof_broker')}
SOLVER_ARGV = ['cvc4', '--lang', 'smt2', '--tlimit-per', '5000', '--no-interactive']
SOLVER_VERSION_PREFIX = 'This is CVC4 version 1.8 '
BUDGETS = {'wall_seconds': 150, 'cpu_seconds': 120, 'memory_bytes': 8*1024**3, 'output_bytes': 256*1024**2}
FARKAS_HELPER = 'ProofBroker.TermMode.farkasContradictN'
BRIDGE_MODULES = ('IR', 'Trace', 'Bridge', 'TermMode', 'Alethe', 'Tactic')
REFERENCE_ANCHOR = '  let closer ← closeOrFail goal goalType path\n  reportIfRequested "proof_broker" t0 path closer\n'
REFERENCE_EDIT = (REFERENCE_ANCHOR, '''  let closer ← closeOrFail goal goalType path
  episodeEvent "broker_closer_returned" [("closer", toJson closer), ("certificate", toJson path.cert)]
  reportIfRequested "proof_broker" t0 path closer
''')


def lean_edits(text):
    """The R6-000 overlay, the R6-013 closer observations, and the reference route's closer observation; each at exactly one site."""
    text = instrument.lean_edits(text)
    for old, new in (*consumption_overlay.EDITS, REFERENCE_EDIT):
        text = instrument.replace(text, old, new)
    return text


def capture_source(route):
    """The census capture helper with `omega` replaced by the route's tactic over the one frozen adapter; nothing else changes."""
    tactic_name, tactic = ROUTES[route]
    capture = site_freeze.CAPTURE.read_text()
    capture = instrument.replace(capture, 'import Lean\n', 'import Lean\nimport ProofBroker\n')
    capture = instrument.replace(capture, 'elab "r6_capture_human"', f'elab "{tactic_name}"')
    capture = instrument.replace(capture, 'evalTactic (← `(tactic| omega))',
                                 'let adapter := mkIdent (Name.mkSimple "cvc4")\n  evalTactic (← `(tactic| %s [$adapter:ident]))' % tactic)
    return instrument.replace(capture, 'R6 human proof left goals', 'R6 broker proof left goals')


def source_record():
    """Base and overlay digests and the patch against the pinned base, without building."""
    paths = [p for p in r6.command(['git', '-C', instrument.REPO, 'ls-tree', '-r', '--name-only', instrument.BASE, 'sdk/lib', 'sdk/ffi']).splitlines() if '/test/' not in p]
    paths += [f'lean-bridge/ProofBroker/{n}.lean' for n in BRIDGE_MODULES] + ['lean-bridge/ProofBroker.lean']
    sources, diffs = {}, []
    for path in paths:
        base = instrument.original(path).decode()
        changed = lean_edits(base) if path.endswith('ProofBroker/Tactic.lean') else instrument.sdk_edits(Path(path).name, base) if path.startswith('sdk/') else base
        sources[path] = {'base_sha256': r6.hashlib.sha256(base.encode()).hexdigest(), 'instrumented_sha256': r6.hashlib.sha256(changed.encode()).hexdigest()}
        diffs.extend(difflib.unified_diff(base.splitlines(True), changed.splitlines(True), fromfile='a/'+path, tofile='b/'+path))
    return sources, ''.join(diffs)


def build(compiler):
    """`instrument.build` into this arm's directory with this arm's Tactic edits; everything else identical (no task-specific file)."""
    sdk, bridge = DEST/'sdk', DEST/'bridge'
    diffs, sources = [], {}

    def save(repo_path, target, edit=lambda x: x):
        base = instrument.original(repo_path).decode(); patched = edit(base)
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists() or target.read_text() != patched: target.write_text(patched)
        sources[repo_path] = {'base_sha256': r6.hashlib.sha256(base.encode()).hexdigest(), 'instrumented_sha256': r6.sha(target)}
        diffs.extend(difflib.unified_diff(base.splitlines(True), patched.splitlines(True), fromfile='a/'+repo_path, tofile='b/'+repo_path))

    for path in r6.command(['git', '-C', instrument.REPO, 'ls-tree', '-r', '--name-only', instrument.BASE, 'sdk/lib', 'sdk/ffi']).splitlines():
        if '/test/' in path: continue
        save(path, DEST/path, lambda text, name=Path(path).name: instrument.sdk_edits(name, text))
    (sdk/'dune-project').write_text('(lang dune 3.21)\n(name proof_broker)\n(package (name proof_broker))\n')
    (sdk/'lib/episode_trace.ml').write_text(instrument.SDK_TRACE)
    (sdk/'validate').mkdir(exist_ok=True)
    shutil.copyfile(r6.ROOT/'validate/verify_certificate.ml', sdk/'validate/verify_certificate.ml')
    (sdk/'validate/dune').write_text('(executable (name verify_certificate) (libraries proof_broker yojson))\n')
    subprocess.run(['dune', 'build', '--root', str(sdk), 'ffi/proof_broker_ffi.so', 'validate/verify_certificate.exe'], check=True)
    for name in BRIDGE_MODULES:
        save(f'lean-bridge/ProofBroker/{name}.lean', bridge/f'ProofBroker/{name}.lean', lean_edits if name == 'Tactic' else lambda t: t)
    save('lean-bridge/ProofBroker.lean', bridge/'ProofBroker.lean')
    (bridge/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage «r6-bridge»\nlean_lib ProofBroker where\n  precompileModules := true\n')
    (bridge/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
    subprocess.run([str(compiler/'bin/lake'), 'build', 'ProofBroker'], cwd=bridge, check=True)
    return DEST, sources, ''.join(diffs)


def solver():
    path = Path(shutil.which('cvc4')).resolve(); version = r6.command([path, '--version'])
    if not version.startswith(SOLVER_VERSION_PREFIX): raise ValueError('The frozen route requires CVC4 1.8')
    return path, version


def policy_record():
    """Everything the arm and the reference are bound to, computed without running a site."""
    path, version = solver(); sources, patch = source_record()
    return {'schema_version': 'r6-deterministic-policy-1', 'arm': ARM, 'reference': REFERENCE,
            'routes': {ARM: {'tactic': 'proof_broker_term', 'helper_sha256': r6.hashlib.sha256(capture_source(ARM).encode()).hexdigest(),
                             'meaning': 'certificate-consuming: SDK witness synthesis, bridge verification, term-mode consumption, independent check, kernel replays'},
                       REFERENCE: {'tactic': 'proof_broker', 'helper_sha256': r6.hashlib.sha256(capture_source(REFERENCE).encode()).hexdigest(),
                                   'meaning': 'default broker closer (closeOrFail); may re-prove the goal with omega once a certificate is accepted (gated_omega); a reference, never pooled'}},
            'sdk_base_commit': instrument.BASE, 'manifest_order': ['cvc4'], 'attempt_limit': 1,
            'manifest_sha256': r6.hashlib.sha256(instrument.original('examples/manifest-cvc4.json')).hexdigest(),
            'solver': {'path': str(path), 'sha256': r6.sha(path), 'version': version, 'argv': SOLVER_ARGV},
            'witness_synthesis': 'sdk Farkas_search.try_close_then_exact at the base commit: bounded enumeration (bound 3), then exact support; compiled caps',
            'budgets': BUDGETS, 'required_local_proof_reference': FARKAS_HELPER,
            'overlay_patch_sha256': r6.hashlib.sha256(patch.encode()).hexdigest(), 'overlay_sources': sources,
            'sites': list(site_task.primary()), 'site_lock_sha256': r6.sha(site_task.LOCK), 'model_calls': 0, 'credentials': 0,
            'scope': 'frozen before any site runs; outcomes derived from each run\'s own evidence; no full-witness-set baseline is claimed'}


def freeze():
    if POLICY.exists() or LOCK.exists(): raise ValueError('deterministic arm is already frozen')
    site_task.verify_lock()
    with LOCK.open('x') as f: f.write(json.dumps({p: r6.sha(r6.ROOT/p) for p in FILES}, indent=2)+'\n')
    with POLICY.open('xb') as f: f.write(events.canonical(policy_record())+b'\n')
    return r6.sha(POLICY)


def verify():
    """The sources, the frozen policy and the recomputed policy agree."""
    lock = json.loads(LOCK.read_bytes())
    if set(lock) != set(FILES) or any(r6.sha(r6.ROOT/p) != h for p, h in lock.items()): raise ValueError('deterministic arm requires its frozen sources')
    site_task.verify_lock()
    if json.loads(POLICY.read_bytes()) != policy_record(): raise ValueError('deterministic arm policy differs from its recomputation')
    return json.loads(POLICY.read_bytes())


def children(run, stage='search'):
    return [r for r in events.read(run/'events.ndjson') if r['source'] == 'child_report' and r['stage'] == stage]


def stage_log(run, name):
    d = run/'stages'/name
    return ''.join((d/f'{name}.{s}').read_text() for s in ('stdout', 'stderr') if (d/f'{name}.{s}').exists())


def errors_of(log):
    return [line for line in log.splitlines() if ': error: ' in line or line.startswith('error:')]


# The reference route's replay: `site_network.final_validation` verbatim but for its one policy line. The local policy is the human
# baseline's (`run.policy([task.local])`), without the Farkas-helper dependency the certificate-consuming arm must show: a goal the
# default closer re-proves with `omega` is validated as a proof, never counted as certificate consumption.
def reference_validation(run, challenge, solution, checker, expected, task):
    reports = {}
    for name, config in [('local', r6.policy([task.local], task=task)), ('whole', r6.policy([task.whole], True,task=task))]:
        inp = run/'validation-input'/name
        inp.mkdir(parents=True)
        r6.write_json(inp/'policy.json', config)
        out = site_stage.stage(run, 'validation-'+name, checker,
                    ['/challenge.ndjson', '/solution.ndjson', '/policy.json', '/out/verdict.json'],
                    [(challenge, '/challenge.ndjson'), (solution, '/solution.ndjson'), (inp/'policy.json', '/policy.json')])
        report = r6.read_json(out/'verdict.json')
        r6.accepted(report)
        r6.pack(out/'verdict.json', run/f'validation-{name}.raw.json.gz')
        for t in report['targets']:
            t['type_sha256'] = hashlib.sha256(t.pop('type_repr').encode()).hexdigest()
            t['type_hash_format'] = 'Lean-4.32.2-reprStr-Expr-UTF8'
        reports[name] = report
        events.append(run, 'validation-'+name, 'kernel_verdict', report)
    baseline = {t['name']: set(t['axioms']) for t in expected['targets']}
    delta = {t['name']: {'added': sorted(set(t['axioms'])-baseline[t['name']]),
                         'removed': sorted(baseline[t['name']]-set(t['axioms']))}
             for report in reports.values() for t in report['targets']}
    return reports, delta


def classify(run, route, search_failed):
    """The first boundary the search stage did not pass, from its own observations and process record, in pipeline order."""
    rows = children(run); names = [r['event'] for r in rows]; data = {}
    for r in rows: data.setdefault(r['event'], []).append(r['payload']['data'])
    process = r6.read_json(run/'stages/search/search.process.json') if (run/'stages/search/search.process.json').exists() else None
    log = stage_log(run, 'search'); errors = errors_of(log)
    base = {'first_error': errors[0][:500] if errors else None, 'error_count': len(errors), 'observations': names}
    if process is None: return {'outcome': 'search_not_recorded', **base}
    if process['resource_exhausted'] or process['resource_violations'] or process['monitor_error'] or process['observation_error']:
        return {'outcome': 'search_resources_or_monitor', 'resource_exhausted': process['resource_exhausted'], **base}
    if 'reification_finished' not in names: return {'outcome': 'reification_failed', **base}
    if 'dispatch_started' not in names: return {'outcome': 'not_dispatched', **base}
    selection = (data.get('selection_decided') or [None])[-1]
    if 'solver_started' not in names:
        return {'outcome': 'backend_not_invoked', 'attempts': selection['attempts'] if selection else None, **base}
    solved = data['solver_finished'][-1] if 'solver_finished' in names else None
    answer = (solved or {}).get('stdout', '').strip()
    if solved is None or solved.get('exit_code') != 0 or answer != 'unsat':
        return {'outcome': 'solver_did_not_refute', 'solver_answer': answer[:80] if solved else None, 'exit_code': (solved or {}).get('exit_code'), **base}
    received = (data.get('dispatch_received') or [None])[-1]
    cert = (received or {}).get('certificate')
    recovery = [d for d in data.get('recovery_finished', [])]
    if not cert or cert.get('tier') != 1 or cert.get('format') != 'farkas':
        return {'outcome': 'witness_not_recovered', 'recovery': [{k: d.get(k) for k in ('route', 'ok', 'reason')} for d in recovery],
                'certificate_tier': (cert or {}).get('tier'), **base}
    verified = (data.get('certificate_verification_finished') or [None])[-1]
    if not verified or verified.get('ok') is not True or verified.get('envelope_ok') is not True:
        return {'outcome': 'certificate_not_verified', 'reason': (verified or {}).get('reason'), **base}
    if route == REFERENCE:
        returned = data.get('broker_closer_returned') or []
        if search_failed or len(returned) != 1: return {'outcome': 'closer_failed', **base}
        return {'outcome': 'closed', 'closer': returned[0]['closer'], 'certificate': cert, **base}
    selected = data.get('closer_selected') or []
    if not selected: return {'outcome': 'reconstruction_not_started', **base}
    finished = data.get('reconstruction_finished') or []
    if search_failed or len(finished) != 1:
        return {'outcome': 'reconstruction_refused', 'closer': selected[-1]['closer'], 'comparison_type': selected[-1].get('comparison_type'),
                'goal': selected[-1].get('goal'), **base}
    if not (finished[0]['certificate'] == cert == selected[0]['certificate'] and finished[0]['closer'] == selected[0]['closer'] and finished[0]['certificate_consumed'] is True):
        return {'outcome': 'consumption_receipt_inconsistent', **base}
    return {'outcome': 'consumed', 'closer': finished[0]['closer'], 'certificate': cert,
            'recovery_route': next((d['route'] for d in recovery if d.get('ok')), None), **base}


def resources(run):
    records = {p.parent.name: r6.read_json(p) for p in sorted((run/'stages').glob('*/*.process.json'))}
    return {'stages': {k: {x: v.get(x) for x in ('wall_seconds', 'cgroup_cpu_usec', 'cgroup_memory_peak_bytes', 'exit_code')} for k, v in records.items()},
            'wall_seconds': round(sum(v.get('wall_seconds') or 0 for v in records.values()), 3),
            'cpu_seconds': round(sum(v.get('cgroup_cpu_usec') or 0 for v in records.values())/1e6, 3),
            'peak_memory_bytes': max([v.get('cgroup_memory_peak_bytes') or 0 for v in records.values()] or [0])}


def tools_for(packages):
    """The D1 toolchain and environment (every site's environment equals D1's), this arm's bridge, and CVC4 — built or located, never guessed."""
    site_task.same_environment()
    compiler, exporter, checker = r6.build_tools(task=r6.D1)
    dest, sources, patch = build(compiler)
    mounts, lean_path, _ = r6.environment(packages.resolve(), compiler, r6.D1)
    native = dest/'bridge/.lake/build/lib/lean'
    modules = [native/f'r6_x2dbridge_ProofBroker_{n}.so' for n in BRIDGE_MODULES]
    ffi = dest/'sdk/_build/default/ffi/proof_broker_ffi.so'; glue = r6.ROOT.parents[1]/'lean-bridge/.lake/build/lib/libpbglue.so'
    verifier = dest/'sdk/_build/default/validate/verify_certificate.exe'
    path, version = solver()
    loads = ['--load-dynlib=/broker/lib/glue.so', '--load-dynlib=/broker/lib/ffi.so'] + [f'--load-dynlib=/broker/modules/{m.name}' for m in modules]
    return {'compiler': compiler, 'exporter': exporter, 'checker': checker, 'verifier': verifier, 'solver': path, 'solver_version': version,
            'mounts': [*mounts, (native, '/broker/modules'), (ffi, '/broker/lib/ffi.so'), (glue, '/broker/lib/glue.so')],
            'lean_path': lean_path+':/broker/modules', 'loads': loads, 'extras': [ffi, glue, *modules], 'sources': sources, 'patch': patch}


def episode(run, task, route, tools, policy_sha):
    """One site, one route: capture build, search, then — only where the search stage returned with its route's success evidence — the
    independent certificate check (arm only), export and both kernel replays. Always ends with an outcome record, a terminal event and a seal."""
    tactic_name, _ = ROUTES[route]; _, expected = site_task.frozen_site(task)
    run.mkdir(parents=True)
    events.append(run, 'episode', 'episode_started', {'route': route, 'policy_sha256': policy_sha, 'task_manifest_sha256': r6.sha(task.path/'manifest.json'),
                                                     'challenge_sha256': expected['challenge_sha256'], 'model_calls': 0}, task_id=task.id)
    provenance = run/'provenance'; provenance.mkdir()
    (provenance/'instrumentation.patch').write_text(tools['patch']); r6.write_json(provenance/'sources.json', tools['sources'])
    for name in (*FILES, 'site_task.py', 'site_stage.py', 'site_supervise.py', 'site_network.py', 'instrument.py', 'consumption_overlay.py'):
        (provenance/'harness').mkdir(exist_ok=True); shutil.copyfile(r6.ROOT/name, provenance/'harness'/name)
    shutil.copyfile(POLICY, provenance/POLICY.name); shutil.copyfile(LOCK, provenance/LOCK.name)
    binaries = [tools['compiler']/'bin/lean', tools['exporter'], tools['checker'], tools['verifier'], tools['solver'], *tools['extras']]
    before = {str(p): r6.sha(p) for p in binaries}; r6.write_json(provenance/'binaries.json', before)
    inputs = run/'input'; inputs.mkdir()
    source = site_task.instrumented(task, 'BrokerCapture', tactic_name); pristine = site_task.census.pristine().decode()
    (inputs/'Frozen.lean').write_text(source); (inputs/'BrokerCapture.lean').write_text(capture_source(route))
    (inputs/'source.patch').write_text(''.join(difflib.unified_diff(pristine.splitlines(True), source.splitlines(True), fromfile='Pristine.lean', tofile='Frozen.lean')))
    manifests = run/'manifests'; manifests.mkdir(); (manifests/'manifest-cvc4.json').write_bytes(instrument.original('examples/manifest-cvc4.json'))
    r6.write_json(run/'search-policy.json', {'schema_version': 'r6-deterministic-run-1', 'route': route, 'policy_sha256': policy_sha, 'lock_sha256': r6.sha(LOCK),
                                             'task_id': task.id, 'manifest_sha256': r6.sha(task.path/'manifest.json'), 'model_calls': 0})
    T = tools; compiler = T['compiler']; outcome = None; accepted = False; verdict = None
    try:
        built = site_stage.stage(run, 'capture-build', compiler/'bin/lean', [*T['loads'], '-R', '/input', '-o', '/out/BrokerCapture.olean', '/input/BrokerCapture.lean'],
                                 [*T['mounts'], (inputs, '/input')], compiler=compiler, env={'LEAN_PATH': T['lean_path']+':/out'}, extra_binaries=T['extras'])
        failed = False
        try:
            searched = site_stage.stage(run, 'search', compiler/'bin/lean', [*T['loads'], '-R', '/input', '-o', '/out/Frozen.olean', '/input/Frozen.lean'],
                [*T['mounts'], (inputs, '/input'), (built, '/capture'), (manifests, '/manifests'), (T['solver'], '/bin/cvc4')], compiler=compiler,
                extra_binaries=[*T['extras'], T['solver']], capture_events=True,
                env={'LEAN_PATH': T['lean_path']+':/capture', 'PATH': '/bin', 'PROOF_BROKER_EXAMPLES_DIR': '/manifests', 'PROOF_BROKER_EPISODE_TRACE': '1',
                     'R6_CAPTURE_OUTPUT': '/out/context.json'})
        except site_stage.StageFailure:
            failed = True; searched = run/'stages/search/output'
        outcome = classify(run, route, failed)
        success = outcome['outcome'] == ('consumed' if route == ARM else 'closed')
        if success:
            if r6.read_json(searched/'context.json') != r6.read_json(task.path/'context/local-context.json'): raise ValueError('search changed the frozen context')
            events.append(run, 'search', 'context_validated', {'captured_context_sha256': r6.sha(searched/'context.json'),
                                                                'frozen_context_sha256': r6.sha(task.path/'context/local-context.json')})
            data = {r['event']: r['payload']['data'] for r in children(run)}
            packet = {'certificate': outcome['certificate'], 'input_ir': data['dispatch_started']['ir'],
                      'final_ir': data['dispatch_received']['final_ir'], 'trace': data['dispatch_received']['trace']}
            r6.write_json(run/'evidence.json', packet)
            try:
                checked = site_stage.stage(run, 'certificate-check', T['verifier'], ['/evidence.json', '/out/verdict.json'], [(run/'evidence.json', '/evidence.json')])
                report = r6.read_json(checked/'verdict.json')
            except site_stage.StageFailure:
                report = r6.read_json(run/'stages/certificate-check/output/verdict.json') if (run/'stages/certificate-check/output/verdict.json').exists() else None
            r6.write_json(run/'certificate-verdict.json', report)
            events.append(run, 'certificate-check', 'independent_certificate_verdict', report or {'accepted': None})
            if not (report and report.get('accepted') is True):
                outcome = {**outcome, 'outcome': 'independent_check_rejected'}
            else:
                exported = site_stage.stage(run, 'export', T['exporter'], ['Frozen', '--', task.whole, task.local, *r6.EXPORT_TARGETS],
                    [*T['mounts'], (searched, '/objects'), (built, '/capture')], compiler=compiler,
                    env={'LEAN_PATH': T['lean_path']+':/capture:/objects'}, extra_binaries=T['extras'])
                solution = exported.parent/'export.stdout'; r6.pack(solution, run/'solution.ndjson.gz')
                with tempfile.TemporaryDirectory(prefix='r6-broker-challenge-') as temp:
                    challenge = Path(temp)/'challenge.ndjson'; r6.unpack(task.path/'challenge.ndjson.gz', challenge)
                    if r6.sha(challenge) != expected['challenge_sha256']: raise ValueError('challenge changed')
                    validate = site_network.final_validation if route == ARM else reference_validation
                    reports, delta = validate(run, challenge, solution, T['checker'], expected, task)
                verdict = {'schema_version': 'r6-deterministic-verdict-1', 'task_id': task.id, 'route': route, 'closer': outcome['closer'],
                           'certificate_validation': report, 'final_validation': reports, 'axiom_delta': delta, 'solution_sha256': r6.sha(solution),
                           'local_obligation_closed': True, 'whole_declaration_validated': True, 'model_calls': 0}
                r6.write_json(run/'verdict.json', verdict); accepted = all(v == {'added': [], 'removed': []} for v in delta.values())
                outcome = {**outcome, 'outcome': 'proof' if route == ARM else 'closed_and_validated', 'axiom_delta_empty': accepted}
    except site_stage.StageFailure as failure:
        outcome = {**(outcome or {}), 'outcome': f'{failure.stage}_failed', 'stage_category': failure.category}
    except Exception as error:  # the record is sealed on every path
        outcome = {**(outcome or {}), 'outcome': 'harness_failure', 'error': type(error).__name__+': '+str(error)[:500]}
    if {str(p): r6.sha(p) for p in binaries} != before: outcome = {**outcome, 'outcome': 'binary_changed_during_episode'}; accepted = False
    outcome = {k: v for k, v in outcome.items() if k != 'certificate'}
    record = {'schema_version': 'r6-deterministic-outcome-1', 'task_id': task.id, 'route': route, **outcome, 'resources': resources(run),
              'verdict_sha256': r6.sha(run/'verdict.json') if verdict else None}
    r6.write_json(run/'outcome.json', record)
    events.append(run, 'episode', 'episode_finished' if verdict and accepted else 'episode_rejected', {'outcome_sha256': r6.sha(run/'outcome.json'), 'outcome': record['outcome']})
    site_network.seal(run, bool(verdict and accepted))
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('freeze', 'run'))
    parser.add_argument('--packages-dir', type=Path, default=r6.ROOT.parents[1]/'lean-bridge/.lake/packages')
    parser.add_argument('--runs', type=Path, default=RUNS)
    parser.add_argument('--sites', nargs='*')
    args = parser.parse_args()
    if args.command == 'freeze': print(freeze()); return
    policy = verify(); policy_sha = r6.sha(POLICY); runs = args.runs.resolve()
    if (runs/'deterministic.json').exists(): raise SystemExit('already recorded: '+str(runs))
    tools = tools_for(args.packages_dir)
    if r6.sha(tools['solver']) != policy['solver']['sha256'] or tools['patch'] != source_record()[1]: raise SystemExit('built tools differ from the frozen policy')
    results = {}
    for site_id in (args.sites or policy['sites']):
        for route in (ARM, REFERENCE):
            started = time.monotonic()
            results.setdefault(route, {})[site_id] = episode(runs/route/site_id, site_task.get(site_id), route, tools, policy_sha)
            print(json.dumps({'site': site_id, 'route': route, 'outcome': results[route][site_id]['outcome'], 'seconds': round(time.monotonic()-started, 1)}), flush=True)
    r6.write_json(runs/'deterministic.json', {'schema_version': 'r6-deterministic-summary-1', 'policy_sha256': policy_sha, 'lock_sha256': r6.sha(LOCK),
        'sites': list(args.sites or policy['sites']), 'results': results, 'program_sha256': r6.sha(Path(__file__)),
        'scope': 'credential-free native runs; outcomes from each run\'s own evidence; the reference route is never pooled with the arm'})


if __name__ == '__main__':
    main()
