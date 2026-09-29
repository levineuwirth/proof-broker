#!/usr/bin/env python3
"""R6-000 deterministic episode: one cvc4 route and consumed Farkas evidence."""
import argparse
import difflib
import gzip
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import uuid

import jsonschema

import events
import instrument
import run as r6

ROOT = r6.ROOT
REPO = ROOT.parents[1]
POLICY = 'cvc4_term_mode_v1'
FARKAS_HELPER = 'ProofBroker.TermMode.farkasContradictN'


class StageFailure(RuntimeError):
    def __init__(self, name, category, message, stats=None):
        super().__init__(message)
        self.stage, self.category, self.stats = name, category, stats


def libraries(binary):
    result = subprocess.run(['ldd', str(binary)], text=True, capture_output=True)
    if result.returncode and 'not a dynamic executable' not in result.stderr + result.stdout:
        raise RuntimeError(f'Cannot identify binary dependencies: {binary}: {result.stderr}')
    return sorted({Path(p) for p in re.findall(r'(/\S+) \(', result.stdout)})


def stage(run, name, binary, argv, mounts, *, compiler=None, env=None, extra_binaries=(),
          wall=150, cpu=120, memory=8 * 1024**3, output_limit=256 * 1024**2):
    records = run/'stages'/name
    records.mkdir(parents=True, exist_ok=False)
    output = records/'output'
    output.mkdir()
    cmd = ['bwrap', '--unshare-all', '--die-with-parent', '--new-session', '--cap-drop', 'ALL',
           '--clearenv', '--setenv', 'PATH', '/no-programs', '--setenv', 'LEAN_ABORT_ON_PANIC', '1',
           '--symlink', 'usr/lib', '/lib', '--symlink', 'usr/lib64', '/lib64',
           '--proc', '/proc', '--dev', '/dev', '--tmpfs', '/tmp', '--dir', '/work', '--chdir', '/work']
    if compiler:
        cmd += ['--ro-bind', str(compiler/'lib'), '/toolchain/lib',
                '--ro-bind', str(compiler/'bin/lean'), '/toolchain/bin/lean',
                '--setenv', 'LEAN_SYSROOT', '/toolchain',
                '--setenv', 'LD_LIBRARY_PATH', '/toolchain/lib/lean:/toolchain/lib']
    deps = set()
    for executable in [binary, *extra_binaries]:
        deps.update(libraries(executable))
    for lib in sorted(deps):
        if compiler and lib.is_relative_to(compiler):
            continue
        cmd += ['--ro-bind', str(lib.resolve()), str(lib)]
    for host, guest in mounts:
        cmd += ['--ro-bind', str(host.resolve()), guest]
    for key, value in (env or {}).items():
        cmd += ['--setenv', key, value]
    program = '/toolchain/bin/program' if compiler else '/runner/bin/program'
    cmd += ['--ro-bind', str(binary), program, '--bind', str(output), '/out', program, *argv]
    spec = {'run': str(run), 'stage': name, 'records': str(records), 'argv': cmd,
            'wall_seconds': wall, 'cpu_seconds': cpu, 'memory_bytes': memory,
            'output_bytes': output_limit}
    r6.write_json(records/'command.json', spec)
    unit = 'r6-'+uuid.uuid4().hex+'.scope'
    scope = ['systemd-run', '--user', '--scope', '--quiet', '--unit='+unit,
             '-p', 'Delegate=yes', '-p', 'OOMPolicy=continue', '-p', 'TasksMax=128',
             '-p', f'RuntimeMaxSec={wall+15}',
             sys.executable, str(ROOT/'supervise.py'), str(records/'command.json')]
    r6.write_json(records/'scope-command.json', scope)
    try:
        result = subprocess.run(scope, capture_output=True, text=True, timeout=wall+30)
    except (subprocess.TimeoutExpired, KeyboardInterrupt):
        # Independent backstop if the monitor cannot complete its own cleanup.
        subprocess.run(['systemctl','--user','kill','--kill-whom=all','--signal=KILL',unit],
                       capture_output=True, timeout=10)
        raise StageFailure(name, 'supervisor_failure', f'{name}: outer watchdog interrupted the scope')
    (records/'supervisor.stdout').write_text(result.stdout)
    (records/'supervisor.stderr').write_text(result.stderr)
    process = records/f'{name}.process.json'
    if not process.exists():
        raise StageFailure(name, 'supervisor_failure', f'{name}: no supervisor verdict: {result.stderr[-1500:]}')
    stats = r6.read_json(process)
    if result.returncode != 0 or stats['exit_code'] != 0 or stats['resource_exhausted']:
        category = 'resource_exhaustion' if stats['resource_exhausted'] else 'stage_rejected'
        if stats.get('monitor_error') or not stats.get('workload_empty_after_cleanup', True):
            category = 'supervisor_failure'
        raise StageFailure(name, category, f'{name}: stage failed; see {records}', stats)
    return output


def observations(run):
    rows = events.read(run/'events.ndjson')
    schema = r6.read_json(ROOT/'schema/event.schema.json')
    for row in rows:
        jsonschema.validate(row, schema)
    return rows


def one(rows, name):
    found = [row for row in rows if row['event'] == name and row['source'] == 'child_report']
    if len(found) != 1:
        raise ValueError(f'Expected one {name} observation; found {len(found)}')
    return found[0]['payload']['data']


def evidence(run):
    rows = observations(run)
    received = one(rows, 'dispatch_received')
    cert = received['certificate']
    if cert['backend']['name'] != 'cvc4' or cert['tier'] != 1 or cert['format'] != 'farkas':
        raise ValueError('Unexpected backend or certificate path')
    dispatch = one(rows, 'dispatch_started')
    if [m['adapter'] for m in dispatch['manifests']] != ['cvc4']:
        raise ValueError('The frozen single-backend policy was not followed')
    if dispatch['prefer_higher_tier'] is not False:
        raise ValueError('Dispatch tier preference changed')
    reified = json.loads(json.dumps(one(rows,'reification_finished')['ir']))
    reified['user_directives']['tier_preference'] = ['1','2']
    if reified != dispatch['ir']:
        raise ValueError('Dispatch changed more than the explicit term-mode tier preference')
    created = one(rows,'certificate_created')
    if created['backend'] != 'cvc4' or created['producer'] != 'sdk_synthesis':
        raise ValueError('Unexpected certificate producer')
    minted = created['certificate']
    bound = one(rows,'certificate_bound')
    if bound['manifest'] != dispatch['manifests'][0]:
        raise ValueError('Certificate was bound to a different backend manifest')
    if bound['before'] != minted or bound['after'] != cert:
        raise ValueError('Certificate envelope binding was not recorded consistently')
    expected_binding = json.loads(json.dumps(minted))
    if minted['backend']['config_hash'] != 'sha256:'+'0'*64:
        raise ValueError('Unexpected pre-binding certificate config hash')
    expected_binding['backend']['config_hash'] = 'sha256:'+events.digest(bound['manifest'])
    if expected_binding != cert:
        raise ValueError('Dispatcher changed more than the permitted manifest hash')
    for event in ['selection_decided', 'certificate_verification_started',
                  'certificate_verification_finished', 'reconstruction_started', 'reconstruction_finished']:
        if one(rows, event)['certificate'] != cert:
            raise ValueError(f'Certificate changed at {event}')
    verified = one(rows, 'certificate_verification_finished')
    if not verified['ok'] or not verified['envelope_ok']:
        raise ValueError('In-process verifier rejected the certificate')
    solver = one(rows, 'solver_finished')
    if solver['backend'] != 'cvc4' or solver['exit_code'] != 0 or solver['stdout'].strip() != 'unsat':
        raise ValueError('Solver did not return the expected unsat result')
    if one(rows,'solver_started')['argv'] != ['cvc4','--lang','smt2','--tlimit-per','5000','--no-interactive']:
        raise ValueError('Solver command or internal limit changed')
    recovery = [r['payload']['data'] for r in rows if r['event']=='recovery_finished'
                and r['payload']['data']['ok']]
    if len(recovery) != 1 or recovery[0]['witness'] != cert['payload']['witness_data']:
        raise ValueError('Synthesized witness is not the certificate witness')
    consumed = one(rows, 'reconstruction_finished')
    if consumed != {'certificate': cert, 'closer': 'term_mode_nat', 'certificate_consumed': True,
                    'derivation_replayed': False, 'residual_closer': 'omega'}:
        raise ValueError('Unexpected reconstruction path')
    sequence = ['reification_started', 'reification_finished', 'dispatch_started', 'solver_started',
                'solver_finished', 'certificate_created', 'certificate_bound', 'selection_decided', 'dispatch_returned',
                'dispatch_received', 'certificate_verification_started', 'certificate_verification_finished',
                'reconstruction_started', 'residual_started', 'residual_finished', 'reconstruction_finished']
    positions = []
    for name in sequence:
        one(rows, name)
        positions.append(next(r['sequence'] for r in rows if r['event']==name))
    if positions != sorted(positions):
        raise ValueError('Evidence stages are out of order')
    sdk_events = {'solver_started','solver_finished','recovery_started','recovery_finished',
                  'certificate_created','certificate_bound','selection_decided','dispatch_returned'}
    for row in rows:
        if row['source'] != 'child_report': continue
        name = row['event']
        if name not in set(sequence) | sdk_events or row['stage'] != 'search':
            raise ValueError('Unexpected observation in the frozen search policy')
        if row['payload']['component'] != ('sdk' if name in sdk_events else 'lean_bridge'):
            raise ValueError('Observation component changed')
    selected = one(rows, 'selection_decided')
    if selected['manifest_order'] != ['cvc4']:
        raise ValueError('Selection manifest order changed')
    if len(selected['attempts']) != 1 or selected['attempts'][0]['outcome'] != 'succeeded':
        raise ValueError('The single attempt did not succeed')
    return {'certificate': cert, 'input_ir': dispatch['ir'],
            'final_ir': received['final_ir'], 'trace': received['trace']}, recovery[0]['route']


def local_policy():
    config = r6.policy([r6.LOCAL])
    config['required_dependency'] = [r6.LOCAL, FARKAS_HELPER]
    return config


def final_validation(run, challenge, solution, checker, expected):
    reports = {}
    for name, config in [('local', local_policy()), ('whole', r6.policy([r6.WHOLE], True))]:
        inp = run/'validation-input'/name
        inp.mkdir(parents=True)
        r6.write_json(inp/'policy.json', config)
        out = stage(run, 'validation-'+name, checker,
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


def seal(run):
    rows = observations(run)
    if not rows or rows[-1]['event'] != 'episode_finished':
        raise ValueError('Cannot seal an incomplete episode')
    # Native compilation products are recorded but not publication dependencies.
    retained, ephemeral = {}, {}
    for p in sorted(run.rglob('*')):
        if not p.is_file() or p.name == 'seal.json':
            continue
        name = str(p.relative_to(run))
        target = ephemeral if ('.olean' in p.name or p.suffix in {'.ilean','.c','.o'}
                               or p.name in {'proof.ndjson','verdict.json'} and '/output/' in name
                               or name.endswith('/export/export.stdout')) else retained
        target[name] = r6.sha(p)
    r6.write_json(run/'seal.json', {'schema_version': 'r6-seal-1', 'event_count': len(rows),
        'last_event_hash': rows[-1]['event_hash'], 'retained_sha256': retained, 'ephemeral_sha256': ephemeral})


def audit(run):
    manifest = r6.read_json(run/'seal.json')
    for name, expected in manifest['retained_sha256'].items():
        p = run/name
        if not p.resolve().is_relative_to(run.resolve()) or r6.sha(p) != expected:
            raise ValueError(f'Sealed artifact changed: {name}')
    rows = observations(run)
    if len(rows) != manifest['event_count'] or rows[-1]['event_hash'] != manifest['last_event_hash']:
        raise ValueError('Sealed event log was truncated or replaced')
    packet, _ = evidence(run)
    if packet != r6.read_json(run/'evidence.json'):
        raise ValueError('Saved evidence differs from observed evidence')
    verdict = r6.read_json(run/'verdict.json')
    jsonschema.validate(verdict,r6.read_json(ROOT/'schema/episode.schema.json'))
    if rows[-1]['event'] != 'episode_finished' or rows[-1]['payload']['verdict_sha256'] != r6.sha(run/'verdict.json'):
        raise ValueError('Episode has no matching terminal verdict')
    if not verdict['accepted'] or not all(verdict[k] for k in
        ['certificate_verified','certificate_consumed','local_obligation_closed','whole_declaration_validated']):
        raise ValueError('Episode does not meet acceptance predicates')
    return verdict


def golden(run, packages):
    manifest, expected = r6.frozen_task()
    compiler, exporter, checker = r6.build_tools()
    overlay, sources, patch = instrument.build(compiler)
    mounts, lean_path, environment = r6.environment(packages.resolve(), compiler)
    with gzip.open(r6.TASK/'environment-inventory.json.gz', 'rt') as f:
        if environment != expected['environment'] or r6.inventory(mounts, compiler) != json.load(f):
            raise ValueError('Frozen upstream environment changed')
    provenance = run/'provenance'
    provenance.mkdir()
    (provenance/'instrumentation.patch').write_text(patch)
    (provenance/'episode_trace.ml').write_text(instrument.SDK_TRACE)
    r6.write_json(provenance/'sources.json', sources)
    for name in ['instrument.py','episode.py','events.py','supervise.py','run.py',
                 'validate/verify_certificate.ml','validate/Replay.lean',
                 'schema/event.schema.json','schema/episode.schema.json']:
        dst = provenance/'harness'/name
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT/name, dst)
    native_root = overlay/'bridge/.lake/build/lib/lean'
    module_libs = [native_root/f'r6_x2dbridge_ProofBroker_{n}.so' for n in ['IR','Trace','Bridge','TermMode','Alethe','Tactic']]
    ffi = overlay/'sdk/_build/default/ffi/proof_broker_ffi.so'
    glue = REPO/'lean-bridge/.lake/build/lib/libpbglue.so'
    solver = Path(shutil.which('cvc4')).resolve()
    solver_version = r6.command([solver,'--version'])
    if not solver_version.startswith('This is CVC4 version 1.8 '):
        raise ValueError('The v1 policy requires CVC4 1.8')
    verify = overlay/'sdk/_build/default/validate/verify_certificate.exe'
    binaries = [compiler/'bin/lean', exporter, checker, ffi, glue, solver, verify, *module_libs]
    for p in binaries:
        if not p.is_file(): raise ValueError(f'Missing built binary: {p}')
    binaries_before = {str(p): r6.sha(p) for p in binaries}
    r6.write_json(provenance/'binaries.json', binaries_before)
    r6.write_json(provenance/'build-environment.json', {
        'solver_version':solver_version, 'ocaml_version':r6.command(['ocamlc','-version']),
        'dune_version':r6.command(['dune','--version']),
        'ocaml_packages':r6.command(['ocamlfind','list']),
        'lean_version':r6.command([compiler/'bin/lean','--version']),
        'systemd_version':r6.command(['systemd-run','--version']),
        'native_glue_source_at_base_sha256':hashlib.sha256(instrument.original('lean-bridge/c/glue.c')).hexdigest(),
        'native_glue_provenance':'prebuilt; binary hash recorded, compilation not attested'})
    r6.write_json(run/'runtime.json', r6.runtime_record(checker))
    inputs = run/'input'
    inputs.mkdir()
    pristine = (r6.TASK/'Pristine.lean').read_text()
    source = r6.instrument(pristine).replace('import Capture\n','import BrokerCapture\n').replace('r6_capture_human','r6_capture_broker')
    (inputs/'Frozen.lean').write_text(source)
    shutil.copyfile(overlay/'BrokerCapture.lean', inputs/'BrokerCapture.lean')
    (provenance/'search.patch').write_text(''.join(difflib.unified_diff(pristine.splitlines(True), source.splitlines(True), fromfile='Pristine.lean', tofile='Frozen.lean')))
    r6.write_json(run/'search-policy.json', {'schema_version':'r6-search-policy-1', 'name':POLICY,
        'parent_task_manifest_sha256':r6.sha(r6.TASK/'manifest.json'), 'task_revision':1,
        'sdk_base_commit':instrument.BASE, 'instrumentation_patch_sha256':r6.sha(provenance/'instrumentation.patch'),
        'source_patch_sha256':r6.sha(provenance/'search.patch'), 'capture_sha256':r6.sha(inputs/'BrokerCapture.lean'),
        'trusted_imports':['BrokerCapture','ProofBroker'], 'manifest_order':['cvc4'], 'attempt_limit':1,
        'context_policy':'complete_local_context; reifier omissions recorded',
        'model_calls':0, 'sampling_settings':None, 'provider':None, 'model_revision':None,
        'solver_internal_limit':{'argument':'--tlimit-per','value_ms':5000},
        'required_local_proof_reference':FARKAS_HELPER,
        'search_stage_wall_seconds':150,'search_stage_cpu_seconds':120,
        'search_stage_memory_bytes':8*1024**3})
    examples = run/'manifests'
    examples.mkdir()
    (examples/'manifest-cvc4.json').write_bytes(instrument.original('examples/manifest-cvc4.json'))
    events.append(run,'episode','episode_started',{'task_manifest_sha256':r6.sha(r6.TASK/'manifest.json'),
        'search_policy_sha256':r6.sha(run/'search-policy.json'), 'challenge_sha256':expected['challenge_sha256']})
    bridge_mounts = [(native_root,'/broker/modules'),(ffi,'/broker/lib/ffi.so'),(glue,'/broker/lib/glue.so')]
    loads = ['--load-dynlib=/broker/lib/glue.so','--load-dynlib=/broker/lib/ffi.so']
    loads += [f'--load-dynlib=/broker/modules/{p.name}' for p in module_libs]
    compile_env = {'LEAN_PATH':lean_path+':/broker/modules:/out'}
    built = stage(run,'capture-build',compiler/'bin/lean',
        [*loads,'-R','/input','-o','/out/BrokerCapture.olean','/input/BrokerCapture.lean'],
        [*mounts,*bridge_mounts,(inputs,'/input')],compiler=compiler,env=compile_env,extra_binaries=[ffi,glue,*module_libs])
    searched = stage(run,'search',compiler/'bin/lean',
        [*loads,'-R','/input','-o','/out/Frozen.olean','/input/Frozen.lean'],
        [*mounts,*bridge_mounts,(inputs,'/input'),(built,'/capture'),(examples,'/manifests'),(solver,'/bin/cvc4')],
        compiler=compiler,extra_binaries=[ffi,glue,solver,*module_libs],
        env={**compile_env,'LEAN_PATH':lean_path+':/broker/modules:/capture', 'PATH':'/bin',
             'PROOF_BROKER_EXAMPLES_DIR':'/manifests','PROOF_BROKER_EPISODE_TRACE':'1',
             'R6_CAPTURE_OUTPUT':'/out/context.json'})
    packet, route = evidence(run)
    if r6.read_json(searched/'context.json') != r6.read_json(r6.TASK/'context/local-context.json'):
        raise ValueError('Broker capture changed the frozen local context')
    events.append(run,'search','context_validated',{
        'captured_context_sha256':r6.sha(searched/'context.json'),
        'frozen_context_sha256':r6.sha(r6.TASK/'context/local-context.json'),
        'comparison':'exact parsed JSON equality; elaborated type checked during final replay'})
    r6.write_json(run/'evidence.json',packet)
    fresh = stage(run,'certificate-check',verify,['/evidence.json','/out/verdict.json'],[(run/'evidence.json','/evidence.json')])
    cert_verdict = r6.read_json(fresh/'verdict.json')
    r6.accepted(cert_verdict)
    r6.write_json(run/'certificate-verdict.json',cert_verdict)
    events.append(run,'certificate-check','independent_certificate_verdict',cert_verdict)
    exported = stage(run,'export',exporter,['Frozen','--',r6.WHOLE,r6.LOCAL,*r6.EXPORT_TARGETS],
        [*mounts,*bridge_mounts,(searched,'/objects'),(built,'/capture')],compiler=compiler,
        env={'LEAN_PATH':lean_path+':/broker/modules:/capture:/objects'},extra_binaries=[ffi,glue,*module_libs])
    solution = exported.parent/'export.stdout'
    r6.pack(solution,run/'solution.ndjson.gz')
    with tempfile.TemporaryDirectory(prefix='r6-golden-challenge-') as temp:
        challenge=Path(temp)/'challenge.ndjson'
        r6.unpack(r6.TASK/'challenge.ndjson.gz',challenge)
        if r6.sha(challenge)!=expected['challenge_sha256']: raise ValueError('Challenge changed')
        reports, delta = final_validation(run,challenge,solution,checker,expected)
    if {str(p):r6.sha(p) for p in binaries} != binaries_before:
        raise ValueError('A loaded binary changed during the episode')
    r6.frozen_task()
    verdict={'schema_version':'r6-episode-1','task_id':'verinf-d1-70','search_policy':POLICY,
        'accepted':True,'search_succeeded':True,'certificate_type':'farkas','trust_tier':1,
        'backend':'cvc4','certificate_producer':'sdk_synthesis','recovery_route':route,
        'certificate_verified':True,'certificate_consumed':True,'derivation_replayed':False,
        'residual_closer':'omega','proof_replayed':True,'local_obligation_closed':True,
        'whole_declaration_validated':True,'axiom_delta':delta,'failure_category':None,
        'local_proof_required_reference':FARKAS_HELPER,
        'model_calls':0,'tokens':0,'model_cost_usd':0,'solution_sha256':r6.sha(solution),
        'challenge_sha256':expected['challenge_sha256'],'manifest_sha256':r6.sha(r6.TASK/'manifest.json'),
        'final_validation':reports,'certificate_validation':cert_verdict,
        'resources':{p.parent.name:r6.read_json(p) for p in sorted((run/'stages').glob('*/*.process.json'))},
        'evidence_receipt_claim':'trusted instrumentation observations; no computation attestation'}
    jsonschema.validate(verdict,r6.read_json(ROOT/'schema/episode.schema.json'))
    r6.write_json(run/'verdict.json',verdict)
    events.append(run,'episode','episode_finished',{'verdict_sha256':r6.sha(run/'verdict.json'),'accepted':True})
    seal(run)
    audit(run)
    print(f'Deterministic episode validated: {run}/verdict.json',flush=True)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('action',choices=['golden','audit','self-test'])
    p.add_argument('--run-dir',type=Path)
    p.add_argument('--packages-dir',type=Path,default=REPO/'lean-bridge/.lake/packages')
    p.add_argument('--episode',type=Path,help='Existing episode for audit or self-test')
    args=p.parse_args()
    if args.action=='audit':
        if args.episode is None: p.error('audit requires --episode')
        audit(args.episode.resolve())
        print('Episode seal and evidence chain verified')
        return
    run=(args.run_dir or ROOT/'runs'/f'broker-{args.action}-{time.time_ns()}').resolve()
    run.mkdir(parents=True,exist_ok=False)
    try:
        if args.action=='self-test':
            from test_episode import integration_tests
            integration_tests(run,args.episode)
        else:
            golden(run,args.packages_dir)
    except Exception as error:
        if not (run/'seal.json').exists():
            failure = {'accepted':False, 'error':str(error),
                       'failure_stage':getattr(error,'stage','harness'),
                       'failure_category':getattr(error,'category','harness_or_evidence_integrity'),
                       'process':getattr(error,'stats',None),
                       'causal_attribution':'unassigned; observed boundary only'}
            try:
                events.append(run,'episode','episode_failed',failure)
            except Exception as log_error:
                failure['failure_log_error'] = str(log_error)
            r6.write_json(run/'failure.json',failure)
        raise


if __name__=='__main__':
    main()
