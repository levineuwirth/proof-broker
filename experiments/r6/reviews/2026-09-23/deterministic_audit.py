#!/usr/bin/env python3
"""R6-014 review repair (finding 4): an independent audit of the deterministic arm's retained artifacts. Non-locked; read-only.

The arm's own controls (`test_site_broker.py`, locked) check its sources and re-read its runs, but they took the run population from the
summary they were checking and never derived a verdict from its raw replay reports. This auditor reads the retained runs as evidence:

* **population**: exactly fifteen reviewed sites × two routes, from the reviewed primary population (never from the summary); exactly those
  run directories and the summary beside them; the summary bound to the frozen policy, lock and program;
* **per run**: the event chain and seal (every retained file at its digest, none unlisted); the identity and search policy; the retained
  harness, policy and lock copies equal to the locked sources; the overlay sources and patch recomputed; the binaries at the digests the
  current tools have; the inputs and manifest recomputed; each stage's command rebuilt by the production `site_stage.stage` (its launch
  stubbed) from the episode's parameters and compared byte for byte, with the frozen budgets; the supervisor's stage receipts equal to its
  process records; the exact receipt sequence for the run's outcome;
* **search outcome**: recomputed by `classify` from the child observations, with its fields; downstream artifacts present exactly when the
  route's success evidence is;
* **proofs**: the captured context equal to the frozen one; the evidence packet rebuilt from the observations; the certificate check
  **re-executed** on the packet and equal to the recorded verdict and its receipt; the consumption receipt (arm) or the closer receipt
  (reference); the export targets and solution digest; both kernel replays **derived from their raw reports** (accepted, the frozen target
  and its frozen type digest, only standard axioms) and equal to the verdict and its receipts, with the axiom delta recomputed;
* **outcome record**: the costs recomputed, the verdict digest, the summary entry, the terminal event and the seal's acceptance.

Each case is named; the first failure rejects the audit. Controls: `deterministic_audit_controls.py`.

Revision 2 (R6-014 revision 2 review):
* finding 3 — every run's search observations follow the frozen grammar for its route and outcome (`OBSERVATIONS`: event, component,
  order); every certificate-bearing observation carries the certificate the bridge received (the SDK's `certificate_created` differs only
  by the unbound backend configuration digest that `certificate_bound` fills in); wherever the bridge claims verification, on refused runs
  too, the packet is rebuilt from the observations and the independent checker re-executed; the selected closer is derived from the pinned
  dispatch (`pinned_closer`, the cohort auditor's, for this IR and certificate without the extension), never read from the observation;
* finding 4 — the retained solution is joined to the export that the replays read: its decompressed bytes equal the retained export stdout
  and its sealed digest, its size is the export's recorded output and receipt, and it contains the site's local and whole declarations;
  that the replays read these bytes is established by the stage commands and the chain, not by re-running them;
* finding 5 — every search stage terminated cleanly (no monitor, observation or resource failure, the workload empty after cleanup); only
  its exit code may carry a mathematical refusal, and a proof requires exit 0;
* the complete per-outcome case population is computed and gated before acceptance (`audit:case_population_complete`).

Revision 3 (R6-014 revision 3 review, finding 1): the export stdout is ignored by version control and survives only as its sealed digest.
The solution join therefore rests on the retained bindings — the decompressed solution's digest equals the verdict's and the sealed export
stdout digest, its size the export's recorded output and receipt, and it names the site's declarations — and compares the stdout bytes
only when the file is present; the result reports for how many runs it was (`export_stdout_compared`).
"""
import argparse
import copy
import difflib
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from types import SimpleNamespace
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import events
import instrument
import run as r6
import site_broker as broker
import site_network
import site_stage
import site_task

RECORDED = broker.RUNS  # the layout the runs were recorded under; a copy is audited against it
SUCCESS = {broker.ARM: 'consumed', broker.REFERENCE: 'closed'}
PROVED = {broker.ARM: 'proof', broker.REFERENCE: 'closed_and_validated'}
PROVENANCE = (*broker.FILES, 'site_task.py', 'site_stage.py', 'site_supervise.py', 'site_network.py', 'instrument.py', 'consumption_overlay.py')
STAGES_REJECTED = ('capture-build', 'search')
STAGES_PROVED = ('capture-build', 'search', 'certificate-check', 'export', 'validation-local', 'validation-whole')
UNBOUND_CONFIG = 'sha256:'+'0'*64
STDOUT_COMPARED = []  # revision 3: per proved run, whether the ephemeral export stdout was present to compare
# Revision 2: the frozen observation grammar, (event, component) in order, by route and search outcome (as the pinned overlay emits them).
_OPEN = [('reification_started', 'lean_bridge'), ('reification_finished', 'lean_bridge'), ('dispatch_started', 'lean_bridge')]
_SOLVED = [('solver_started', 'sdk'), ('solver_finished', 'sdk')]
_RECOVERED = [('recovery_started', 'sdk'), ('recovery_finished', 'sdk')]
_RETURNED = [('certificate_created', 'sdk'), ('certificate_bound', 'sdk'), ('selection_decided', 'sdk'), ('dispatch_returned', 'sdk'), ('dispatch_received', 'lean_bridge'),
             ('certificate_verification_started', 'lean_bridge'), ('certificate_verification_finished', 'lean_bridge')]
_ARM_RECONSTRUCTION = [('reconstruction_started', 'lean_bridge'), ('closer_selected', 'lean_bridge')]
OBSERVATIONS = {
    (broker.ARM, 'consumed'): _OPEN+_SOLVED+_RECOVERED+_RETURNED+_ARM_RECONSTRUCTION+[('residual_started', 'lean_bridge'), ('residual_finished', 'lean_bridge'), ('reconstruction_finished', 'lean_bridge')],
    (broker.ARM, 'reconstruction_refused'): _OPEN+_SOLVED+_RECOVERED+_RETURNED+_ARM_RECONSTRUCTION,
    (broker.ARM, 'witness_not_recovered'): _OPEN+_SOLVED+_RECOVERED+_RECOVERED+_RETURNED+[('reconstruction_started', 'lean_bridge')],
    (broker.ARM, 'backend_not_invoked'): _OPEN+[('dispatch_received', 'lean_bridge')],
    (broker.REFERENCE, 'closed'): _OPEN+_SOLVED+_RECOVERED+_RETURNED+[('broker_closer_returned', 'lean_bridge')],
    (broker.REFERENCE, 'witness_not_recovered'): _OPEN+_SOLVED+_RECOVERED+_RECOVERED+_RETURNED+[('broker_closer_returned', 'lean_bridge')],
    (broker.REFERENCE, 'backend_not_invoked'): _OPEN+[('dispatch_received', 'lean_bridge')]}


def pinned_closer(ir, cert, extension=False):
    """`reviews/2026-09-23/cohort_v8_audit.py`'s derivation of `runTermModeOnGoal`'s branch at e627efe, verbatim."""
    payloads = ir['goal'].get('payloads') or {}
    nat = any(v.get('type') == 'Nat' for v in ir['context']['free_vars']) or \
          any(isinstance(v, dict) and v.get('kind') == 'nat_nonlinear_atom' for v in (payloads.values() if isinstance(payloads, dict) else ()))
    hint = ((cert.get('payload') or {}).get('strategy_hint')) or ''
    if nat: return None if hint == 'case_split_farkas' else 'term_mode_nat'
    if ir['context'].get('type_vars'): return None if (hint == 'case_split_farkas' or not extension) else 'term_mode_poly'
    if hint == 'case_split_farkas': return 'term_mode_case_split' if extension else None
    return 'term_mode_int'  # no extension: the core ℤ closer, whatever the fragment


def verifier_on_packet(tools, packet):
    with tempfile.TemporaryDirectory(prefix='r6-014-det-packet-') as temp:
        path = Path(temp)/'evidence.json'; r6.write_json(path, packet); return verifier_verdict(tools, path)


def observations_bound(a, name, run, route, search_outcome, tools):
    """Revision 2 (finding 3): the grammar, the certificate at every observation, re-checked wherever verification is claimed, the pinned closer."""
    rows = broker.children(run); problems = []
    grammar = [(r['event'], r['payload'].get('component')) for r in rows]
    if grammar != OBSERVATIONS.get((route, search_outcome)) or any(r['stage'] != 'search' for r in rows): problems.append('grammar')
    data = {r['event']: r['payload']['data'] for r in rows}
    received = data.get('dispatch_received') or {}; cert = received.get('certificate')
    if cert is not None:
        for r in rows:
            d = r['payload']['data']
            if 'certificate' not in d or r['event'] in ('dispatch_received',): continue
            if r['event'] == 'certificate_created':
                unbound = copy.deepcopy(cert); unbound['backend'] = {**unbound['backend'], 'config_hash': UNBOUND_CONFIG}
                if d['certificate'] != unbound: problems.append('certificate_created')
            elif d['certificate'] != cert: problems.append('certificate at '+r['event'])
        bound = data.get('certificate_bound') or {}
        if bound.get('after') != cert or bound.get('before') != (data.get('certificate_created') or {}).get('certificate'): problems.append('certificate_bound')
        verified = data.get('certificate_verification_finished') or {}
        if verified.get('ok') is True:
            packet = {'certificate': cert, 'input_ir': data['dispatch_started']['ir'], 'final_ir': received['final_ir'], 'trace': received['trace']}
            recheck = verifier_on_packet(tools, packet)
            if not (recheck and recheck.get('accepted') is True and verified.get('envelope_ok') is True): problems.append('claimed verification not reproduced by the checker')
        if route == broker.ARM and 'closer_selected' in data:
            derived = pinned_closer(data['dispatch_started']['ir'], cert, False)
            if data['closer_selected']['closer'] != derived: problems.append(f"closer {data['closer_selected']['closer']}, pinned {derived}")
    elif any('certificate' in r['payload']['data'] for r in rows if r['event'] != 'dispatch_received'): problems.append('certificate without dispatch')
    a.require(not problems, f'{name}:search:observations_bound', '; '.join(problems))


def expected_cases(primary, outcomes):
    """Revision 2: the complete case population, by each run's recorded outcome; the audit is accepted only if it evaluated exactly these."""
    names = ['population:reviewed_fifteen_sites', 'population:exactly_fifteen_sites_by_two_routes', 'population:summary_bound', 'tools:equal_to_the_frozen_policy']
    for route in (broker.ARM, broker.REFERENCE):
        for site in primary:
            n = f'{route}/{site}'
            names += [f'{n}:{c}' for c in ('chain:valid', 'seal:every_retained_file_at_its_digest', 'chain:expected_sequence', 'identity:bound',
                                            'provenance:locked_sources_and_overlay', 'provenance:binaries_at_current_tool_digests', 'inputs:recomputed',
                                            'stages:exactly_the_outcome_path', 'commands:rebuilt_by_the_stage_function', 'search:terminated_cleanly',
                                            'search:outcome_recomputed', 'search:fields_recomputed', 'search:observations_bound', 'search:downstream_exactly_when_proved',
                                            'outcome:record_bound')]
            if outcomes[(route, site)] == PROVED[route]:
                names += [f'{n}:proof:{c}' for c in ('context_frozen', 'evidence_rebuilt_from_observations', 'certificate_check_reexecuted',
                                                     'consumption_receipt' if route == broker.ARM else 'closer_receipt', 'solution_bound', 'verdict_shape')]
                names += [f'{n}:kernel:derived_from_raw_reports']
    return names


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


def sequence(outcome):
    s = [('episode', 'episode_started'), ('capture-build', 'stage_started'), ('capture-build', 'stage_finished'), ('search', 'stage_started'), ('search', 'stage_finished')]
    if outcome not in PROVED.values(): return s+[('episode', 'episode_rejected')]
    return s+[('search', 'context_validated'), ('certificate-check', 'stage_started'), ('certificate-check', 'stage_finished'),
              ('certificate-check', 'independent_certificate_verdict'), ('export', 'stage_started'), ('export', 'stage_finished'),
              ('validation-local', 'stage_started'), ('validation-local', 'stage_finished'), ('validation-local', 'kernel_verdict'),
              ('validation-whole', 'stage_started'), ('validation-whole', 'stage_finished'), ('validation-whole', 'kernel_verdict'), ('episode', 'episode_finished')]


class Launched(Exception): pass


def rebuilt_command(recorded_run, name, binary, argv, mounts, task, **kwargs):
    """The production stage function, run to the point where it records its command, in a scratch run; the launch is stubbed.
    The scratch output directory is renamed to the recorded one; everything else is the function's own bytes."""
    with tempfile.TemporaryDirectory(prefix='r6-014-det-command-') as temp:
        scratch = Path(temp)/'run'; scratch.mkdir()
        events.append(scratch, 'episode', 'episode_started', {}, task_id=task.id)
        def launch(*args, **kwargs): raise Launched()
        stub = SimpleNamespace(run=launch, TimeoutExpired=subprocess.TimeoutExpired)  # only the stage's own launch; `libraries` still runs ldd
        with patch.object(site_stage, 'subprocess', stub):
            try: site_stage.stage(scratch, name, binary, argv, mounts, **kwargs)
            except Launched: pass
        spec = load(scratch/'stages'/name/'command.json')
        out = str(scratch/'stages'/name/'output')
        spec['argv'] = [str(recorded_run/'stages'/name/'output') if x == out else x for x in spec['argv']]
        spec['run'], spec['records'] = str(recorded_run), str(recorded_run/'stages'/name)
        return spec


CHALLENGE = re.compile(r'.*/r6-broker-challenge-[A-Za-z0-9_]+/challenge\.ndjson')
PLACEHOLDER = Path('/r6-broker-challenge-recorded/challenge.ndjson')


def expected_commands(recorded, route, task, tools, stages):
    T = tools; compiler = T['compiler']; inputs, manifests = recorded/'input', recorded/'manifests'
    built, searched = recorded/'stages/capture-build/output', recorded/'stages/search/output'
    out = {'capture-build': rebuilt_command(recorded, 'capture-build', compiler/'bin/lean',
                [*T['loads'], '-R', '/input', '-o', '/out/BrokerCapture.olean', '/input/BrokerCapture.lean'], [*T['mounts'], (inputs, '/input')], task,
                compiler=compiler, env={'LEAN_PATH': T['lean_path']+':/out'}, extra_binaries=T['extras']),
           'search': rebuilt_command(recorded, 'search', compiler/'bin/lean', [*T['loads'], '-R', '/input', '-o', '/out/Frozen.olean', '/input/Frozen.lean'],
                [*T['mounts'], (inputs, '/input'), (built, '/capture'), (manifests, '/manifests'), (T['solver'], '/bin/cvc4')], task, compiler=compiler,
                extra_binaries=[*T['extras'], T['solver']], capture_events=True,
                env={'LEAN_PATH': T['lean_path']+':/capture', 'PATH': '/bin', 'PROOF_BROKER_EXAMPLES_DIR': '/manifests', 'PROOF_BROKER_EPISODE_TRACE': '1',
                     'R6_CAPTURE_OUTPUT': '/out/context.json'})}
    if 'certificate-check' in stages:
        out['certificate-check'] = rebuilt_command(recorded, 'certificate-check', T['verifier'], ['/evidence.json', '/out/verdict.json'], [(recorded/'evidence.json', '/evidence.json')], task)
        out['export'] = rebuilt_command(recorded, 'export', T['exporter'], ['Frozen', '--', task.whole, task.local, *r6.EXPORT_TARGETS],
                [*T['mounts'], (searched, '/objects'), (built, '/capture')], task, compiler=compiler, env={'LEAN_PATH': T['lean_path']+':/capture:/objects'},
                extra_binaries=T['extras'])
        solution = recorded/'stages/export/export.stdout'
        for kind in ('local', 'whole'):
            out['validation-'+kind] = rebuilt_command(recorded, 'validation-'+kind, T['checker'], ['/challenge.ndjson', '/solution.ndjson', '/policy.json', '/out/verdict.json'],
                [(PLACEHOLDER, '/challenge.ndjson'), (solution, '/solution.ndjson'), (recorded/'validation-input'/kind/'policy.json', '/policy.json')], task)
    return out


def masked(spec):
    """The validation challenge is unpacked into a fresh temporary directory; only its location is masked, and only in that form."""
    spec = copy.deepcopy(spec); argv = spec['argv']
    for i in range(len(argv)-2):
        if argv[i] == '--ro-bind' and argv[i+2] == '/challenge.ndjson' and CHALLENGE.fullmatch(argv[i+1]): argv[i+1] = str(PLACEHOLDER)
    return spec


def verifier_verdict(tools, evidence):
    with tempfile.TemporaryDirectory(prefix='r6-014-det-verify-') as temp:
        out = Path(temp)/'verdict.json'
        subprocess.run([str(tools['verifier']), str(evidence), str(out)], capture_output=True, timeout=120)
        return load(out) if out.exists() else None


def kernel(a, name, run, task, route, verdict, receipts, frozen):
    baseline = {t['name']: t for t in frozen['targets']}; delta = {}; problems = []
    local_policy = site_network.local_policy(task) if route == broker.ARM else r6.policy([task.local], task=task)
    for kind, target, policy in (('local', task.local, local_policy), ('whole', task.whole, r6.policy([task.whole], True, task=task))):
        try:
            if load(run/'validation-input'/kind/'policy.json') != policy: problems.append(kind+': validation policy'); continue
            with gzip.open(run/f'validation-{kind}.raw.json.gz', 'rb') as f: raw = f.read(4*1024**2+1)
            report = json.loads(raw)
            if len(raw) > 4*1024**2 or len(report['targets']) != 1: problems.append(kind+': report shape'); continue
            t = report['targets'][0]; t['type_sha256'] = hashlib.sha256(t.pop('type_repr').encode()).hexdigest(); t['type_hash_format'] = 'Lean-4.32.2-reprStr-Expr-UTF8'
            if not (report['accepted'] is True and report['stage'] == 'complete' and report['kernel_version'] == '4.32.2'
                    and report['local_proof_binding_checked'] is (policy.get('required_dependency') is not None)
                    and report['checked_declarations'] > 0 and t['name'] == target and all(t[k] is True for k in ('declaration_exists', 'statement_and_dependencies_match', 'kernel_accepted'))
                    and t['type_sha256'] == baseline[target]['type_sha256'] and set(t['axioms']) <= set(r6.AXIOMS)):
                problems.append(kind+': raw report content or frozen type')
            if not (report == verdict['final_validation'][kind] == receipts[('validation-'+kind, 'kernel_verdict')]): problems.append(kind+': raw report, verdict and receipt differ')
            delta[target] = {'added': sorted(set(t['axioms'])-set(baseline[target]['axioms'])), 'removed': sorted(set(baseline[target]['axioms'])-set(t['axioms']))}
        except (OSError, KeyError, ValueError, EOFError, gzip.BadGzipFile) as error: problems.append(f'{kind}: {type(error).__name__}: {error}')
    if verdict['axiom_delta'] != delta: problems.append('axiom delta')
    a.require(not problems, f'{name}:kernel:derived_from_raw_reports', '; '.join(problems))
    return all(v == {'added': [], 'removed': []} for v in delta.values())


def audit_run(a, root, route, site, tools, policy_sha, summary, reviewed):
    name = f'{route}/{site}'; run = root/route/site; recorded = RECORDED/route/site; task = site_task.get(site); _, frozen = site_task.frozen_site(task)
    try: rows = events.read(run/'events.ndjson'); seal = load(run/'seal.json')
    except (OSError, ValueError) as error: a.require(False, f'{name}:chain:valid', str(error))
    a.require(True, f'{name}:chain:valid')
    files = sorted(str(p.relative_to(run)) for p in run.rglob('*') if p.is_file() and p.name != 'seal.json')
    listed = {**seal['retained_sha256'], **seal['ephemeral_sha256']}
    a.require(seal['event_count'] == len(rows) and seal['last_event_hash'] == rows[-1]['event_hash'] and set(seal['retained_sha256']) <= set(files)
              and all(f in listed for f in files) and all(r6.sha(run/k) == v for k, v in seal['retained_sha256'].items()), f'{name}:seal:every_retained_file_at_its_digest')
    outcome = load(run/'outcome.json')
    supervisor = [(r['stage'], r['event']) for r in rows if r['source'] == 'supervisor']
    a.require(supervisor == sequence(outcome['outcome']) and all(r['task_id'] == site for r in rows), f'{name}:chain:expected_sequence', str(supervisor))
    receipts = {(r['stage'], r['event']): r['payload'] for r in rows if r['source'] == 'supervisor'}
    a.require(receipts[('episode', 'episode_started')] == {'route': route, 'policy_sha256': policy_sha, 'task_manifest_sha256': r6.sha(task.path/'manifest.json'),
                                                          'challenge_sha256': frozen['challenge_sha256'], 'model_calls': 0}
              and load(run/'search-policy.json') == {'schema_version': 'r6-deterministic-run-1', 'route': route, 'policy_sha256': policy_sha, 'lock_sha256': r6.sha(broker.LOCK),
                                                     'task_id': site, 'manifest_sha256': r6.sha(task.path/'manifest.json'), 'model_calls': 0}, f'{name}:identity:bound')
    lock = load(broker.LOCK)
    sources, patch_text = reviewed['sources']
    a.require(all((run/'provenance/harness'/f).read_bytes() == (ROOT/f).read_bytes() for f in PROVENANCE) and sorted(p.name for p in (run/'provenance/harness').iterdir()) == sorted(PROVENANCE)
              and all(r6.sha(run/'provenance/harness'/f) == lock[f] for f in broker.FILES)
              and (run/'provenance'/broker.POLICY.name).read_bytes() == broker.POLICY.read_bytes() and (run/'provenance'/broker.LOCK.name).read_bytes() == broker.LOCK.read_bytes()
              and load(run/'provenance/sources.json') == sources and (run/'provenance/instrumentation.patch').read_text() == patch_text, f'{name}:provenance:locked_sources_and_overlay')
    a.require(load(run/'provenance/binaries.json') == reviewed['binaries'], f'{name}:provenance:binaries_at_current_tool_digests')
    pristine = site_task.census.pristine().decode(); source = site_task.instrumented(task, 'BrokerCapture', broker.ROUTES[route][0])
    a.require((run/'input/Frozen.lean').read_text() == source and (run/'input/BrokerCapture.lean').read_text() == broker.capture_source(route)
              and (run/'input/source.patch').read_text() == ''.join(difflib.unified_diff(pristine.splitlines(True), source.splitlines(True), fromfile='Pristine.lean', tofile='Frozen.lean'))
              and (run/'manifests/manifest-cvc4.json').read_bytes() == instrument.original('examples/manifest-cvc4.json')
              and r6.sha(run/'manifests/manifest-cvc4.json') == reviewed['policy']['manifest_sha256'], f'{name}:inputs:recomputed')
    proved = outcome['outcome'] == PROVED[route]
    stages = STAGES_PROVED if proved else STAGES_REJECTED
    a.require(sorted(p.name for p in (run/'stages').iterdir()) == sorted(stages), f'{name}:stages:exactly_the_outcome_path')
    expected = expected_commands(recorded, route, task, tools, stages); problems = []
    for stage in stages:
        spec = masked(load(run/'stages'/stage/'command.json'))
        if spec != expected[stage]:
            diff = next((i for i, (x, y) in enumerate(zip(spec['argv'], expected[stage]['argv'])) if x != y), None)
            problems.append(f'{stage}: first difference at {diff}')
        if {k: spec[k] for k in ('wall_seconds', 'cpu_seconds', 'memory_bytes', 'output_bytes')} != broker.BUDGETS: problems.append(stage+': budgets')
        process = load(run/'stages'/stage/f'{stage}.process.json')
        if receipts[(stage, 'stage_finished')] != process: problems.append(stage+': receipt differs from its process record')
        if receipts[(stage, 'stage_started')]['command_file'] != f'stages/{stage}/command.json': problems.append(stage+': start receipt')
        clean = (process['exit_code'] == 0 and not process['resource_exhausted'] and not process['resource_violations'] and not process['monitor_error']
                 and not process['observation_error'] and process['workload_empty_after_cleanup'] is True)
        if stage != 'search' and not clean: problems.append(stage+': not clean')  # the search stage: `search:terminated_cleanly`
    a.require(not problems, f'{name}:commands:rebuilt_by_the_stage_function', '; '.join(problems))
    search = load(run/'stages/search/search.process.json')
    a.require(not search['resource_exhausted'] and search['resource_violations'] == [] and search['monitor_error'] is None and search['observation_error'] is None
              and search['workload_empty_after_cleanup'] is True and isinstance(search['exit_code'], int) and (search['exit_code'] == 0 or not proved),
              f'{name}:search:terminated_cleanly')  # revision 2 (finding 5): only the exit code may carry a refusal
    failed = search['exit_code'] != 0
    again = broker.classify(run, route, failed)
    a.require(again['outcome'] == outcome['outcome'] or (proved and again['outcome'] == SUCCESS[route]), f'{name}:search:outcome_recomputed', f"{again['outcome']} vs {outcome['outcome']}")
    a.require({k: v for k, v in again.items() if k not in ('outcome', 'certificate')} == {k: outcome.get(k) for k in again if k not in ('outcome', 'certificate')},
              f'{name}:search:fields_recomputed')
    observations_bound(a, name, run, route, again['outcome'], tools)
    downstream = ('evidence.json', 'certificate-verdict.json', 'solution.ndjson.gz', 'verdict.json', 'validation-input', 'validation-local.raw.json.gz', 'validation-whole.raw.json.gz')
    a.require(all((run/f).exists() == proved for f in downstream), f'{name}:search:downstream_exactly_when_proved')
    accepted = False
    if proved:
        data = {r['event']: r['payload']['data'] for r in broker.children(run)}
        context = run/'stages/search/output/context.json'
        a.require(load(context) == load(task.path/'context/local-context.json')
                  and receipts[('search', 'context_validated')] == {'captured_context_sha256': r6.sha(context), 'frozen_context_sha256': r6.sha(task.path/'context/local-context.json')},
                  f'{name}:proof:context_frozen')
        packet = load(run/'evidence.json')
        a.require(packet == {'certificate': data['dispatch_received']['certificate'], 'input_ir': data['dispatch_started']['ir'],
                             'final_ir': data['dispatch_received']['final_ir'], 'trace': data['dispatch_received']['trace']}, f'{name}:proof:evidence_rebuilt_from_observations')
        verdict = load(run/'verdict.json'); recomputed = verifier_verdict(tools, run/'evidence.json')
        a.require(recomputed is not None and recomputed.get('accepted') is True and recomputed == load(run/'certificate-verdict.json') == verdict['certificate_validation']
                  == receipts[('certificate-check', 'independent_certificate_verdict')], f'{name}:proof:certificate_check_reexecuted')
        if route == broker.ARM:
            selected = [r['payload']['data'] for r in broker.children(run) if r['event'] == 'closer_selected']
            a.require(data['reconstruction_finished'] == {'certificate': packet['certificate'], 'closer': verdict['closer'], 'certificate_consumed': True,
                                                           'derivation_replayed': False, 'residual_closer': 'omega'}
                      and len(selected) == 1 and selected[0]['certificate'] == packet['certificate'] and selected[0]['closer'] == verdict['closer'], f'{name}:proof:consumption_receipt')
        else:
            a.require(data['broker_closer_returned'] == {'closer': verdict['closer'], 'certificate': packet['certificate']}, f'{name}:proof:closer_receipt')
        try:
            with gzip.open(run/'solution.ndjson.gz', 'rb') as f: solution = f.read()
        except (OSError, EOFError, gzip.BadGzipFile): solution = None
        stdout = run/'stages/export/export.stdout'; export = load(run/'stages/export/export.process.json')
        present = stdout.is_file(); STDOUT_COMPARED.append(present)  # revision 3: ignored by version control; compared only when present
        a.require(solution is not None and sha(solution) == verdict['solution_sha256'] == seal['ephemeral_sha256'].get('stages/export/export.stdout')
                  and (not present or stdout.read_bytes() == solution) and len(solution) == export['output_bytes'] == receipts[('export', 'stage_finished')]['output_bytes']
                  and all(('"str":"'+n.split('.')[-1]+'"}').encode() in solution for n in (task.local, task.whole)), f'{name}:proof:solution_bound')  # revision 2 (finding 4)
        accepted = kernel(a, name, run, task, route, verdict, receipts, frozen)
        a.require(verdict == {'schema_version': 'r6-deterministic-verdict-1', 'task_id': site, 'route': route, 'closer': outcome['closer'],
                              'certificate_validation': verdict['certificate_validation'], 'final_validation': verdict['final_validation'], 'axiom_delta': verdict['axiom_delta'],
                              'solution_sha256': verdict['solution_sha256'], 'local_obligation_closed': True, 'whole_declaration_validated': True, 'model_calls': 0}
                  and outcome['axiom_delta_empty'] is accepted, f'{name}:proof:verdict_shape')
    terminal = receipts[('episode', 'episode_finished' if proved and accepted else 'episode_rejected')]
    a.require(outcome['resources'] == broker.resources(run) and outcome['verdict_sha256'] == (r6.sha(run/'verdict.json') if proved else None)
              and outcome['task_id'] == site and outcome['route'] == route and summary['results'][route][site] == outcome
              and terminal == {'outcome_sha256': r6.sha(run/'outcome.json'), 'outcome': outcome['outcome']} and seal['accepted'] is (proved and accepted),
              f'{name}:outcome:record_bound')
    return outcome['outcome']


def audit(root):
    a = Audit(); root = Path(root); STDOUT_COMPARED.clear()
    policy = broker.verify(); policy_sha = r6.sha(broker.POLICY)
    primary = list(site_task.primary())
    a.require(len(primary) == 15 and len(set(primary)) == 15 and policy['sites'] == primary, 'population:reviewed_fifteen_sites')
    try: summary = load(root/'deterministic.json')
    except (OSError, ValueError) as error: a.require(False, 'population:summary_bound', str(error))
    present = sorted(str(p.relative_to(root)) for p in root.iterdir())
    runs = sorted(f'{route}/{site}' for route in (broker.ARM, broker.REFERENCE) for site in primary)
    on_disk = sorted(f'{p.name}/{q.name}' for p in root.iterdir() if p.is_dir() for q in p.iterdir())
    a.require(present == sorted(['deterministic.json', broker.ARM, broker.REFERENCE]) and on_disk == runs, 'population:exactly_fifteen_sites_by_two_routes', str(on_disk)[:300])
    a.require(summary.get('sites') == primary and sorted(summary.get('results', {})) == sorted((broker.ARM, broker.REFERENCE))
              and all(sorted(summary['results'][r]) == sorted(primary) for r in (broker.ARM, broker.REFERENCE))
              and summary['policy_sha256'] == policy_sha and summary['lock_sha256'] == r6.sha(broker.LOCK) and summary['program_sha256'] == load(broker.LOCK)['site_broker.py']
              and summary['schema_version'] == 'r6-deterministic-summary-1', 'population:summary_bound')
    tools = broker.tools_for(ROOT.parents[1]/'lean-bridge/.lake/packages')
    a.require(r6.sha(tools['solver']) == policy['solver']['sha256'] and tools['patch'] == broker.source_record()[1], 'tools:equal_to_the_frozen_policy')
    binaries = [tools['compiler']/'bin/lean', tools['exporter'], tools['checker'], tools['verifier'], tools['solver'], *tools['extras']]
    reviewed = {'sources': broker.source_record(), 'binaries': {str(p): r6.sha(p) for p in binaries}, 'policy': policy}
    table = {}
    for route in (broker.ARM, broker.REFERENCE):
        for site in primary:
            table.setdefault(route, {}).setdefault(audit_run(a, root, route, site, tools, policy_sha, summary, reviewed), []).append(site)
    expected = expected_cases(primary, {(route, site): route_outcome for route, outcomes in table.items() for route_outcome, sites in outcomes.items() for site in sites})
    a.require(sorted(a.cases) == sorted(expected), 'audit:case_population_complete', str(sorted(set(a.cases) ^ set(expected)))[:300])
    return {'accepted': True, 'case_count': len(a.cases), 'runs': len(runs), 'outcomes': table, 'policy_sha256': policy_sha,
            'export_stdout_compared': {'proved_runs': len(STDOUT_COMPARED), 'stdout_present_and_compared': sum(STDOUT_COMPARED),
                                       'qualification': 'the export stdout is not retained by version control; where absent, the solution is bound by the sealed digest and size'}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runs', type=Path, default=broker.RUNS)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output and args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    try: result = audit(args.runs)
    except Rejection as rejection: result = {'accepted': False, 'rejected_case': rejection.case, 'detail': str(rejection)}
    result = {**result, 'auditor_sha256': r6.sha(Path(__file__)), 'model_calls': 0, 'credentials_read': 0,
              'scope': 'retained deterministic-arm evidence; the certificate check is re-executed, the kernel replays are derived from their raw reports; no episode is rerun'}
    if args.output: r6.write_json(args.output, result)
    print(json.dumps({k: result[k] for k in result if k != 'outcomes'}, indent=1))
    if not result['accepted']: raise SystemExit(1)


if __name__ == '__main__':
    main()
