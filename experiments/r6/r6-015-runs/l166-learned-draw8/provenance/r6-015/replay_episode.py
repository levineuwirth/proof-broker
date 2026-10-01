#!/usr/bin/env python3
"""R6-015 replay episode: one certificate, offline, through the constrained route, sealed (`R6-015-PROPOSAL.md`, revision 5).

    replay_episode.py --spec SPEC.json --run-dir DIR

A spec names one site, one retained source and, for a mutation, the coefficient list that replaces the retained one:

    {"id": ..., "site": "bracket-l166",
     "source": {"arm": "learned", "run": "cohort-live-v9/l166-draw2"}
             | {"arm": "deterministic", "run": "census-runs/deterministic-v1/site_cvc4_term_mode_v1/bracket-l166"},
     "coefficients": null | [{"hypothesis": ..., "coefficient": ...}, ...],
     "inject_unverified": false, "route": "constrained"}

The episode, every stage under R6's site stage and its frozen checks:
1. **Setup** (`replay_bridge.setup`): the approved bridge revision with R6's overlays and R6-015's observations.
2. **Packet.** The retained one, checked against its run's seal: a learned run's `evidence.json`; for a deterministic run, the
   packet rebuilt from its sealed, hash-chained events (`dispatch_started.ir`; `dispatch_received.final_ir`, `.trace`,
   `.certificate`). A mutation replaces only `certificate.payload.witness_data.coefficients`; the envelope binds the final IR
   and the trace, not the multipliers.
3. **The independent check** (R6's `verify_certificate`). A rejected certificate ends the episode, unless the spec is a
   deliberate injection (`inject_unverified`, controls 1(b) and 4), which proceeds with the bridge's own gate bypassed.
4. **Reconstruction**: R6's capture helper for the site, with `proofBroker.term.constrained` set around the one tactic call
   (the frozen option setting). The packet is delivered as in R6 (`R6_PROPOSAL_PACKET`).
5. **The receipt**: exactly `term_route` (the option as the closers saw it, which must match the route), one `closer_selected`
   and one `reconstruction_finished` naming this certificate, the same closer and the constrained final step, in that order,
   after R6's reconstruction prefix.
6. **Export, and the local and whole kernel replays** (R6's `final_validation`, with the axiom delta).
7. **The residual, printed from the exported term**: the audit program of `qualification-audit-v1` reads the export in
   `--synthetic` mode and prints `hpos`'s type; that line is retained as the run's residual, for control 8's binding.
8. **Verdict, terminal event, seal** on every path. Failures are recorded with their stage and the closer's error lines; the
   analysis classifies them.

**Admission** (`replay_lock.admit`) comes before anything else is run or written: a planned episode must be exactly its entry in the
locked plan, under a verifying lock; a pinned episode must be exactly one of the two approved pre-lock rehearsals. `route:
"pinned"` leaves the option unset (R6's pinned closers) and requires R6's receipt; its records are marked as rehearsals, excluded
from R6-015's results.

Offline: no provider, credential, reservation or spending.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
if str(R6) not in sys.path: sys.path.insert(0, str(R6))
if str(HERE) not in sys.path: sys.path.insert(0, str(HERE))

import episode  # noqa: E402
import events  # noqa: E402
import run as r6  # noqa: E402
import site_network  # noqa: E402
import site_stage  # noqa: E402
import site_task  # noqa: E402
import replay_bridge  # noqa: E402
import replay_lock  # noqa: E402

SCHEMA = 'r6-015-replay-2'
AUDIT_TOOL, AUDIT_TOOLCHAIN, AUDIT_LOCK = replay_lock.AUDIT_TOOL, replay_lock.AUDIT_TOOLCHAIN, replay_lock.AUDIT_LOCK
check_spec = replay_lock.check_spec
PACKAGES = R6.parents[1]/'lean-bridge/.lake/packages'
PREFIX = ['reification_started', 'reification_finished', 'dispatch_started', 'dispatch_received', 'certificate_verification_started',
          'certificate_verification_finished', 'reconstruction_started']
HARNESS = (HERE/'replay_lock.py', HERE/'replay_bridge.py', Path(__file__).resolve())


class Outcome(Exception):
    """An episode outcome other than a validated proof, with its stage and evidence."""
    def __init__(self, category, stage, detail):
        super().__init__(f'{category} at {stage}: {detail}')
        self.category, self.stage, self.detail = category, stage, detail


def sealed(source_run, name):
    """A retained file, checked against its run's seal."""
    seal = r6.read_json(source_run/'seal.json')
    if seal['retained_sha256'].get(name) != r6.sha(source_run/name): raise ValueError(f'{source_run.name}/{name} differs from its seal')
    return source_run/name


def retained_packet(spec):
    source = R6/spec['source']['run']
    if spec['source']['arm'] == 'learned':
        packet = r6.read_json(sealed(source, 'evidence.json'))
    else:
        rows = events.read(sealed(source, 'events.ndjson'))
        child = [(r['event'], r['payload']['data']) for r in rows if r['source'] == 'child_report' and r['stage'] == 'search']
        started = [d for e, d in child if e == 'dispatch_started']; received = [d for e, d in child if e == 'dispatch_received']
        if len(started) != 1 or len(received) != 1 or received[0].get('certificate') is None:
            raise ValueError('the deterministic run has no single dispatch with a certificate')
        packet = {'input_ir': started[0]['ir'], 'final_ir': received[0]['final_ir'], 'trace': received[0]['trace'],
                  'certificate': received[0]['certificate']}
    if set(packet) != {'input_ir', 'final_ir', 'trace', 'certificate'}: raise ValueError('packet fields')
    return packet


def mutated(packet, coefficients):
    if coefficients is None: return packet
    packet = json.loads(json.dumps(packet))
    data = packet['certificate']['payload']['witness_data']
    if set(data) != {'coefficients'}: raise ValueError('witness data has fields beyond the coefficients')
    data['coefficients'] = coefficients
    return packet


def observed(run):
    return [(r['event'], r['payload']['data']) for r in events.read(run/'events.ndjson') if r['source'] == 'child_report' and r['stage'] == 'reconstruct']


def expected_events(spec):
    """The reconstruct stage's events for a proof, derived from the spec: the bypass only under injection, R6's residual events
    only on the pinned route (the pinned fold's `omega`)."""
    return (PREFIX + (['certificate_gate_bypassed'] if spec['inject_unverified'] else []) + ['term_route', 'closer_selected']
            + (['residual_started', 'residual_finished'] if spec['route'] == 'pinned' else []) + ['reconstruction_finished'])


def receipt(run, packet, spec):
    """The closer's own receipt, from the reconstruct stage's events only, against the events the spec requires."""
    route = spec['route']
    rows = observed(run); names = [e for e, _ in rows]; found = dict(rows)
    if names != expected_events(spec): raise Outcome('consumption_unobserved', 'reconstruct', {'events': names})
    if spec['inject_unverified']:
        bypass = found['certificate_gate_bypassed']
        if bypass.get('certificate') != packet['certificate'] or 'verify_ok' not in bypass:
            raise Outcome('consumption_unobserved', 'reconstruct', 'the bypass does not name this certificate')
    if found['term_route'] != {'constrained': route == 'constrained'}: raise Outcome('route_mismatch', 'reconstruct', found['term_route'])
    selected, finished = found['closer_selected'], found['reconstruction_finished']
    if not (selected['certificate'] == finished['certificate'] == packet['certificate'] and selected['closer'] == finished['closer']
            and finished['certificate_consumed'] is True):
        raise Outcome('consumption_unobserved', 'reconstruct', 'the receipt does not name this certificate and closer')
    if route == 'constrained':
        if not (selected.get('route') == 'constrained' and finished.get('final_step') == 'constrained'
                and finished.get('residual_closer') == 'constrained_normalization' and finished.get('constrained_option') is True):
            raise Outcome('consumption_unobserved', 'reconstruct', 'the receipt does not name the constrained final step')
    elif not (finished.get('residual_closer') == 'omega' and found['residual_finished'] == {'closer': 'omega'}):
        raise Outcome('consumption_unobserved', 'reconstruct', 'the pinned receipt does not name the pinned final step')
    return finished


def stage_log(run, name):
    record = run/'stages'/name
    log = ''.join((record/f'{name}.{s}').read_text() for s in ('stdout', 'stderr') if (record/f'{name}.{s}').exists())
    return [line for line in log.splitlines() if ': error: ' in line or 'error:' in line][:20]


def residual_from_export(run, solution, task):
    """`hpos`'s type, printed by the frozen audit program from the exported term (`--synthetic`: no residual is consulted)."""
    lock = r6.read_json(AUDIT_LOCK)
    if r6.sha(AUDIT_TOOL) != lock['tool_sha256']: raise ValueError('the audit program differs from qualification-audit-v1')
    out = run/'residual'; out.mkdir()
    env = {'PATH': '/usr/bin:/bin', 'LEAN_SYSROOT': str(AUDIT_TOOLCHAIN)}
    with tempfile.TemporaryDirectory(prefix='r6-015-residual-') as tmp:
        export = Path(tmp)/'export.ndjson'; r6.unpack(solution, export)
        argv = [str(AUDIT_TOOL), '--synthetic', str(export), task.local, task.whole, '-', str(out/'report.json')]
        proc = subprocess.run(argv, capture_output=True, text=True, env=env)
        unpacked = r6.sha(export)
    (out/'stdout').write_text(proc.stdout); (out/'stderr').write_text(proc.stderr)
    normalized = [str(AUDIT_TOOL.relative_to(R6)), '--synthetic', '<tmp>/export.ndjson', task.local, task.whole, '-',
                  str((out/'report.json').relative_to(run))]
    r6.write_json(out/'command.json', {'argv': normalized, 'env': env, 'exit_code': proc.returncode,
        'inputs': {'<tmp>/export.ndjson': {'unpacked_from': 'solution.ndjson.gz', 'sha256': unpacked}},
        'tool_sha256': r6.sha(AUDIT_TOOL), 'audit_lock_sha256': r6.sha(AUDIT_LOCK)})
    report = r6.read_json(out/'report.json') if (out/'report.json').exists() else {}
    goal = report.get('audit', {}).get('local', {}).get('residual_goal')
    if proc.returncode != 0 or not isinstance(goal, str): raise Outcome('residual_unprinted', 'residual', {'exit': proc.returncode})
    (run/'residual.txt').write_text(goal + '\n')
    return goal


def execute(run, spec):
    admission = replay_lock.admit(spec)
    if any(run.iterdir()): raise replay_lock.Refused('the run directory is not empty')
    task = site_task.get(spec['site'])
    events.append(run, 'episode', 'episode_started', {'schema_version': SCHEMA, 'spec': spec, 'admission': admission,
        'excluded_from_results': admission == 'rehearsal', 'lock_sha256': r6.sha(replay_lock.LOCK) if admission == 'planned' else None,
        'harness_sha256': {str(p.relative_to(R6)): r6.sha(p) for p in HARNESS}, 'bridge_rev': replay_bridge.BRIDGE_REV}, task_id=task.id)
    r6.write_json(run/'spec.json', spec)
    result = {'schema_version': SCHEMA, 'id': spec['id'], 'site': task.id, 'source': spec['source'], 'route': spec['route'],
              'coefficients': spec['coefficients'], 'mutated': spec['coefficients'] is not None,
              'inject_unverified': spec['inject_unverified'], 'admission': admission, 'excluded_from_results': admission == 'rehearsal'}
    try:
        tools = replay_bridge.setup(run, site_task, task, PACKAGES)
        for p in HARNESS:
            target = run/'provenance/r6-015'/p.name; target.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(p, target)
        retained = retained_packet(spec); packet = mutated(retained, spec['coefficients'])
        r6.write_json(run/'evidence.json', packet)
        events.append(run, 'packet', 'packet_loaded', {'source': spec['source'], 'certificate_sha256': events.digest(packet['certificate']),
            'retained_certificate_sha256': events.digest(retained['certificate']), 'mutated': spec['coefficients'] is not None})
        try:
            verified = site_stage.stage(run, 'certificate-check', tools['verifier'], ['/evidence.json', '/out/verdict.json'],
                                        [(run/'evidence.json', '/evidence.json')])
        except episode.StageFailure as error:
            if error.category != 'stage_rejected': raise
            verified = run/'stages/certificate-check/output'
        verdict = r6.read_json(verified/'verdict.json')
        r6.write_json(run/'certificate-verdict.json', verdict)
        events.append(run, 'certificate-check', 'independent_certificate_verdict', verdict)
        result['certificate_accepted'] = verdict['accepted'] is True
        if verdict['accepted'] is not True and not spec['inject_unverified']:
            raise Outcome('certificate_rejected', 'certificate-check', verdict.get('reason'))
        inputs = site_task.compile_input(run, 'input', 'ProposalCapture', replay_bridge.capture_source(site_task, task, spec['route']), task)
        compiler = tools['compiler']; mounts = [*tools['mounts'], (inputs, '/input')]
        built = site_stage.stage(run, 'capture-build', compiler/'bin/lean',
            [*tools['loads'], '-R', '/input', '-o', '/out/ProposalCapture.olean', '/input/ProposalCapture.lean'],
            mounts, compiler=compiler, env={'LEAN_PATH': tools['lean_path']+':/out'}, extra_binaries=tools['extras'])
        env = {'LEAN_PATH': tools['lean_path']+':/capture', 'R6_PROPOSAL_PACKET': '/evidence.json',
               'PROOF_BROKER_EPISODE_TRACE': '1', 'R6_CAPTURE_OUTPUT': '/out/context.json'}
        if spec['inject_unverified']: env['R6_015_INJECT_UNVERIFIED'] = '1'
        try:
            reconstructed = site_stage.stage(run, 'reconstruct', compiler/'bin/lean',
                [*tools['loads'], '-R', '/input', '-o', '/out/Frozen.olean', '/input/Frozen.lean'],
                [*mounts, (built, '/capture'), (run/'evidence.json', '/evidence.json')], compiler=compiler,
                extra_binaries=tools['extras'], capture_events=True, env=env)
        except episode.StageFailure as error:
            if error.category != 'stage_rejected': raise
            raise Outcome('reconstruction_failed', 'reconstruct', {'events': [e for e, _ in observed(run)], 'errors': stage_log(run, 'reconstruct')})
        found = receipt(run, packet, spec)
        result.update(closer=found['closer'], final_step=found.get('final_step'), residual_closer=found['residual_closer'])
        if r6.read_json(reconstructed/'context.json') != r6.read_json(task.path/'context/local-context.json'):
            raise Outcome('context_changed', 'reconstruct', 'reconstruction changed the frozen context')
        exported = site_stage.stage(run, 'export', tools['exporter'], ['Frozen', '--', task.whole, task.local, *r6.EXPORT_TARGETS],
            [*tools['mounts'], (reconstructed, '/objects'), (built, '/capture')], compiler=compiler,
            extra_binaries=tools['extras'], env={'LEAN_PATH': tools['lean_path']+':/capture:/objects'})
        r6.pack(exported.parent/'export.stdout', run/'solution.ndjson.gz')
        with tempfile.TemporaryDirectory(prefix='r6-015-challenge-') as temp:
            challenge = Path(temp)/'challenge.ndjson'; r6.unpack(task.path/'challenge.ndjson.gz', challenge)
            if r6.sha(challenge) != tools['expected']['challenge_sha256']: raise ValueError('challenge changed')
            try:
                reports, delta = site_network.final_validation(run, challenge, exported.parent/'export.stdout', tools['checker'],
                                                               tools['expected'], task)
            except (episode.StageFailure, ValueError) as error:
                raise Outcome('kernel_rejected', 'validation', str(error)[:500])
        result.update(local_validated=True, whole_validated=True, axiom_delta=delta, solution_sha256=r6.sha(run/'solution.ndjson.gz'))
        result['residual_goal'] = residual_from_export(run, run/'solution.ndjson.gz', task)
        result['outcome'] = 'proved'
        events.append(run, 'episode', 'proof_validated', {'solution_sha256': result['solution_sha256'], 'closer': result['closer']})
    except Outcome as caught:
        result.update(outcome=caught.category, failure_stage=caught.stage, detail=caught.detail)
        events.append(run, caught.stage, 'outcome_recorded', {'category': caught.category, 'detail': caught.detail})
    except episode.StageFailure as caught:
        result.update(outcome='stage_failure', failure_stage=caught.stage, detail=f'{caught.category}: {caught}'[:500])
        events.append(run, caught.stage, 'stage_failure_recorded', {'category': caught.category})
    except Exception as caught:  # the episode is a sealed record on every path
        result.update(outcome='harness_failure', failure_stage='harness', detail=f'{type(caught).__name__}: {caught}'[:500])
        events.append(run, 'episode', 'harness_failure_recorded', {'error': type(caught).__name__})
    r6.write_json(run/'verdict.json', result)
    events.append(run, 'episode', 'episode_finished', {'outcome': result['outcome'], 'verdict_sha256': r6.sha(run/'verdict.json')})
    site_network.seal(run, result['outcome'] == 'proved')
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--spec', type=Path, required=True)
    p.add_argument('--run-dir', type=Path, required=True)
    args = p.parse_args()
    spec = json.loads(args.spec.read_text())
    replay_lock.admit(spec)  # before the run directory exists
    run = args.run_dir.resolve(); run.mkdir(parents=True, exist_ok=False)
    print(json.dumps(execute(run, spec), indent=1, default=str))


if __name__ == '__main__':
    main()
