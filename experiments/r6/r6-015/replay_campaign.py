#!/usr/bin/env python3
"""R6-015 replay campaign: the frozen plan, under the R6-015 lock (`R6-015-PROPOSAL.md`, revision 5, steps 4-5, and control 8).

    replay_campaign.py lock --plan PLAN.json        write the R6-015 lock, once (step 4; only after review)
    replay_campaign.py run --runs DIR               replay every planned episode, each sealed, into DIR/<id>
    replay_campaign.py control8 --runs DIR --output RECORD.json

The lock and admission are `replay_lock`'s. `run` refuses unless the lock verifies, admits each episode again at its boundary,
and verifies the lock afterwards.

Step 5's order, each under the lock: `run`; `control3.py` (the synthetic probe); `control8`; then `analysis.py`.

`control8` (harness revision 3) binds every run to the locked plan before it evaluates anything, for every planned episode, proof
or not:
1. the run's seal: every file present is sealed, retained or ephemeral, every retained file is present with its digest (ephemeral
   build products may be absent), and the event chain matches the seal's count and last hash;
2. the run's spec, its `episode_started` record and its verdict's identity fields equal the locked plan's entry; the start record
   names the verified lock's digest, its bridge revision and the locked harness digests, and the run's provenance (its harness
   copies and instrumented `Tactic.lean`) matches the lock;
2a. exactly one `episode_finished`, the last event, from the supervisor, names the verdict's outcome and digest, and the seal's
   acceptance agrees with the outcome;
3. its packet equals the one rebuilt from the locked consumed artifact and the spec's coefficients;
4. for a proof, the receipt is the one the spec requires (`replay_episode.receipt`).

Then, for each proof, the audit program runs in real mode on the run's export with its retained residual, and revision 5's frozen
predicate is evaluated: the program exits 0 without a refusal, `binding` is `matches_residual`, both targets are locatable, and
both carry an explicit, empty hypothesis list. An error, a refusal or a missing field fails. Afterwards every audited artifact is
rechecked against its seal, and the lock is verified again. Kernel validation is the episode's own (acceptance 3 and 4).

Offline: no provider, credential, reservation or spending.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
if str(R6) not in sys.path: sys.path.insert(0, str(R6))
if str(HERE) not in sys.path: sys.path.insert(0, str(HERE))

import events  # noqa: E402
import run as r6  # noqa: E402
import site_task  # noqa: E402
import replay_episode  # noqa: E402
import replay_lock  # noqa: E402

AUDITED = ('solution.ndjson.gz', 'residual.txt', 'verdict.json', 'spec.json', 'evidence.json', 'events.ndjson')


def lock(args):
    print(replay_lock.write_lock(args.plan))


def run_all(args):
    frozen = replay_lock.verify_lock()
    runs = Path(args.runs).resolve()
    results = {}
    for spec in replay_lock.planned(frozen).values():
        target = runs/spec['id']
        if target.exists(): raise SystemExit(f'refusing to overwrite {target}')
        target.mkdir(parents=True)
        results[spec['id']] = replay_episode.execute(target, spec)
        print(spec['id'], results[spec['id']]['outcome'], flush=True)
    replay_lock.verify_lock()
    r6.write_json(runs/'index.json', {'lock_sha256': r6.sha(replay_lock.LOCK), 'results': results})


def sealed(run):
    """Every file present is sealed; every retained digest matches; the event chain matches the seal."""
    seal = r6.read_json(run/'seal.json')
    present = {str(p.relative_to(run)) for p in run.rglob('*') if p.is_file() and p.name != 'seal.json'}
    if present - set(seal['retained_sha256']) - set(seal['ephemeral_sha256']): raise ValueError('a file present is not sealed')
    for name, digest in seal['retained_sha256'].items():
        if r6.sha(run/name) != digest: raise ValueError(f'{name} differs from the seal')
    rows = events.read(run/'events.ndjson')
    if len(rows) != seal['event_count'] or rows[-1]['event_hash'] != seal['last_event_hash']: raise ValueError('events differ from the seal')
    return seal, rows


def bound(run, spec, frozen, lock_sha):
    """The run is the planned episode, run by the locked programs under the verified lock, and finished; all checked before the
    outcome is used: seal, spec, start record and provenance, terminal event, seal acceptance, verdict identity, packet and, for a
    proof, the receipt."""
    seal, rows = sealed(run)
    if r6.read_json(run/'spec.json') != spec: raise ValueError('spec differs from the plan')
    first, last = rows[0], rows[-1]; started = first['payload']
    if (first['event'] != 'episode_started' or first['source'] != 'supervisor' or started.get('spec') != spec
            or started.get('admission') != 'planned' or started.get('excluded_from_results') is not False):
        raise ValueError('the episode did not start as this planned episode')
    # provenance: the verified lock, its bridge revision, its harness, as recorded at the start and in the run's provenance
    harness = {str(p.relative_to(R6)): frozen['python_sha256'][str(p.relative_to(R6))] for p in replay_episode.HARNESS}
    if (started.get('schema_version') != replay_episode.SCHEMA or started.get('lock_sha256') != lock_sha
            or started.get('bridge_rev') != frozen['bridge_rev'] or started.get('harness_sha256') != harness):
        raise ValueError('the episode was not run under this lock, bridge and harness')
    copies = {f'r6-015/{Path(name).name}': r6.sha(run/'provenance/r6-015'/Path(name).name) for name in harness}
    if copies != harness: raise ValueError("the run's harness copies differ from the lock")
    sources = r6.read_json(run/'provenance/sources.json')
    if sources['lean-bridge/ProofBroker/Tactic.lean']['instrumented_sha256'] != frozen['instrumented_tactic_sha256']:
        raise ValueError("the run's bridge differs from the lock")
    # the terminal event: exactly one, last, from the supervisor, naming this verdict
    verdict = r6.read_json(run/'verdict.json')
    if ([r['event'] for r in rows].count('episode_finished') != 1 or last['event'] != 'episode_finished' or last['source'] != 'supervisor'
            or last['payload'] != {'outcome': verdict['outcome'], 'verdict_sha256': r6.sha(run/'verdict.json')}):
        raise ValueError('the terminal event does not name this verdict')
    if seal['accepted'] is not (verdict['outcome'] == 'proved'): raise ValueError("the seal's acceptance disagrees with the verdict")
    identity = {'id': spec['id'], 'site': spec['site'], 'source': spec['source'], 'route': spec['route'], 'coefficients': spec['coefficients'],
                'mutated': spec['coefficients'] is not None, 'inject_unverified': spec['inject_unverified'], 'admission': 'planned',
                'excluded_from_results': False}
    if {k: verdict.get(k) for k in identity} != identity: raise ValueError('verdict identity differs from the plan')
    packet = replay_episode.mutated(replay_episode.retained_packet(spec), spec['coefficients'])
    if r6.read_json(run/'evidence.json') != packet: raise ValueError('packet differs from the locked source and the spec')
    if verdict['outcome'] == 'proved': replay_episode.receipt(run, packet, spec)
    return seal, verdict


def audit_real(run, solution, residual, task):
    env = {'PATH': '/usr/bin:/bin', 'LEAN_SYSROOT': str(replay_lock.AUDIT_TOOLCHAIN)}
    with tempfile.TemporaryDirectory(prefix='r6-015-control-8-') as tmp:
        tmp = Path(tmp); export = tmp/'export.ndjson'; r6.unpack(solution, export)
        (tmp/'residual.txt').write_text(residual + '\n')
        argv = [str(replay_lock.AUDIT_TOOL), str(export), task.local, task.whole, str(tmp/'residual.txt'), str(tmp/'report.json')]
        proc = subprocess.run(argv, capture_output=True, text=True, env=env)
        report = r6.read_json(tmp/'report.json') if (tmp/'report.json').exists() else {'error': (proc.stdout + proc.stderr)[-2000:]}
        inputs = {'<tmp>/export.ndjson': {'unpacked_from': f'{run.name}/solution.ndjson.gz', 'sha256': r6.sha(export)},
                  '<tmp>/residual.txt': {'copied_from': f'{run.name}/residual.txt', 'sha256': r6.sha(tmp/'residual.txt')}}
    report['exit'] = proc.returncode
    command = {'argv': [str(replay_lock.AUDIT_TOOL.relative_to(R6)), '<tmp>/export.ndjson', task.local, task.whole, '<tmp>/residual.txt',
                        '<tmp>/report.json'], 'env': env, 'exit_code': proc.returncode, 'inputs': inputs,
               'stdout': proc.stdout[-2000:], 'stderr': proc.stderr[-2000:], 'tool_sha256': r6.sha(replay_lock.AUDIT_TOOL)}
    return report, command


def predicate(r):
    """Revision 5's frozen predicate, real mode. Returns the unmet conditions; empty is a pass."""
    a = r.get('audit')
    if r.get('exit') != 0: return [f"exit {r.get('exit')}"]
    if 'refused' in r or not isinstance(a, dict): return ['refused or no report']
    unmet = [] if a.get('binding') == 'matches_residual' else [f"binding {a.get('binding')!r}"]
    for t in ('local', 'whole'):
        s = a.get(t)
        if not isinstance(s, dict): unmet.append(f'{t} missing'); continue
        if s.get('locatable') is not True: unmet.append(f'{t} not locatable')
        if not isinstance(s.get('hypotheses'), list): unmet.append(f'{t}.hypotheses missing')
        elif s['hypotheses']: unmet.append(f"{t} refers to {[h.get('name') for h in s['hypotheses']]}")
    return unmet


def control8(args):
    frozen = replay_lock.verify_lock()
    out = Path(args.output)
    if out.exists(): raise SystemExit(f'refusing to overwrite {out}')
    runs = Path(args.runs).resolve(); results = {}; audited = {}
    lock_sha = r6.sha(replay_lock.LOCK)
    for spec in replay_lock.planned(frozen).values():
        run = runs/spec['id']
        try:
            seal, verdict = bound(run, spec, frozen, lock_sha)  # before branching on the outcome
        except (OSError, ValueError, KeyError, replay_episode.Outcome) as unbound:
            results[spec['id']] = {'bound': False, 'reason': f'{type(unbound).__name__}: {unbound}'[:500]}
            print(spec['id'], 'unbound', results[spec['id']]['reason'], flush=True); continue
        if verdict['outcome'] != 'proved':
            results[spec['id']] = {'bound': True, 'outcome': verdict['outcome'], 'audited': False}; continue
        report, command = audit_real(run, run/'solution.ndjson.gz', (run/'residual.txt').read_text().rstrip('\n'), site_task.get(spec['site']))
        results[spec['id']] = {'bound': True, 'outcome': 'proved', 'audited': True, 'unmet': predicate(report), 'command': command,
                               'report': report}
        audited[spec['id']] = {name: seal['retained_sha256'][name] for name in AUDITED}
        print(spec['id'], 'pass' if not results[spec['id']]['unmet'] else results[spec['id']]['unmet'], flush=True)
    for run_id, digests in audited.items():  # afterwards: every audited artifact is still the sealed one
        if any(r6.sha(runs/run_id/name) != digest for name, digest in digests.items()): raise SystemExit(f'{run_id} changed during control 8')
    replay_lock.verify_lock()
    passed = all(r['bound'] and not r.get('unmet') for r in results.values())
    out.write_text(json.dumps({'passed': passed, 'lock_sha256': r6.sha(replay_lock.LOCK),
                               'audit_tool_sha256': r6.sha(replay_lock.AUDIT_TOOL), 'results': results}, indent=1) + '\n')
    print(json.dumps({'passed': passed}))


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='cmd', required=True)
    sub.add_parser('lock').add_argument('--plan', type=Path, required=True)
    sub.add_parser('run').add_argument('--runs', required=True)
    c = sub.add_parser('control8'); c.add_argument('--runs', required=True); c.add_argument('--output', required=True)
    args = p.parse_args()
    try:
        {'lock': lock, 'run': run_all, 'control8': control8}[args.cmd](args)
    except replay_lock.Refused as refused:
        raise SystemExit(str(refused))


if __name__ == '__main__':
    main()
