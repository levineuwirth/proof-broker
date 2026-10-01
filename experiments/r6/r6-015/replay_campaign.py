#!/usr/bin/env python3
"""R6-015 replay campaign: the frozen plan, under the R6-015 lock (`R6-015-PROPOSAL.md`, revision 5, steps 4-5, and control 8).

    replay_campaign.py lock --plan PLAN.json        write the R6-015 lock, once (step 4; only after review)
    replay_campaign.py run --runs DIR               replay every planned episode, each sealed, into DIR/<id>
    replay_campaign.py control8 --runs DIR --output RECORD.json

`run` refuses unless the lock verifies, and verifies it again afterwards. The lock binds:
- this harness (`replay_bridge.py`, `replay_episode.py`, this file) and R6's harness locks it builds on (`site-harness-v4`,
  `fixture-harness-v1`, the census lock), by digest;
- the bridge revision and the instrumented `Tactic.lean` (`replay_bridge.source_record`);
- the plan, by digest, and, for every planned episode, its source run's `seal.json` and the consumed artifact (`evidence.json` for a
  learned run, `events.ndjson` for a deterministic one), by digest;
- the audit program and the exporter, whose digests must also equal `qualification-audit-v1`'s.

`control8` evaluates revision 5's frozen predicate on every episode that produced a proof: the audit program in real mode on the
run's export, with the run's retained residual (printed from that export). It passes only if the program exits 0 without a
refusal, `binding` is `matches_residual`, both targets are locatable, and both carry an explicit, empty hypothesis list. An error,
a refusal or a missing field fails. Kernel validation is the episode's own (acceptance 3 and 4).

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

import census  # noqa: E402
import run as r6  # noqa: E402
import site_task  # noqa: E402
import replay_bridge  # noqa: E402
import replay_episode  # noqa: E402

LOCK = R6/'policies/r6-015-replay-v1.sha256.json'
EXPORTER = R6/'.cache/exporter/.lake/build/bin/lean4export'
SOURCES = (HERE/'replay_bridge.py', HERE/'replay_episode.py', Path(__file__).resolve())
R6_LOCKS = (site_task.LOCK, R6/'policies/fixture-harness-v1.sha256.json', replay_episode.AUDIT_LOCK)


def consumed(spec):
    run = R6/spec['source']['run']
    name = 'evidence.json' if spec['source']['arm'] == 'learned' else 'events.ndjson'
    return {'seal_sha256': r6.sha(run/'seal.json'), 'artifact': name, 'artifact_sha256': r6.sha(run/name)}


def lock_record(plan_path):
    plan = r6.read_json(plan_path)
    audit = r6.read_json(replay_episode.AUDIT_LOCK)
    if r6.sha(replay_episode.AUDIT_TOOL) != audit['tool_sha256'] or r6.sha(EXPORTER) != audit['exporter_sha256']:
        raise ValueError('the audit program or the exporter differs from qualification-audit-v1')
    sources, patch = replay_bridge.source_record()
    for spec in plan['episodes']: replay_episode.check_spec(spec)
    ids = [s['id'] for s in plan['episodes']]
    if len(set(ids)) != len(ids): raise ValueError('episode ids are not unique')
    if any(s['route'] != 'constrained' for s in plan['episodes']): raise ValueError('the plan runs the constrained route only')
    return {'schema_version': 'r6-015-replay-lock-1',
            'harness_sha256': {str(p.relative_to(R6)): r6.sha(p) for p in SOURCES},
            'r6_locks_sha256': {str(p.relative_to(R6)): r6.sha(p) for p in R6_LOCKS},
            'bridge_rev': replay_bridge.BRIDGE_REV,
            'instrumented_tactic_sha256': sources['lean-bridge/ProofBroker/Tactic.lean']['instrumented_sha256'],
            'instrumentation_patch_sha256': r6.hashlib.sha256(patch.encode()).hexdigest(),
            'plan': str(Path(plan_path).resolve().relative_to(R6)), 'plan_sha256': r6.sha(plan_path),
            'consumed': {s['id']: consumed(s) for s in plan['episodes']},
            'audit_tool_sha256': r6.sha(replay_episode.AUDIT_TOOL), 'exporter_sha256': r6.sha(EXPORTER)}


def verify_lock():
    if not LOCK.exists(): raise SystemExit('the R6-015 lock does not exist; nothing is replayed before the lock')
    frozen = r6.read_json(LOCK)
    site_task.verify_lock(); census.verify_lock()
    if lock_record(R6/frozen['plan']) != frozen: raise SystemExit('the R6-015 lock does not verify')
    return frozen


def lock(args):
    if LOCK.exists(): raise SystemExit('the R6-015 lock already exists')
    record = lock_record(args.plan)
    LOCK.write_text(json.dumps(record, indent=1) + '\n')
    print(r6.sha(LOCK))


def run_all(args):
    frozen = verify_lock()
    runs = Path(args.runs).resolve()
    plan = r6.read_json(R6/frozen['plan'])
    results = {}
    for spec in plan['episodes']:
        target = runs/spec['id']
        if target.exists(): raise SystemExit(f'refusing to overwrite {target}')
        target.mkdir(parents=True)
        results[spec['id']] = replay_episode.execute(target, spec)
        print(spec['id'], results[spec['id']]['outcome'], flush=True)
    verify_lock()
    r6.write_json(runs/'index.json', {'lock_sha256': r6.sha(LOCK), 'results': results})


def audit_real(solution, residual, task):
    with tempfile.TemporaryDirectory(prefix='r6-015-control-8-') as tmp:
        tmp = Path(tmp); export = tmp/'export.ndjson'; r6.unpack(solution, export)
        (tmp/'residual.txt').write_text(residual + '\n')
        proc = subprocess.run([str(replay_episode.AUDIT_TOOL), str(export), task.local, task.whole, str(tmp/'residual.txt'),
                               str(tmp/'report.json')], capture_output=True, text=True,
                              env={'PATH': '/usr/bin:/bin', 'LEAN_SYSROOT': str(replay_episode.AUDIT_TOOLCHAIN)})
        report = r6.read_json(tmp/'report.json') if (tmp/'report.json').exists() else {'error': (proc.stdout + proc.stderr)[-2000:]}
    report['exit'] = proc.returncode
    return report


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
    frozen = verify_lock()
    out = Path(args.output)
    if out.exists(): raise SystemExit(f'refusing to overwrite {out}')
    runs = Path(args.runs).resolve(); results = {}
    for spec in r6.read_json(R6/frozen['plan'])['episodes']:
        run = runs/spec['id']; verdict = r6.read_json(run/'verdict.json')
        if verdict['outcome'] != 'proved': continue
        seal = r6.read_json(run/'seal.json')
        for name in ('solution.ndjson.gz', 'residual.txt', 'verdict.json'):
            if seal['retained_sha256'].get(name) != r6.sha(run/name): raise SystemExit(f'{spec["id"]}/{name} differs from its seal')
        report = audit_real(run/'solution.ndjson.gz', (run/'residual.txt').read_text().rstrip('\n'), site_task.get(spec['site']))
        results[spec['id']] = {'unmet': predicate(report), 'report': report}
        print(spec['id'], 'pass' if not results[spec['id']]['unmet'] else results[spec['id']]['unmet'], flush=True)
    verify_lock()
    out.write_text(json.dumps({'lock_sha256': r6.sha(LOCK), 'audit_tool_sha256': r6.sha(replay_episode.AUDIT_TOOL),
                               'results': results}, indent=1) + '\n')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='cmd', required=True)
    sub.add_parser('lock').add_argument('--plan', type=Path, required=True)
    sub.add_parser('run').add_argument('--runs', required=True)
    c = sub.add_parser('control8'); c.add_argument('--runs', required=True); c.add_argument('--output', required=True)
    args = p.parse_args()
    {'lock': lock, 'run': run_all, 'control8': control8}[args.cmd](args)


if __name__ == '__main__':
    main()
