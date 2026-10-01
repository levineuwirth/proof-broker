#!/usr/bin/env python3
"""R6-015 harness rehearsal on the site path, pinned route (the limited pre-lock exception approved in the review of harness
revision 1): l069 draw 1 (learned) and l069's deterministic run, bridge `476fab31`, the option unset, injection disabled.

    rehearse_pinned.py --runs DIR --output RECORD.json

Each rehearsal is a sealed episode admitted as `rehearsal` (`replay_lock.REHEARSALS`), marked excluded from R6-015's results. They
test the harness. Expected, from R6-014's recorded results: each closes through R6's pinned ℕ closer (`term_mode_nat`, residual
closer `omega`), and the kernel replays pass. Afterwards, for each run:
- the seal check control 8 uses (`replay_campaign.sealed`) and the receipt the spec requires;
- the audit program in real mode with the run's residual (printed from its export), and control 8's predicate, as a test of that
  path only;
- whether the export equals R6's retained `solution.ndjson.gz` for the same source, byte for byte.

Finally, the R6 modules this process loaded are compared with `replay_lock.python_closure()` computed in a fresh process: a module
loaded only lazily would be outside the lock's closure.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
if str(R6) not in sys.path: sys.path.insert(0, str(R6))
if str(HERE) not in sys.path: sys.path.insert(0, str(HERE))

import run as r6  # noqa: E402
import site_task  # noqa: E402
import replay_campaign  # noqa: E402
import replay_episode  # noqa: E402
import replay_lock  # noqa: E402


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--runs', required=True); p.add_argument('--output', required=True)
    args = p.parse_args()
    runs, out = Path(args.runs).resolve(), Path(args.output)
    if out.exists(): raise SystemExit(f'refusing to overwrite {out}')
    results, failures = {}, {}
    for spec in replay_lock.REHEARSALS.values():
        run = runs/spec['id']
        if run.exists(): raise SystemExit(f'refusing to overwrite {run}')
        run.mkdir(parents=True)
        verdict = replay_episode.execute(run, spec)
        r = {'verdict': verdict}; unmet = []
        if verdict.get('outcome') != 'proved' or verdict.get('closer') != 'term_mode_nat' or verdict.get('residual_closer') != 'omega':
            unmet.append('did not reproduce R6-014 (proved, term_mode_nat, omega)')
        try:
            replay_campaign.sealed(run)
            packet = replay_episode.mutated(replay_episode.retained_packet(spec), spec['coefficients'])
            if r6.read_json(run/'evidence.json') != packet: unmet.append('packet differs')
            if verdict.get('outcome') == 'proved':
                replay_episode.receipt(run, packet, spec)
                report, command = replay_campaign.audit_real(run, run/'solution.ndjson.gz', (run/'residual.txt').read_text().rstrip('\n'),
                                                             site_task.get(spec['site']))
                r.update(control_8_unmet=replay_campaign.predicate(report), control_8_command=command,
                         binding=report.get('audit', {}).get('binding'),
                         classification={t: report.get('audit', {}).get(t, {}).get('classification') for t in ('local', 'whole')})
                if r['binding'] != 'matches_residual': unmet.append('residual binding')
                source = R6/spec['source']['run']/'solution.ndjson.gz'
                r['export_equals_r6'] = source.exists() and r6.sha(source) == r6.sha(run/'solution.ndjson.gz')
                r['r6_solution_retained'] = source.exists()
        except (OSError, ValueError, KeyError, replay_episode.Outcome) as caught:
            unmet.append(f'{type(caught).__name__}: {caught}'[:300])
        r['unmet'] = unmet; results[spec['id']] = r; failures[spec['id']] = unmet
        print(spec['id'], 'as expected' if not unmet else unmet, flush=True)
    loaded = sorted(str(Path(m.__file__).resolve().relative_to(R6)) for m in list(sys.modules.values())
                    if getattr(m, '__file__', None) and Path(m.__file__).resolve().is_relative_to(R6) and m.__file__.endswith('.py'))
    fresh = json.loads(subprocess.run([sys.executable, '-c', 'import json, sys; sys.path[:0] = [sys.argv[1], sys.argv[2]]; import replay_lock; '
                                       'print(json.dumps([str(p.relative_to(replay_lock.R6)) for p in replay_lock.python_closure()]))',
                                       str(R6), str(HERE)], capture_output=True, text=True, check=True).stdout.splitlines()[-1])
    outside = sorted(set(loaded) - set(fresh) - {'r6-015/rehearse_pinned.py'})
    if outside: failures['closure'] = [f'loaded outside the lock closure: {outside}']
    passed = not any(failures.values())
    out.write_text(json.dumps({'passed': passed, 'failures': failures, 'results': results, 'closure_loaded_outside': outside,
        'bridge_rev': replay_episode.replay_bridge.BRIDGE_REV, 'admission': 'rehearsal', 'excluded_from_results': True,
        'sources_sha256': {str(f.relative_to(R6)): r6.sha(f) for f in
                           (HERE/'replay_lock.py', HERE/'replay_bridge.py', HERE/'replay_episode.py', HERE/'replay_campaign.py',
                            Path(__file__).resolve())},
        'scope': 'pre-lock harness rehearsal, pinned route; approved exception; excluded from R6-015 results'}, indent=1) + '\n')
    print(json.dumps({'passed': passed}))
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(main())
