#!/usr/bin/env python3
"""R6-016 harness rehearsal on synthetic goals: R6-015's (`r6-015/rehearse_synthetic.py`), on R6-016's bridge revision, with
`qualification-audit-v2`'s program. No site, no retained certificate (pre-lock). The cases and expectations are R6-015's.

    rehearse_synthetic.py --output RECORD.json

Builds the replay bridge (`replay_bridge.build`) and drives R6's own helpers on synthetic goals, with `lean` run directly rather
than under the site stage:
- preparation: R6's preparation helper (`site_task.capture_source(…, True)` over `capture/CaptureSite.lean`) reifies the goal as
  reconstruction will; R6's driver prepares the problem and assembles each packet from a witness written here;
- reconstruction: R6's reconstruction helper with the frozen option setting (`replay_bridge.capture_source`), the packet
  delivered as in R6 (`R6_PROPOSAL_PACKET`), the events read from the child's `R6_EVENT` lines;
- for a proof: the export (R6's pinned exporter), the residual printed from it by the audit program of `qualification-audit-v2`
  (`--synthetic`), and that program again in real mode with the residual, evaluated by control 8's frozen predicate.

Cases, each with its frozen expectation:
- `valid`: the mixed-carrier goal (`hn` 1, `hz` 1, `neg_goal` 1), constrained: closes, with the constrained receipt; control 8
  passes;
- `invalid_checked`: `neg_goal` doubled, constrained: the bridge's own gate refuses it; no closer runs;
- `invalid_injected`: the same with `R6_015_INJECT_UNVERIFIED=1`: the gate is bypassed and recorded; the constrained closer is
  selected and fails, the sum not cancelling;
- `valid_pinned`: the valid witness on the pinned route: `term_route` records the option unset, and R6's ℕ closer refuses the
  `Int` goal, as it refused the four sites.

Offline: no provider, credential, episode or spending.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
if str(R6) not in sys.path: sys.path.insert(0, str(R6))
if str(HERE) not in sys.path: sys.path.insert(0, str(HERE))

import run as r6  # noqa: E402
import site_freeze  # noqa: E402
import site_task  # noqa: E402
import replay_bridge  # noqa: E402
import replay_episode  # noqa: E402

WORK = R6/'.cache/r6-016-rehearsal'
EXPORTER = R6/'.cache/exporter/.lake/build/bin/lean4export'
GOAL = 'theorem c1_whole (n m : Nat) (z : Int) (hn : n ≤ m) (hz : z + ↑m ≤ 5) : z + ↑n ≤ 5 := by\n  {tactic} "c1_whole.r6_site_c1" "synthetic-c1"\n'
VALID = [{'hypothesis': 'hn', 'coefficient': '1'}, {'hypothesis': 'hz', 'coefficient': '1'}, {'hypothesis': 'neg_goal', 'coefficient': '1'}]
INVALID = [{'hypothesis': 'hn', 'coefficient': '1'}, {'hypothesis': 'hz', 'coefficient': '1'}, {'hypothesis': 'neg_goal', 'coefficient': '2'}]
CASES = {'valid': (VALID, 'constrained', False), 'invalid_checked': (INVALID, 'constrained', False),
         'invalid_injected': (INVALID, 'constrained', True), 'valid_pinned': (VALID, 'pinned', False)}


class Stub:
    capture = site_freeze.CAPTURE


def lean(compiler, dest, cwd, argv, env):
    native = dest/'bridge/.lake/build/lib/lean'
    loads = [f'--load-dynlib={R6.parents[1]}/lean-bridge/.lake/build/lib/libpbglue.so',
             f"--load-dynlib={dest/'sdk/_build/default/ffi/proof_broker_ffi.so'}"]
    loads += [f'--load-dynlib={native}/{replay_bridge.MODULE_PREFIX}{m}.so' for m in replay_bridge.MODULES]
    full = {'PATH': '/usr/bin:/bin', 'LEAN_SYSROOT': str(compiler), 'LEAN_PATH': f'{native}:{cwd}', **env}
    return subprocess.run([str(compiler/'bin/lean'), *loads, *argv], cwd=cwd, env=full, capture_output=True, text=True)


def child_events(stderr):
    rows = []
    for line in stderr.splitlines():
        if line.startswith('R6_EVENT '):
            row = json.loads(line[len('R6_EVENT '):]); rows.append((row['event'], row.get('data', row)))
    return rows


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--output', required=True)
    out = Path(p.parse_args().output)
    if out.exists(): raise SystemExit(f'refusing to overwrite {out}')
    compiler, _, _ = r6.build_tools(task=r6.D1)
    dest, sources, _ = replay_bridge.build(compiler)
    driver = dest/'sdk/_build/default/validate/proposal_driver.exe'
    if WORK.exists(): shutil.rmtree(WORK)
    prep = WORK/'prepare'; prep.mkdir(parents=True)
    (prep/'PreparationCapture.lean').write_text(site_task.capture_source(Stub, True))
    (prep/'Synthetic.lean').write_text('import PreparationCapture\n\n' + GOAL.format(tactic='r6_prepare'))
    steps = {}
    built = lean(compiler, dest, prep, ['-o', 'PreparationCapture.olean', 'PreparationCapture.lean'], {})
    if built.returncode: raise SystemExit('preparation helper: ' + built.stderr[-2000:])
    prepared = lean(compiler, dest, prep, ['Synthetic.lean'], {'R6_PREPARE_OUTPUT': str(prep/'reification.json'),
                                                              'R6_CAPTURE_OUTPUT': str(prep/'context.json')})
    if prepared.returncode: raise SystemExit('preparation: ' + (prepared.stdout + prepared.stderr)[-2000:])
    r6.write_json(prep/'input-ir.json', r6.read_json(prep/'reification.json')['ir'])
    subprocess.run([str(driver), 'prepare', str(prep/'input-ir.json'), str(prep/'prepared.json')], check=True)
    results, failures = {}, {}
    for case, (coefficients, route, inject) in CASES.items():
        work = WORK/case; work.mkdir()
        r6.write_json(work/'response.json', {'witness': {'coefficients': coefficients}})
        subprocess.run([str(driver), 'assemble', str(prep/'prepared.json'), str(work/'response.json'), 'sha256:synthetic-rehearsal',
                        str(work/'evidence.json')], check=True)
        (work/'ProposalCapture.lean').write_text(replay_bridge.capture_source(site_task, Stub, route))
        (work/'Synthetic.lean').write_text('import ProposalCapture\n\n' + GOAL.format(tactic='r6_capture_proposal'))
        built = lean(compiler, dest, work, ['-o', 'ProposalCapture.olean', 'ProposalCapture.lean'], {})
        if built.returncode: raise SystemExit('reconstruction helper: ' + built.stderr[-2000:])
        env = {'R6_PROPOSAL_PACKET': str(work/'evidence.json'), 'PROOF_BROKER_EPISODE_TRACE': '1',
               'R6_CAPTURE_OUTPUT': str(work/'context.json')}
        if inject: env['R6_015_INJECT_UNVERIFIED'] = '1'
        proc = lean(compiler, dest, work, ['-o', 'Synthetic.olean', 'Synthetic.lean'], env)
        observed = child_events(proc.stderr)
        names = [e for e, _ in observed]
        data = dict(observed)
        errors = [l for l in (proc.stdout + proc.stderr).splitlines() if 'error' in l and not l.startswith('R6_EVENT')]
        r = {'exit': proc.returncode, 'events': names, 'errors': errors[:5], 'term_route': data.get('term_route'),
             'closer_selected': {k: v for k, v in (data.get('closer_selected') or {}).items() if k != 'certificate'},
             'reconstruction_finished': {k: v for k, v in (data.get('reconstruction_finished') or {}).items() if k != 'certificate'}}
        unmet = []
        if case == 'valid':
            if proc.returncode != 0: unmet.append('did not close')
            fin = data.get('reconstruction_finished') or {}
            if names[-3:] != ['term_route', 'closer_selected', 'reconstruction_finished'] or data['term_route'] != {'constrained': True} \
                    or fin.get('final_step') != 'constrained' or fin.get('residual_closer') != 'constrained_normalization' \
                    or (data.get('closer_selected') or {}).get('closer') != 'term_mode_int':
                unmet.append('constrained receipt')
            if not unmet:
                with open(work/'export.ndjson', 'wb') as f:
                    subprocess.run([str(EXPORTER), 'Synthetic', '--', 'c1_whole', 'c1_whole.r6_site_c1'], cwd=work, stdout=f, check=True,
                                   env={'PATH': '/usr/bin:/bin', 'LEAN_SYSROOT': str(compiler),
                                        'LEAN_PATH': f"{dest/'bridge/.lake/build/lib/lean'}:{work}"})
                synthetic = audit(work/'export.ndjson', None, work/'residual-report.json')
                residual = synthetic.get('audit', {}).get('local', {}).get('residual_goal')
                real = audit(work/'export.ndjson', residual, work/'control-8-report.json')
                r.update(residual_goal=residual, control_8=real.get('audit'), control_8_unmet=control_8(real))
                if residual is None or r['control_8_unmet']: unmet.append('control 8')
        elif case == 'invalid_checked':
            if proc.returncode == 0 or 'closer_selected' in names or not any('verifier did not' in e for e in errors):
                unmet.append('the bridge gate did not refuse')
        elif case == 'invalid_injected':
            if proc.returncode == 0 or 'certificate_gate_bypassed' not in names or (data.get('closer_selected') or {}).get('route') != 'constrained' \
                    or not any('does not cancel' in e for e in errors):
                unmet.append('injection did not reach the constrained closer and fail there')
        elif case == 'valid_pinned':
            if proc.returncode == 0 or data.get('term_route') != {'constrained': False} \
                    or (data.get('closer_selected') or {}).get('closer') != 'term_mode_nat' \
                    or not any('non-False ℕ goal must have shape' in e for e in errors):
                unmet.append('the pinned ℕ closer did not refuse')
        r['unmet'] = unmet; results[case] = r; failures[case] = unmet
        print(case, 'as expected' if not unmet else unmet, flush=True)
    passed = not any(failures.values())
    out.write_text(json.dumps({'passed': passed, 'failures': failures, 'results': results, 'bridge_rev': replay_bridge.BRIDGE_REV,
        'instrumented_tactic_sha256': sources['lean-bridge/ProofBroker/Tactic.lean']['instrumented_sha256'],
        'sources_sha256': {str(f.relative_to(R6.parents[1])): r6.sha(f) for f in
                           (HERE/'replay_bridge.py', HERE/'replay_episode.py', Path(__file__).resolve())},
        'scope': 'synthetic goals only; no site; no retained certificate; pre-lock'}, indent=1) + '\n')
    print(json.dumps({'passed': passed}))
    return 0 if passed else 1


def audit(export, residual, report):
    with tempfile.TemporaryDirectory(prefix='r6-016-rehearsal-') as tmp:
        argv = [str(replay_episode.AUDIT_TOOL)] + (['--synthetic'] if residual is None else [])
        if residual is not None: (Path(tmp)/'residual.txt').write_text(residual + '\n')
        argv += [str(export), 'c1_whole.r6_site_c1', 'c1_whole', '-' if residual is None else str(Path(tmp)/'residual.txt'), str(report)]
        proc = subprocess.run(argv, capture_output=True, text=True,
                              env={'PATH': '/usr/bin:/bin', 'LEAN_SYSROOT': str(replay_episode.AUDIT_TOOLCHAIN)})
    r = r6.read_json(report) if report.exists() else {'error': (proc.stdout + proc.stderr)[-1000:]}
    r['exit'] = proc.returncode
    return r


def control_8(r):
    """Revision 5's frozen predicate, in real mode."""
    a = r.get('audit')
    if r.get('exit') != 0 or 'refused' in r or not isinstance(a, dict): return ['exit, refusal or no report']
    unmet = [] if a.get('binding') == 'matches_residual' else [f"binding {a.get('binding')!r}"]
    for t in ('local', 'whole'):
        s = a.get(t)
        if not isinstance(s, dict) or s.get('locatable') is not True: unmet.append(f'{t} not locatable'); continue
        if not isinstance(s.get('hypotheses'), list) or s['hypotheses']: unmet.append(f'{t} hypotheses {s.get("hypotheses")}')
    return unmet


if __name__ == '__main__':
    raise SystemExit(main())
