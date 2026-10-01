#!/usr/bin/env python3
"""R6-015 control 3, under the lock: the review's synthetic probe (`R6-015-PROPOSAL.md`, revision 5).

    control3.py --output RECORD.json

`h : x ≤ y ⊢ x ≤ y` with (`h` 1, `neg_goal` 2): the combination does not cancel. It is not a site; it is driven through R6's
own preparation and reconstruction helpers on the replay bridge, as `rehearse_synthetic.py` does, with the packet assembled by
R6's driver and delivered as in R6. The independent checker rejects the certificate, so both runs are injected
(`R6_015_INJECT_UNVERIFIED=1`), recorded as `certificate_gate_bypassed`.

Frozen expectations:
- **constrained** (the option set): the constrained closer is selected and fails, the weighted sum not cancelling;
- **pinned** (the option unset): R6's pinned fold closes it through contextual `omega`, with R6's receipt. This is the documented
  difference, recorded, not counted as consumption.

The R6-015 lock must verify before and after.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
if str(R6) not in sys.path: sys.path.insert(0, str(R6))
if str(HERE) not in sys.path: sys.path.insert(0, str(HERE))

import run as r6  # noqa: E402
import site_task  # noqa: E402
import replay_bridge  # noqa: E402
import replay_lock  # noqa: E402
from rehearse_synthetic import Stub, child_events, lean  # noqa: E402

WORK = R6/'.cache/r6-015-control3'
GOAL = 'theorem probe_whole (x y : Int) (h : x ≤ y) : x ≤ y := by\n  {tactic} "probe_whole.r6_site_probe" "synthetic-probe"\n'
PROBE = [{'hypothesis': 'h', 'coefficient': '1'}, {'hypothesis': 'neg_goal', 'coefficient': '2'}]


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--output', required=True)
    out = Path(p.parse_args().output)
    if out.exists(): raise SystemExit(f'refusing to overwrite {out}')
    try:
        replay_lock.verify_lock()
    except replay_lock.Refused as refused:
        raise SystemExit(str(refused))
    compiler, _, _ = r6.build_tools(task=r6.D1)
    dest, sources, _ = replay_bridge.build(compiler)
    driver = dest/'sdk/_build/default/validate/proposal_driver.exe'
    verifier = dest/'sdk/_build/default/validate/verify_certificate.exe'
    if WORK.exists(): shutil.rmtree(WORK)
    prep = WORK/'prepare'; prep.mkdir(parents=True)
    (prep/'PreparationCapture.lean').write_text(site_task.capture_source(Stub, True))
    (prep/'Synthetic.lean').write_text('import PreparationCapture\n\n' + GOAL.format(tactic='r6_prepare'))
    if lean(compiler, dest, prep, ['-o', 'PreparationCapture.olean', 'PreparationCapture.lean'], {}).returncode: raise SystemExit('preparation helper')
    prepared = lean(compiler, dest, prep, ['Synthetic.lean'], {'R6_PREPARE_OUTPUT': str(prep/'reification.json'),
                                                              'R6_CAPTURE_OUTPUT': str(prep/'context.json')})
    if prepared.returncode: raise SystemExit('preparation: ' + (prepared.stdout + prepared.stderr)[-2000:])
    r6.write_json(prep/'input-ir.json', r6.read_json(prep/'reification.json')['ir'])
    subprocess.run([str(driver), 'prepare', str(prep/'input-ir.json'), str(prep/'prepared.json')], check=True)
    r6.write_json(prep/'response.json', {'witness': {'coefficients': PROBE}})
    subprocess.run([str(driver), 'assemble', str(prep/'prepared.json'), str(prep/'response.json'), 'sha256:r6-015-control-3',
                    str(prep/'evidence.json')], check=True)
    subprocess.run([str(verifier), str(prep/'evidence.json'), str(prep/'verdict.json')], capture_output=True)
    checker = r6.read_json(prep/'verdict.json')
    results, unmet = {'checker': checker}, []
    if checker.get('accepted') is not False: unmet.append('the independent checker did not reject the probe')
    for route in ('constrained', 'pinned'):
        work = WORK/route; work.mkdir()
        (work/'ProposalCapture.lean').write_text(replay_bridge.capture_source(site_task, Stub, route))
        (work/'Synthetic.lean').write_text('import ProposalCapture\n\n' + GOAL.format(tactic='r6_capture_proposal'))
        if lean(compiler, dest, work, ['-o', 'ProposalCapture.olean', 'ProposalCapture.lean'], {}).returncode: raise SystemExit('helper')
        proc = lean(compiler, dest, work, ['-o', 'Synthetic.olean', 'Synthetic.lean'],
                    {'R6_PROPOSAL_PACKET': str(prep/'evidence.json'), 'PROOF_BROKER_EPISODE_TRACE': '1',
                     'R6_CAPTURE_OUTPUT': str(work/'context.json'), 'R6_015_INJECT_UNVERIFIED': '1'})
        observed = child_events(proc.stderr); names = [e for e, _ in observed]; data = dict(observed)
        errors = [line for line in (proc.stdout + proc.stderr).splitlines() if ': error: ' in line]
        results[route] = {'exit': proc.returncode, 'events': names, 'term_route': data.get('term_route'),
                          'closer_selected': {k: v for k, v in (data.get('closer_selected') or {}).items() if k != 'certificate'},
                          'reconstruction_finished': {k: v for k, v in (data.get('reconstruction_finished') or {}).items() if k != 'certificate'},
                          'errors': errors[:5]}
        if 'certificate_gate_bypassed' not in names: unmet.append(f'{route}: the injection was not recorded')
        if route == 'constrained':
            if proc.returncode == 0 or data.get('term_route') != {'constrained': True} \
                    or (data.get('closer_selected') or {}).get('route') != 'constrained' \
                    or not any('the weighted sum does not cancel' in e for e in errors):
                unmet.append('constrained: did not fail in the constrained final step')
        elif proc.returncode != 0 or data.get('term_route') != {'constrained': False} \
                or (data.get('reconstruction_finished') or {}).get('residual_closer') != 'omega':
            unmet.append('pinned: the documented difference did not reproduce')
    replay_lock.verify_lock()
    passed = not unmet
    out.write_text(json.dumps({'control': 3, 'passed': passed, 'unmet': unmet, 'results': results,
        'lock_sha256': r6.sha(replay_lock.LOCK), 'bridge_rev': replay_bridge.BRIDGE_REV,
        'instrumented_tactic_sha256': sources['lean-bridge/ProofBroker/Tactic.lean']['instrumented_sha256'],
        'documented_difference': 'the pinned fold closes the probe through contextual omega; not consumption'}, indent=1) + '\n')
    print(json.dumps({'passed': passed, 'unmet': unmet}))
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(main())
