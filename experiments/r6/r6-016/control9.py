#!/usr/bin/env python3
"""R6-016 control 9, under the R6-016 lock: the normalizer (`R6-016-PROPOSAL.md`, revision 2, section 5).

    control9.py --output RECORD.json [--dry-run]

Synthetic goals, none a site, driven through R6's own preparation and reconstruction helpers on the replay bridge, as control 3
is (`control3.py`): R6's preparation helper reifies each goal, R6's driver prepares the problem and assembles the packet from the
witness frozen here, R6's independent checker verifies it, and R6's reconstruction helper runs with the frozen option setting,
the packet delivered as in R6. A case the checker rejects runs injected (`R6_015_INJECT_UNVERIFIED=1`), recorded as
`certificate_gate_bypassed`; each case's checker verdict is frozen with it.

**The cases** (`CASES`), each with its frozen expectation:
- **9a, the axiom gate:** `posOfLinearNum` depends on exactly `propext` and `Quot.sound`; the mixed-carrier goal closes through
  the route; and its theorem's axioms are among its `omega` proof's, which avoids `Classical.choice`. The axioms are read with
  `#print axioms` in the same file;
- **9b, no commutativity:** `h : x * y ≤ 5 ⊢ y * x ≤ 5` with (`h` 1, `neg_goal` 1) fails, the sum not cancelling;
- **9c, product identity:** the same product in the same order closes; `↑(a * b)` against `↑a * ↑b` closes;
- **9d, numeral products:** `3 * (a − b)` (with `neg_goal` 3), `a * 0`, and `↑(Zmax * 2 ^ 16)` against `65536 * ↑Zmax` close;
- **9e, ℕ nonnegativity is not used:** `m < m + n + 1` with `neg_goal` alone fails, the sum not cancelling; with `_pb_nonneg_n`
  it closes;
- **9f, a hypothesis reached through the sum:** a cast instance taking a hypothesis (the bridge review's case) fails, the
  positivity proof reaching it.

**A closing case** must exit 0 with the constrained receipt (`term_route` set, the closer selected on the constrained route,
`final_step: constrained`); **a failing case** must reach the constrained closer and fail in its final step, with the frozen
reason. `--dry-run` skips the lock and labels the record so; the analysis rejects a dry run.
"""
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
if str(R6) not in sys.path: sys.path.insert(0, str(R6))
if str(HERE) not in sys.path: sys.path.insert(0, str(HERE))

import events  # noqa: E402
import run as r6  # noqa: E402
import site_task  # noqa: E402
import replay_bridge  # noqa: E402
import replay_lock  # noqa: E402
from rehearse_synthetic import Stub, child_events, lean  # noqa: E402

WORK = R6/'.cache/r6-016-control9'
SCHEMA = 'r6-016-control-9-1'
SOURCES = (Path(__file__).resolve(), HERE/'rehearse_synthetic.py', HERE/'replay_bridge.py', HERE/'replay_lock.py')
CAST_VIA_HYP = '@[reducible] def castViaHyp (_h : True) : NatCast Int := instNatCastInt\n\n'
ALLOWED = ['propext', 'Quot.sound']


def w(*pairs): return [{'hypothesis': h, 'coefficient': str(c)} for h, c in pairs]


# name -> (preamble, binders and statement, witness, frozen checker verdict, expectation)
#   expectation: 'closes', or the substring of the constrained final step's failure. The checker verdicts were observed in the
#   pre-lock dry runs on these synthetic goals and are frozen here.
#   R6's preparation helper closes its goal with `omega`, so 9b and 9f carry one hypothesis (`hc`, `h'`) that lets `omega` prove
#   the goal. The witness does not use it.
CASES = {
    'c9a': ('', '(n m : Nat) (z : Int) (hn : n ≤ m) (hz : z + ↑m ≤ 5) : z + ↑n ≤ 5',
            w(('hn', 1), ('hz', 1), ('neg_goal', 1)), True, 'closes'),
    'c9b': ('', '(x y : Int) (h : x * y ≤ 5) (hc : y * x ≤ x * y) : y * x ≤ 5', w(('h', 1), ('neg_goal', 1)), False,
            'the weighted sum does not cancel'),
    'c9c_order': ('', '(x y : Int) (h : x * y ≤ 5) : x * y ≤ 5', w(('h', 1), ('neg_goal', 1)), True, 'closes'),
    'c9c_cast': ('', '(a b : Nat) (z : Int) (h : (a : Int) * (b : Int) ≤ z) : ((a * b : Nat) : Int) ≤ z',
                 w(('h', 1), ('neg_goal', 1)), False, 'closes'),
    'c9d_factor': ('', '(a b : Int) (h : 3 * (a - b) ≤ 6) : a ≤ b + 2', w(('h', 1), ('neg_goal', 3)), True, 'closes'),
    'c9d_zero': ('', '(a b : Int) (h : a * 0 + b ≤ 0) : b ≤ 0', w(('h', 1), ('neg_goal', 1)), True, 'closes'),
    'c9d_power': ('', '(Zmax : Nat) (v : Int) (h : ((Zmax * 2 ^ 16 : Nat) : Int) ≤ v) : (65536 : Int) * Zmax ≤ v',
                  w(('h', 1), ('neg_goal', 1)), True, 'closes'),
    'c9e_without': ('', '(m n : Nat) : m < m + n + 1', w(('neg_goal', 1)), False, 'the weighted sum does not cancel'),
    'c9e_with': ('', '(m n : Nat) : m < m + n + 1', w(('neg_goal', 1), ('_pb_nonneg_n', 1)), True, 'closes'),
    'c9f': (CAST_VIA_HYP, "(tag : True) (n m : Nat) (h : n ≤ m) "
            "(h' : @NatCast.natCast Int (castViaHyp tag) n ≤ @NatCast.natCast Int (castViaHyp tag) m) : "
            "@NatCast.natCast Int (castViaHyp tag) n ≤ @NatCast.natCast Int (castViaHyp tag) m",
            w(('h', 1), ('neg_goal', 1)), True, 'the positivity proof reaches hypotheses [tag]'),
}
AXIOMS = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")


def goal(name, tactic):
    preamble, statement, _, _, _ = CASES[name]
    return preamble + f'theorem {name}_whole {statement} := by\n  {tactic} "{name}_whole.r6_site_{name}" "synthetic-{name}"\n'


def axioms_appendix(name):
    """9a: the route's theorem, its `omega` proof's, and the final step's lemma, printed in the same file."""
    _, statement, _, _, _ = CASES[name]
    return (f'\ntheorem {name}_omega {statement} := by omega\n\n#print axioms {name}_whole\n#print axioms {name}_omega\n'
            '#print axioms ProofBroker.TermMode.posOfLinearNum\n')


def evaluate(results):
    """Control 9's frozen expectations, from its results; the analysis recomputes this. Returns the unmet ones."""
    unmet = []
    for name, (_, _, _, checker, expectation) in CASES.items():
        r = results.get(name)
        if not isinstance(r, dict): unmet.append(f'{name}: no result'); continue
        accepted = (r.get('checker') or {}).get('accepted')
        if accepted is not True and accepted is not False: unmet.append(f'{name}: no checker verdict'); continue
        if checker is not None and accepted is not checker: unmet.append(f'{name}: the checker verdict is not the frozen one')
        if r.get('injected') is not (accepted is False): unmet.append(f'{name}: injected exactly when the checker rejects')
        if r.get('injected') and 'certificate_gate_bypassed' not in (r.get('events') or []): unmet.append(f'{name}: injection not recorded')
        selected = r.get('closer_selected') or {}
        if r.get('term_route') != {'constrained': True} or selected.get('route') != 'constrained':
            unmet.append(f'{name}: the constrained closer was not reached'); continue
        if type(r.get('exit')) is not int: unmet.append(f'{name}: no exit'); continue
        if expectation == 'closes':
            finished = r.get('reconstruction_finished') or {}
            if r['exit'] != 0 or finished.get('final_step') != 'constrained' or finished.get('residual_closer') != 'constrained_normalization' \
                    or finished.get('closer') != selected.get('closer'):
                unmet.append(f'{name}: did not close with the constrained receipt')
        elif r['exit'] == 0 or not any(f'(constrained): {expectation}' in e for e in r.get('errors') or []):
            unmet.append(f'{name}: did not fail in the constrained final step as frozen ({expectation})')
    a = (results.get('c9a') or {}).get('axioms') or {}
    whole, omega, step = a.get('c9a_whole'), a.get('c9a_omega'), a.get('ProofBroker.TermMode.posOfLinearNum')
    if step != ALLOWED: unmet.append(f'9a: posOfLinearNum depends on {step}, not exactly {ALLOWED}')
    if not isinstance(omega, list) or 'Classical.choice' in omega: unmet.append("9a: the goal's omega proof does not avoid Classical.choice")
    if not isinstance(whole, list) or not isinstance(omega, list) or not set(whole) <= set(omega):
        unmet.append(f'9a: the route adds an axiom ({whole} against {omega})')
    return unmet


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--output', required=True); p.add_argument('--dry-run', action='store_true')
    args = p.parse_args(); out = Path(args.output)
    if out.exists(): raise SystemExit(f'refusing to overwrite {out}')
    if not args.dry_run:
        try:
            replay_lock.verify_lock()
        except replay_lock.Refused as refused:
            raise SystemExit(str(refused))
    compiler, _, _ = r6.build_tools(task=r6.D1)
    dest, sources, _ = replay_bridge.build(compiler)
    driver = dest/'sdk/_build/default/validate/proposal_driver.exe'
    verifier = dest/'sdk/_build/default/validate/verify_certificate.exe'
    if WORK.exists(): shutil.rmtree(WORK)
    results, evidence = {}, {}
    for name, (_, _, witness, _, _) in CASES.items():
        prep = WORK/name/'prepare'; prep.mkdir(parents=True)
        (prep/'PreparationCapture.lean').write_text(site_task.capture_source(Stub, True))
        (prep/'Synthetic.lean').write_text('import PreparationCapture\n\n' + goal(name, 'r6_prepare'))
        if lean(compiler, dest, prep, ['-o', 'PreparationCapture.olean', 'PreparationCapture.lean'], {}).returncode: raise SystemExit('preparation helper')
        prepared = lean(compiler, dest, prep, ['Synthetic.lean'], {'R6_PREPARE_OUTPUT': str(prep/'reification.json'),
                                                                  'R6_CAPTURE_OUTPUT': str(prep/'context.json')})
        if prepared.returncode:
            results[name] = {'prepared': False, 'errors': [l for l in (prepared.stdout + prepared.stderr).splitlines() if 'error' in l][:5]}
            print(name, 'preparation failed', flush=True); continue
        r6.write_json(prep/'input-ir.json', r6.read_json(prep/'reification.json')['ir'])
        subprocess.run([str(driver), 'prepare', str(prep/'input-ir.json'), str(prep/'prepared.json')], check=True)
        r6.write_json(prep/'response.json', {'witness': {'coefficients': witness}})
        subprocess.run([str(driver), 'assemble', str(prep/'prepared.json'), str(prep/'response.json'), f'sha256:r6-016-control-9-{name}',
                        str(prep/'evidence.json')], check=True)
        subprocess.run([str(verifier), str(prep/'evidence.json'), str(prep/'verdict.json')], capture_output=True)
        checker = r6.read_json(prep/'verdict.json'); injected = checker.get('accepted') is not True
        work = WORK/name/'constrained'; work.mkdir()
        (work/'ProposalCapture.lean').write_text(replay_bridge.capture_source(site_task, Stub, 'constrained'))
        (work/'Synthetic.lean').write_text('import ProposalCapture\n\n' + goal(name, 'r6_capture_proposal')
                                           + (axioms_appendix(name) if name == 'c9a' else ''))
        if lean(compiler, dest, work, ['-o', 'ProposalCapture.olean', 'ProposalCapture.lean'], {}).returncode: raise SystemExit('helper')
        env = {'R6_PROPOSAL_PACKET': str(prep/'evidence.json'), 'PROOF_BROKER_EPISODE_TRACE': '1', 'R6_CAPTURE_OUTPUT': str(work/'context.json')}
        if injected: env['R6_015_INJECT_UNVERIFIED'] = '1'
        proc = lean(compiler, dest, work, ['-o', 'Synthetic.olean', 'Synthetic.lean'], env)
        observed = child_events(proc.stderr); names = [e for e, _ in observed]; data = dict(observed)
        errors = [line for line in (proc.stdout + proc.stderr).splitlines() if ': error: ' in line]
        results[name] = {'prepared': True, 'checker': checker, 'injected': injected, 'exit': proc.returncode, 'events': names,
                         'term_route': data.get('term_route'),
                         'closer_selected': {k: v for k, v in (data.get('closer_selected') or {}).items() if k != 'certificate'},
                         'reconstruction_finished': {k: v for k, v in (data.get('reconstruction_finished') or {}).items() if k != 'certificate'},
                         'errors': errors[:5]}
        if name == 'c9a':
            results[name]['axioms'] = {m.group(1): [x.strip() for x in m.group(2).split(',') if x.strip()]
                                       for m in AXIOMS.finditer(proc.stdout + proc.stderr)}
        evidence[name] = {'evidence_sha256': r6.sha(prep/'evidence.json'),
                          'certificate_sha256': events.digest(r6.read_json(prep/'evidence.json')['certificate']), 'coefficients': witness}
        print(name, 'exit', proc.returncode, 'checker', checker.get('accepted'), flush=True)
    unmet = evaluate(results)
    if not args.dry_run: replay_lock.verify_lock()
    passed = not unmet
    record = {'schema_version': SCHEMA, 'control': 9, 'passed': passed, 'unmet': unmet, 'results': results, 'evidence': evidence,
              'cases': {n: {'statement': c[1], 'witness': c[2], 'checker': c[3], 'expectation': c[4]} for n, c in CASES.items()},
              'sources_sha256': {str(f.relative_to(R6)): r6.sha(f) for f in SOURCES},
              'lock_sha256': None if args.dry_run else r6.sha(replay_lock.LOCK), 'bridge_rev': replay_bridge.BRIDGE_REV,
              'instrumented_tactic_sha256': sources['lean-bridge/ProofBroker/Tactic.lean']['instrumented_sha256']}
    if args.dry_run: record['dry_run'] = 'pre-lock rehearsal on synthetic goals; not control 9'
    out.write_text(json.dumps(record, indent=1) + '\n')
    print(json.dumps({'passed': passed, 'unmet': unmet}))
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(main())
