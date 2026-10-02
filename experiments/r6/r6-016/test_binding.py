#!/usr/bin/env python3
"""R6-016: control 8's binding (`replay_campaign.bound`, `control8`) on synthetic sealed runs. R6-015's test
(`r6-015/test_binding.py`), on R6-016's modules: the provenance directory is `r6-016/`, R6-015's own schema is refused, and
`qualification-audit-v2`'s lock check is stubbed with the rest of the lock.

No Lean runs and no retained certificate is read: each run is written with R6's own event chain and seal (`events.append`,
`site_network.seal`), shaped as `replay_episode.execute` writes it; the locked plan, the lock and the packet source are synthetic
stand-ins (monkeypatched), and so is the audit program's report. Each probe must be refused before the outcome is used, and
control 8 must then fail. Run: `python3 r6-016/test_binding.py` (or under pytest).
"""
import copy
import json
import shutil
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
if str(R6) not in sys.path: sys.path.insert(0, str(R6))
if str(HERE) not in sys.path: sys.path.insert(0, str(HERE))

import events  # noqa: E402
import run as r6  # noqa: E402
import site_network  # noqa: E402
import site_task  # noqa: E402
import replay_campaign  # noqa: E402
import replay_episode  # noqa: E402
import replay_lock  # noqa: E402

SPEC = {'id': 'probe', 'site': 'bracket-l166', 'source': {'arm': 'learned', 'run': 'synthetic/probe'},
        'coefficients': None, 'inject_unverified': False, 'route': 'constrained'}
CERT = {'payload': {'witness_data': {'coefficients': [{'hypothesis': 'h', 'coefficient': '1'}]}}}
PACKET = {'input_ir': {'ir': 1}, 'final_ir': {'ir': 2}, 'trace': {'t': 1}, 'certificate': CERT}
HARNESS = {str(p.relative_to(R6)): r6.sha(p) for p in replay_episode.HARNESS}
FROZEN = {'bridge_rev': replay_episode.replay_bridge.BRIDGE_REV, 'instrumented_tactic_sha256': 'T' * 64,
          'python_sha256': dict(HARNESS)}


LOCK_SHA = None  # the stand-in lock's digest, set in `main`


def write_run(run, outcome='certificate_rejected', start=None, terminal=True, accepted=None, verdict_edit=None):
    """A run as `execute` writes it, with one deviation per probe."""
    run.mkdir(parents=True)
    payload = {'schema_version': replay_episode.SCHEMA, 'spec': SPEC, 'admission': 'planned', 'excluded_from_results': False,
               'lock_sha256': LOCK_SHA, 'harness_sha256': HARNESS, 'bridge_rev': FROZEN['bridge_rev']}
    payload.update(start or {})
    events.append(run, 'episode', 'episode_started', payload, task_id=SPEC['site'])
    r6.write_json(run/'spec.json', SPEC)
    for p in replay_episode.HARNESS:
        target = run/'provenance/r6-016'/p.name; target.parent.mkdir(parents=True, exist_ok=True); target.write_bytes(p.read_bytes())
    r6.write_json(run/'provenance/sources.json', {'lean-bridge/ProofBroker/Tactic.lean': {'instrumented_sha256': 'T' * 64}})
    r6.write_json(run/'evidence.json', PACKET)
    if outcome == 'proved':
        for name, data in [(n, {}) for n in replay_episode.PREFIX] + [
                ('term_route', {'constrained': True}),
                ('closer_selected', {'certificate': CERT, 'closer': 'term_mode_int', 'route': 'constrained'}),
                ('reconstruction_finished', {'certificate': CERT, 'closer': 'term_mode_int', 'certificate_consumed': True,
                                             'derivation_replayed': False, 'residual_closer': 'constrained_normalization',
                                             'final_step': 'constrained', 'constrained_option': True})]:
            events.append(run, 'reconstruct', name, {'component': 'lean_bridge', 'data': data}, source='child_report')
        (run/'solution.ndjson.gz').write_bytes(b'synthetic'); (run/'residual.txt').write_text('0 < 1\n')
    verdict = {'schema_version': replay_episode.SCHEMA, 'id': SPEC['id'], 'site': SPEC['site'], 'source': SPEC['source'],
               'route': SPEC['route'], 'coefficients': None, 'mutated': False, 'inject_unverified': False, 'admission': 'planned',
               'excluded_from_results': False, 'outcome': outcome}
    r6.write_json(run/'verdict.json', verdict)
    if terminal:
        events.append(run, 'episode', 'episode_finished', {'outcome': outcome, 'verdict_sha256': r6.sha(run/'verdict.json')})
    if verdict_edit:  # the verdict changed after the terminal event, then resealed
        r6.write_json(run/'verdict.json', {**verdict, **verdict_edit})
    site_network.seal(run, outcome == 'proved' if accepted is None else accepted)
    return run


def refused(run):
    try:
        replay_campaign.bound(run, SPEC, FROZEN, LOCK_SHA)
    except (OSError, ValueError, KeyError, replay_episode.Outcome) as caught:
        return str(caught)
    return None


def main():
    global LOCK_SHA
    site_task.get(SPEC['site'])  # registered, as `execute` registers it
    replay_episode.retained_packet = lambda spec: copy.deepcopy(PACKET)  # the packet provider, synthetic
    probes = {}
    with tempfile.TemporaryDirectory(prefix='r6-016-binding-') as tmp:
        tmp = Path(tmp)
        lock = tmp/'lock.json'; lock.write_text('{"stand-in": true}\n'); LOCK_SHA = r6.sha(lock)
        assert refused(write_run(tmp/'good')) is None, 'a well-formed run must bind'
        assert refused(write_run(tmp/'good-proved', 'proved')) is None, 'a well-formed proof must bind'
        cases = {
            'another lock': write_run(tmp/'lock', start={'lock_sha256': 'M' * 64}),
            'another bridge': write_run(tmp/'bridge', start={'bridge_rev': '0' * 40}),
            'another harness': write_run(tmp/'harness', start={'harness_sha256': {k: '0' * 64 for k in HARNESS}}),
            'another schema': write_run(tmp/'schema', start={'schema_version': 'r6-015-replay-2'}),
            'a rehearsal start': write_run(tmp/'rehearsal', start={'admission': 'rehearsal', 'excluded_from_results': True}),
            'resealed verdict disagreeing with the terminal event': write_run(tmp/'resealed', verdict_edit={'outcome': 'proved'}),
            'no terminal event': write_run(tmp/'unfinished', terminal=False),
            'no terminal event, proved': write_run(tmp/'unfinished-proved', 'proved', terminal=False),
            'seal acceptance disagrees': write_run(tmp/'accepted', accepted=True),
        }
        drift = write_run(tmp/'provenance')  # a harness copy changed, then resealed
        (drift/'provenance/r6-016/replay_lock.py').write_text('# changed\n'); site_network.seal(drift, False)
        cases['harness copy differs'] = drift
        bridge = write_run(tmp/'tactic')
        r6.write_json(bridge/'provenance/sources.json', {'lean-bridge/ProofBroker/Tactic.lean': {'instrumented_sha256': 'U' * 64}})
        site_network.seal(bridge, False); cases['instrumented Tactic differs'] = bridge
        unsealed = write_run(tmp/'unsealed'); (unsealed/'extra.txt').write_text('x'); cases['an unsealed file'] = unsealed
        for name, run in cases.items():
            probes[name] = refused(run)
            assert probes[name] is not None, f'accepted: {name}'
        # control 8 itself, on the reviewer's last case: an unfinished, sealed proof must make it fail
        replay_lock.LOCK = lock
        replay_lock.verify_lock = lambda: FROZEN
        replay_campaign.qualification_audit_v2.verify_lock = lambda: None
        replay_lock.planned = lambda frozen: {'probe': SPEC}
        replay_campaign.audit_real = lambda *a: ({'exit': 0, 'audit': {'binding': 'matches_residual',
            'local': {'locatable': True, 'hypotheses': []}, 'whole': {'locatable': True, 'hypotheses': []}}}, {})
        for name, run, expect in [('unfinished proof', tmp/'unfinished-proved', False), ('good proof', tmp/'good-proved', True)]:
            runs = tmp/f'runs-{expect}'; runs.mkdir(); shutil.copytree(run, runs/'probe')
            out = tmp/f'control8-{expect}.json'
            replay_campaign.control8(type('A', (), {'runs': str(runs), 'output': str(out)}))
            passed = json.loads(out.read_text())['passed']
            probes[f'control 8, {name}'] = passed
            assert passed is expect, f'control 8 on the {name}: passed {passed}'
    print(json.dumps(probes, indent=1))
    return probes


def test_binding():
    main()


if __name__ == '__main__':
    main()
