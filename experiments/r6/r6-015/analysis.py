#!/usr/bin/env python3
"""R6-015 analysis, frozen before the lock (`R6-015-PROPOSAL.md`, revision 5, step 6).

    analysis.py --runs DIR --control3 RECORD.json --control8 RECORD.json --output ANALYSIS.json

Runs after the replay (`replay_campaign.py run`), control 3 (`control3.py`) and control 8 (`replay_campaign.py control8`), under
the R6-015 lock, which must verify before and after. Reads only bound evidence:
- **every planned run** is bound to the locked plan by `replay_campaign.bound` (seal, spec, start record and provenance, terminal
  event, seal acceptance, verdict identity, packet, and for a proof the receipt). A run that does not bind stops the analysis;
- **the control-3 and control-8 records** must name this lock;
- **the step-3 record** (`R6-015-MUTATIONS-2.json`, bound by the lock) supplies the maps, classes and control-5 labels;
- **R6-014's analysis** (`R6-014-BLOCK2-ANALYSIS.json`, bound by the lock) supplies the original closers (control 5) and the
  reference route's closures (control 7).

**Consumed and validated** (the proposal's acceptance, for one episode): the outcome is a proof; the receipt names this
certificate, the closer and the constrained final step (checked in binding); the local and whole kernel replays accepted; no axiom
added and every axiom among `propext`, `Classical.choice`, `Quot.sound` (acceptance 4); and control 8's predicate met.

**Failure stages**, from the verdict's bound evidence only. A failed reconstruction is classified by its first bridge error line,
against `STAGES` in order:
- certificate decoding, the packet binding (the fresh-reification guard), the bridge's gate, the specialization gate;
- selection; fact assertion (casts and opaque atoms included); the fold; the constrained final step;
- otherwise `unclassified`, which requires diagnosis.

A kernel rejection is `kernel`; a checker rejection is `checker`. A harness outcome (an unobserved receipt, a route mismatch, a
changed context, an unprinted residual, a stage or harness failure) is not a route result and requires diagnosis.

**Units:** results per obligation (4), per map (6) and per class (5), by source, never merged.

**The outcome, by the proposal's frozen definitions:**
- **complete success**: all 36 retained certificates consumed and validated (so all six maps, both sources, all four obligations,
  both l166 maps), and controls 1, 2, 3, 4, 6 and 8 as frozen;
- **none**: no retained certificate consumed and validated;
- **partial**: anything else, with the failures located per obligation, map and class.

Control 5's expectations are stated before replay, and a failure requires diagnosis: it is reported for every entry, but it is not
part of the outcome's definition. Control 7 is cited, never counted as consumption.
"""
import argparse
from collections import Counter
import gzip
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
if str(R6) not in sys.path: sys.path.insert(0, str(R6))
if str(HERE) not in sys.path: sys.path.insert(0, str(HERE))

import events  # noqa: E402
import run as r6  # noqa: E402
import replay_campaign  # noqa: E402
import replay_lock  # noqa: E402

MUTATIONS = R6/'reviews/2026-10-01/R6-015-MUTATIONS-2.json'
R6014 = R6/'reviews/2026-09-29/R6-014-BLOCK2-ANALYSIS.json'
TARGETS = ('l166', 'l175', 'l178', 'l204')
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
HARNESS_OUTCOMES = {'consumption_unobserved', 'route_mismatch', 'context_changed', 'residual_unprinted', 'stage_failure', 'harness_failure'}
STAGES = (  # (stage, detail, substring of the first bridge error line), in order
    ('certificate_decode', 'payload', 'proof_broker_term: cert missing'),
    ('certificate_decode', 'not farkas', 'proof_broker_term: cert is not a Farkas witness'),
    ('certificate_decode', 'coefficient', 'proof_broker_term: malformed coefficient'),
    ('certificate_decode', 'entry', 'proof_broker_term: witness entry missing hypothesis'),
    ('packet_binding', 'input IR', 'R6 proposal input differs'),
    ('bridge_gate', 'verifier', 'verifier did not'),
    ('specialization_gate', 'specialization', 'records a specialization'),
    ('specialization_gate', 'specialization', 'records no Nat → Int type specialization'),
    ('selection', 'outside the route', 'is outside the constrained route'),
    ('selection', 'goal shape', 'goal must have shape'),
    ('selection', 'goal shape', 'witness lacks neg_goal'),
    ('selection', 'goal shape', 'cert/goal mismatch'),
    ('fact_assertion', 'name not in scope', 'witness names hypothesis'),
    ('fact_assertion', 'cast', 'the ℕ→ℤ lift cannot cast'),
    ('fact_assertion', 'atom', 'but the extraction has no atom'),
    ('constrained_final_step', 'does not cancel', '(constrained): the weighted sum does not cancel'),
    ('constrained_final_step', 'not positive', 'which is not positive'),
    ('constrained_final_step', 'reaches hypotheses', '(constrained): the positivity proof reaches hypotheses'),
    ('constrained_final_step', 'kernel rejected the step', '(constrained): the kernel rejected the positivity proof'),
    ('fold', 'hypothesis shape', 'hypothesis shape outside'),
    ('fold', 'negative coefficient', 'negative coefficient'),
    ('fold', 'zero coefficients', 'all coefficients are zero'),
    ('fold', 'empty witness', 'empty witness'),
    ('fold', 'name not in scope', "' not in scope"),
    ('fold', 'shadowed', 'is ambiguous (shadowed)'),
)


def classify(verdict):
    """(stage, detail, line) for a non-proof, from the verdict's bound evidence only."""
    outcome = verdict['outcome']
    if outcome == 'proved': return ('proved', None, None)
    if outcome == 'certificate_rejected': return ('checker', None, None)
    if outcome == 'kernel_rejected': return ('kernel', None, str(verdict.get('detail'))[:300])
    if outcome in HARNESS_OUTCOMES: return ('harness', outcome, str(verdict.get('detail'))[:300])
    if outcome != 'reconstruction_failed': return ('unclassified', outcome, None)
    errors = (verdict.get('detail') or {}).get('errors') or []
    line = next((e for e in errors if 'proof_broker' in e or 'R6 proposal' in e), None)
    if line is None: return ('unclassified', 'no bridge error line', errors[0][:300] if errors else None)
    for stage, detail, needle in STAGES:
        if needle in line: return (stage, detail, line[:300])
    return ('unclassified', 'no stage matched', line[:300])


def reconstruct_events(run):
    return [(r['event'], r['payload']['data']) for r in events.read(run/'events.ndjson') if r['source'] == 'child_report' and r['stage'] == 'reconstruct']


def packet_certificate(run):
    return r6.read_json(run/'evidence.json')['certificate']


def axioms_ok(run, verdict):
    for name in ('local', 'whole'):
        report = json.loads(gzip.decompress((run/f'validation-{name}.raw.json.gz').read_bytes()))
        if report.get('accepted') is not True: return False
        if any(not set(t['axioms']) <= ALLOWED_AXIOMS for t in report['targets']): return False
    return all(not d['added'] for d in verdict['axiom_delta'].values())


def analyse(runs, control3, control8):
    frozen = replay_lock.verify_lock(); lock_sha = r6.sha(replay_lock.LOCK)
    for name, record in (('control 3', control3), ('control 8', control8)):
        if record.get('lock_sha256') != lock_sha: raise SystemExit(f'the {name} record does not name this lock')
    plan = replay_lock.planned(frozen); mutations = r6.read_json(MUTATIONS); r6014 = r6.read_json(R6014)
    episodes = {}
    for spec in plan.values():
        run = runs/spec['id']
        try:
            _, verdict = replay_campaign.bound(run, spec, frozen, lock_sha)
        except (OSError, ValueError, KeyError, replay_campaign.replay_episode.Outcome) as unbound:
            raise SystemExit(f"{spec['id']} does not bind: {unbound}")
        stage, detail, line = classify(verdict)
        observed = reconstruct_events(run); found = dict(observed)
        c8 = control8['results'].get(spec['id'])
        proved = verdict['outcome'] == 'proved'
        accepted = proved and verdict.get('local_validated') is True and verdict.get('whole_validated') is True and axioms_ok(run, verdict)
        c8_ok = bool(c8 and c8.get('bound') and c8.get('audited') and c8.get('unmet') == [])
        episodes[spec['id']] = {
            'site': spec['site'].removeprefix('bracket-'), 'arm': spec['source']['arm'], 'source': spec['source']['run'],
            'mutated': spec['coefficients'] is not None, 'injected': spec['inject_unverified'], 'outcome': verdict['outcome'],
            'stage': stage, 'stage_detail': detail, 'error_line': line, 'certificate_accepted': verdict.get('certificate_accepted'),
            'closer_selected': (found.get('closer_selected') or {}).get('closer'),
            'comparison_type': (found.get('closer_selected') or {}).get('comparison_type'),
            'gate_bypassed': 'certificate_gate_bypassed' in found and found['certificate_gate_bypassed'].get('certificate') ==
                             packet_certificate(run),
            'closer': verdict.get('closer'), 'final_step': verdict.get('final_step'), 'kernel_and_axioms': accepted,
            'control_8': c8_ok if proved else None, 'consumed_and_validated': accepted and c8_ok}
    if not set(control8['results']) <= set(episodes): raise SystemExit('control 8 covers episodes outside the plan')
    if {i for i, e in episodes.items() if e['outcome'] == 'proved'} - {i for i, r in control8['results'].items() if r.get('audited')}:
        raise SystemExit('a proof was not audited by control 8')

    # the measurement: the 36 retained certificates of the four obligations
    measurement = {i: e for i, e in episodes.items() if e['site'] in TARGETS and not e['mutated'] and not e['injected']}
    if len(measurement) != 36: raise SystemExit('the measurement is not 36 episodes')
    def unit(e, kind):
        s = mutations['sources'][e['source']]
        return json.dumps([e['site'], s['map' if kind == 'map' else 'class']], sort_keys=True)
    def tally(selected):
        return {'episodes': len(selected), 'consumed_and_validated': sum(e['consumed_and_validated'] for e in selected),
                'stages': dict(Counter(e['stage'] if not e['consumed_and_validated'] else 'consumed_and_validated' for e in selected))}
    per_obligation = {site: {arm: tally([e for e in measurement.values() if e['site'] == site and e['arm'] == arm])
                             for arm in ('learned', 'deterministic')} for site in TARGETS}
    per_map, per_class = {}, {}
    for kind, table in (('map', per_map), ('class', per_class)):
        for key in sorted({unit(e, kind) for e in measurement.values()}):
            sel = [e for e in measurement.values() if unit(e, kind) == key]
            table[key] = {arm: tally([e for e in sel if e['arm'] == arm]) for arm in ('learned', 'deterministic') if any(e['arm'] == arm for e in sel)}
    if (len(per_map), len(per_class)) != (6, 5): raise SystemExit('the units are not 6 maps and 5 classes')

    # the controls
    def ids(pred): return [i for i, e in episodes.items() if pred(i, e)]
    c1 = ids(lambda i, e: e['site'] in TARGETS and e['mutated'] and e['injected'])
    c2 = ids(lambda i, e: e['site'] in TARGETS and e['mutated'] and not e['injected'])
    c4 = ids(lambda i, e: e['site'] == 'l170')
    c5 = ids(lambda i, e: '-control5-' in i)
    controls = {
        'control_1': {'episodes': len(c1), 'failures': [i for i in c1 if not (episodes[i]['certificate_accepted'] is False
                       and episodes[i]['gate_bypassed'] and episodes[i]['outcome'] != 'proved')],
                      'stages': dict(Counter(episodes[i]['stage'] for i in c1))},
        'control_2': {'episodes': len(c2), 'failures': [i for i in c2 if not episodes[i]['consumed_and_validated']],
                      'stages': dict(Counter(episodes[i]['stage'] for i in c2))},
        'control_3': {'passed': control3.get('passed') is True, 'unmet': control3.get('unmet')},
        'control_4': {'episodes': len(c4), 'failures': [i for i in c4 if not (
                       (episodes[i]['injected'] and episodes[i]['certificate_accepted'] is False and episodes[i]['gate_bypassed']
                        and episodes[i]['outcome'] != 'proved')
                       or (not episodes[i]['injected'] and episodes[i]['outcome'] == 'certificate_rejected'))]},
        'control_6': {'checked': 0, 'failures': []},
        'control_7': {'cited': {s: {'outcome': r6014['arms']['deterministic_reference']['by_site'][f'bracket-{s}'],
                                    'closer': r6014['arms']['deterministic_reference']['closers'][f'bracket-{s}']} for s in TARGETS},
                      'counted_as_consumption': False},
        'control_8': {'passed': control8.get('passed') is True,
                      'failures': [i for i, r in control8['results'].items() if not (r.get('bound') and (not r.get('audited') or r.get('unmet') == []))]},
    }
    for i, e in episodes.items():  # control 6: a Nat comparison takes the ℕ closer, any other the ℤ closer
        if e['closer_selected'] is None: continue
        controls['control_6']['checked'] += 1
        if (e['comparison_type'] in ('ℕ', 'Nat')) != (e['closer_selected'] == 'term_mode_nat'): controls['control_6']['failures'].append(i)
    for name in ('control_1', 'control_2', 'control_4', 'control_6'):
        controls[name]['passed'] = not controls[name]['failures']
    expected_sizes = {'control_1': 24, 'control_2': 25, 'control_4': 9}
    for name, n in expected_sizes.items():
        if controls[name]['episodes'] != n: raise SystemExit(f'{name} has {controls[name]["episodes"]} episodes')

    # control 5: each entry against its stated expectation
    original = {}
    for slot, row in r6014['per_slot'].items():
        site = slot.split('/')[0].removeprefix('bracket-')
        if row.get('closer'): original.setdefault(site, set()).add(row['closer'])
    entries = []
    for c in mutations['control_5']:
        if c.get('retained') is False: entries.append({'site': c['site'], 'arm': 'deterministic', 'retained': False}); continue
        id_ = f"{c['site']}-control5-learned-draw{c['draws'][0]}" if c['source']['arm'] == 'learned' else f"{c['site']}-control5-deterministic"
        e = episodes[id_]; closers = original.get(c['site'], set())
        if len(closers) != 1: raise SystemExit(f"{c['site']}: R6-014's closer is not unique")
        closer_ok = e['closer'] == next(iter(closers))
        passed = e['consumed_and_validated'] and closer_ok
        entries.append({'episode': id_, 'site': c['site'], 'arm': c['source']['arm'], 'map': c['map'], 'expectation': c['expectation'],
                        'passed': passed, 'original_closer': next(iter(closers)), 'closer': e['closer'], 'stage': e['stage'],
                        'requires_diagnosis': c['expectation'] == 'expected_pass' and not passed})
    controls['control_5'] = {'episodes': len(c5), 'entries': entries,
                             'expected_pass_met': sum(1 for x in entries if x.get('expectation') == 'expected_pass' and x['passed']),
                             'expected_pass': sum(1 for x in entries if x.get('expectation') == 'expected_pass'),
                             'requires_diagnosis': [x['episode'] for x in entries if x.get('requires_diagnosis')]}

    consumed = sum(e['consumed_and_validated'] for e in measurement.values())
    frozen_controls = all(controls[c]['passed'] for c in ('control_1', 'control_2', 'control_3', 'control_4', 'control_6', 'control_8'))
    outcome = ('complete_success' if consumed == 36 and frozen_controls else 'none' if consumed == 0 else 'partial')
    replay_lock.verify_lock()
    return {'schema_version': 'r6-015-analysis-1', 'lock_sha256': lock_sha, 'outcome': outcome,
            'measurement': {'consumed_and_validated': consumed, 'of': 36, 'per_obligation': per_obligation, 'per_map': per_map,
                            'per_class': per_class},
            'frozen_controls_as_expected': frozen_controls, 'controls': controls, 'episodes': episodes,
            'scope': 'R6-015, offline; reported separately from R6-014 and never pooled with it'}


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--runs', required=True); p.add_argument('--control3', required=True); p.add_argument('--control8', required=True)
    p.add_argument('--output', required=True)
    args = p.parse_args()
    out = Path(args.output)
    if out.exists(): raise SystemExit(f'refusing to overwrite {out}')
    try:
        result = analyse(Path(args.runs).resolve(), r6.read_json(args.control3), r6.read_json(args.control8))
    except replay_lock.Refused as refused:
        raise SystemExit(str(refused))
    out.write_text(json.dumps(result, indent=1) + '\n')
    print(json.dumps({'outcome': result['outcome'], 'consumed_and_validated': result['measurement']['consumed_and_validated']}))


if __name__ == '__main__':
    main()
