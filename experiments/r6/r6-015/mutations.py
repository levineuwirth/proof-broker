#!/usr/bin/env python3
"""R6-015 step 3: the mutation sets, their validity labels, the control-5 maps and the plan (`R6-015-PROPOSAL.md`, revision 5).

    mutations.py --record RECORD.json --plan PLAN.json

Reads retained R6 evidence only; replays nothing and runs no closer. The live-evaluation-v3 lock is verified before and after,
and every source file against its run's seal.

**Sources.** A learned source is a run's retained `evidence.json`; a deterministic source is the packet rebuilt from the run's
sealed events (`replay_episode.retained_packet`). Each packet's rows are derived again with R6's driver (`proposal_driver
prepare` on the packet's input IR); the derived final IR must equal the packet's, and for a learned run the rows must equal the
run's retained `prepared.json`.

**Two independent labels for every certificate and mutation**, which must agree, or the program stops:
- **exact rational arithmetic** over the rows, mirroring the SDK's Farkas check (`Farkas.verify` at R6's base): every entry names
  a row; a negative multiplier only on an equation; the weighted sum leaves no variable; its constant is positive, or
  non-negative when a strict row carries a positive multiplier;
- **R6's independent checker** (`verify_certificate`), on the packet.

**Units** (proposal, "Units"): raw ordering (the list as retained), coefficient map (name → multiplier, order ignored, zeros
dropped) and class (the map divided by the gcd of its absolute multipliers). The counts must equal the proposal's.

**Mutation rules, fixed here before anything is computed**, for each of the six maps of the four obligations, each applied to the
map's representative packet (the lowest learned draw with that map, else the deterministic run). Entries are taken in sorted
hypothesis-name order wherever a choice is made; `neg_goal` is never the chosen entry of rules 2-4 or 8.

Invalid (control 1; each replayed injected, so that both the checker's rejection and the closer's failure are recorded):
1. `neg_goal_doubled`: `neg_goal`'s multiplier ×2;
2. `inequality_doubled`: the first inequality entry whose doubling makes the arithmetic invalid;
3. `hypothesis_dropped`: the first entry whose removal makes the arithmetic invalid;
4. `unrelated_inequality_added`: the first inequality row outside the map whose addition with multiplier 1 makes the arithmetic
   invalid.

Validity-preserving (control 2; each replayed through the checked path):
5. `scaled_2`, 6. `scaled_3`: every multiplier ×2, ×3;
7. `reordered`: the retained list reversed (rotated by one if reversal leaves it unchanged);
8. `zero_entry_added`: the first row outside the map appended with multiplier 0;
9. at l166 only, `hrec_dropped`: `hrec` removed from the deterministic map, which must then equal the learned map.

A rule with no candidate is recorded as not applicable. An invalid mutation must be invalid by both labels, a valid one valid by
both; otherwise the program stops.

**Control 5**: every distinct (source, map) retained for the six proved obligations, with each map's identity, the audited learned
slots it matches (with their qualification-audit classifications) and its expectation label, per revision 5.

**Control 4**: l170's eight retained proposals, labelled; replayed through the checked path, and the first one also injected.

**The plan** lists every episode: the 36 retained certificates of the four obligations, control 5, the mutation sets, control 4.
"""
import argparse
from collections import Counter
from fractions import Fraction
import json
from math import gcd
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
if str(R6) not in sys.path: sys.path.insert(0, str(R6))
if str(HERE) not in sys.path: sys.path.insert(0, str(HERE))
if str(R6/'qualification-audit') not in sys.path: sys.path.insert(0, str(R6/'qualification-audit'))

import events  # noqa: E402
import qualification_audit  # noqa: E402
import run as r6  # noqa: E402
import replay_bridge  # noqa: E402
import replay_episode  # noqa: E402
import replay_lock  # noqa: E402

TARGETS = ('l166', 'l175', 'l178', 'l204')
PROVED = ('l069', 'l070', 'l071', 'l078', 'l096', 'l099')
DETERMINISTIC = 'census-runs/deterministic-v1/site_cvc4_term_mode_v1/bracket-{site}'
AUDIT = R6/'reviews/2026-10-01/R6-QUALIFICATION-1-AUDIT.json'
PROPOSAL_COUNTS = {'learned': {'orderings': 7, 'maps': 4, 'classes': 4}, 'both': {'maps': 6, 'classes': 5}}
INEQUALITY = ('le', 'lt')


def learned_run(site, draw):
    name = f'cohort-live-v9/{site}-draw{draw}'
    return name + '-attempt2' if (R6/(name + '-attempt2')).exists() else name


def source(site, arm, draw=None):
    run = learned_run(site, draw) if arm == 'learned' else DETERMINISTIC.format(site=site)
    return {'arm': arm, 'run': run}


def packet_of(src):
    return replay_episode.retained_packet({'source': src})


def entries(packet):
    return packet['certificate']['payload']['witness_data']['coefficients']


def coefficient_map(es):
    m = Counter()
    for e in es: m[e['hypothesis']] += Fraction(e['coefficient'])
    return {k: v for k, v in sorted(m.items()) if v != 0}


def class_of(m):
    if any(v.denominator != 1 for v in m.values()): raise ValueError('a non-integer multiplier')
    g = 0
    for v in m.values(): g = gcd(g, abs(int(v)))
    return {k: v / g for k, v in m.items()}


def show(m):
    return {k: str(v) for k, v in m.items()}


def arithmetic(rows, es):
    """`Farkas.verify`'s arithmetic over the emitted rows, exactly."""
    by_name = {}
    for r in rows: by_name.setdefault(r['name'], []).append(r)
    if any(len(v) > 1 for v in by_name.values()): return {'valid': False, 'reason': 'duplicate_hypothesis'}
    if not es: return {'valid': False, 'reason': 'malformed_witness'}
    acc, const, strict = Counter(), Fraction(0), False
    for e in es:
        c = Fraction(e['coefficient']); row = by_name.get(e['hypothesis'])
        if row is None: return {'valid': False, 'reason': 'unknown_hypothesis', 'hypothesis': e['hypothesis']}
        row = row[0]
        if row['relation'] in INEQUALITY and c < 0: return {'valid': False, 'reason': 'negative_coefficient', 'hypothesis': e['hypothesis']}
        if row['relation'] == 'lt' and c > 0: strict = True
        for t in row['terms']: acc[t['variable']] += c * Fraction(t['coefficient'])
        const += c * Fraction(row['constant'])
    residual = {k: str(v) for k, v in sorted(acc.items()) if v != 0}
    if residual: return {'valid': False, 'reason': 'not_contradictory', 'residual': residual, 'constant': str(const)}
    valid = const >= 0 if strict else const > 0
    return {'valid': valid, 'reason': 'verified' if valid else 'not_contradictory', 'constant': str(const), 'strict': strict}


class Tools:
    def __init__(self):
        compiler, _, _ = r6.build_tools(task=r6.D1)
        dest, _, _ = replay_bridge.build(compiler)
        self.driver = dest/'sdk/_build/default/validate/proposal_driver.exe'
        self.verifier = dest/'sdk/_build/default/validate/verify_certificate.exe'

    def rows(self, packet):
        with tempfile.TemporaryDirectory(prefix='r6-015-rows-') as tmp:
            tmp = Path(tmp); r6.write_json(tmp/'ir.json', packet['input_ir'])
            subprocess.run([str(self.driver), 'prepare', str(tmp/'ir.json'), str(tmp/'prepared.json')], check=True, capture_output=True)
            prepared = r6.read_json(tmp/'prepared.json')
        if prepared['final_ir'] != packet['final_ir']: raise SystemExit('derived final IR differs from the packet')
        return prepared['rows']

    def checker(self, packet):
        with tempfile.TemporaryDirectory(prefix='r6-015-check-') as tmp:
            tmp = Path(tmp); r6.write_json(tmp/'evidence.json', packet)
            subprocess.run([str(self.verifier), str(tmp/'evidence.json'), str(tmp/'verdict.json')], capture_output=True)
            return r6.read_json(tmp/'verdict.json')


def labelled(tools, rows, packet, es):
    mutated = replay_episode.mutated(packet, es)
    a = arithmetic(rows, es); c = tools.checker(mutated)
    if a['valid'] != (c['accepted'] is True):
        raise SystemExit(f"the labels disagree: arithmetic {a} against checker {c}")
    return {'coefficients': es, 'arithmetic': a, 'checker': {k: c.get(k) for k in ('accepted', 'stage', 'reason', 'error')}, 'valid': a['valid']}


def mutation_set(tools, site, rows, packet):
    retained = entries(packet); m = coefficient_map(retained)
    names = sorted(k for k in m if k != 'neg_goal'); relation = {r['name']: r['relation'] for r in rows}
    outside = sorted(r['name'] for r in rows if r['name'] not in m and r['name'] != 'neg_goal')
    def entry_list(mm): return [{'hypothesis': k, 'coefficient': str(v)} for k, v in mm.items()]
    def first(candidates, build):
        for name in candidates:
            es = build(name); lab = labelled(tools, rows, packet, es)
            if not lab['valid']: return {'chosen': name, **lab}
        return {'not_applicable': 'no candidate makes the arithmetic invalid'}
    out = {'invalid': {}, 'valid': {}}
    out['invalid']['neg_goal_doubled'] = {'chosen': 'neg_goal', **labelled(tools, rows, packet,
        entry_list({**m, 'neg_goal': m['neg_goal']*2}))}
    out['invalid']['inequality_doubled'] = first([n for n in names if relation.get(n) in INEQUALITY],
                                                 lambda n: entry_list({**m, n: m[n]*2}))
    out['invalid']['hypothesis_dropped'] = first(names, lambda n: entry_list({k: v for k, v in m.items() if k != n}))
    out['invalid']['unrelated_inequality_added'] = first([n for n in outside if relation.get(n) in INEQUALITY],
                                                         lambda n: entry_list({**m, n: Fraction(1)}))
    out['valid']['scaled_2'] = labelled(tools, rows, packet, entry_list({k: v*2 for k, v in m.items()}))
    out['valid']['scaled_3'] = labelled(tools, rows, packet, entry_list({k: v*3 for k, v in m.items()}))
    reordered = list(reversed(retained))
    if reordered == retained: reordered = retained[1:] + retained[:1]
    out['valid']['reordered'] = labelled(tools, rows, packet, reordered)
    out['valid']['zero_entry_added'] = ({'chosen': outside[0], **labelled(tools, rows, packet, retained + [{'hypothesis': outside[0], 'coefficient': '0'}])}
                                        if outside else {'not_applicable': 'no row outside the map'})
    for kind, expected in (('invalid', False), ('valid', True)):
        for name, lab in out[kind].items():
            if 'not_applicable' not in lab and lab['valid'] is not expected: raise SystemExit(f'{site} {name}: labelled {lab["valid"]}')
    return out


def spec(id_, site, src, coefficients=None, inject=False):
    s = {'id': id_, 'site': f'bracket-{site}', 'source': src, 'coefficients': coefficients, 'inject_unverified': inject,
         'route': 'constrained'}
    replay_lock.check_spec(s)
    return s


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--record', required=True); p.add_argument('--plan', required=True)
    args = p.parse_args()
    record_path, plan_path = Path(args.record), Path(args.plan)
    for path in (record_path, plan_path):
        if path.exists(): raise SystemExit(f'refusing to overwrite {path}')
    qualification_audit.verify_live_evaluation()
    tools = Tools(); audit = r6.read_json(AUDIT)['slots']
    record = {'schema_version': 'r6-015-mutations-1', 'rules': 'mutations.py docstring', 'sources': {}, 'units': {}, 'maps': {},
              'mutations': {}, 'control_5': [], 'control_4': [], 'episodes': {}}
    plan = []

    def load(site, src):
        packet = packet_of(src); rows = tools.rows(packet)
        if src['arm'] == 'learned' and rows != r6.read_json(R6/src['run']/'prepared.json')['rows']: raise SystemExit('rows differ from prepared.json')
        es = entries(packet); lab = labelled(tools, rows, packet, es)
        record['sources'][src['run']] = {'site': site, 'arm': src['arm'], 'ordering': [[e['hypothesis'], e['coefficient']] for e in es],
                                         'map': show(coefficient_map(es)), 'class': show(class_of(coefficient_map(es))),
                                         'arithmetic': lab['arithmetic'], 'checker': lab['checker']}
        return packet, rows, es

    # the four obligations: 32 learned and 4 deterministic certificates, replayed as retained
    reps = {}
    for site in TARGETS:
        for draw in range(1, 9):
            src = source(site, 'learned', draw); packet, rows, es = load(site, src)
            if not record['sources'][src['run']]['arithmetic']['valid']: raise SystemExit(f'{src["run"]}: a retained certificate is invalid')
            key = json.dumps(show(coefficient_map(es)), sort_keys=True); reps.setdefault((site, key), (src, packet, rows))
            plan.append(spec(f'{site}-learned-draw{draw}', site, src))
        src = source(site, 'deterministic'); packet, rows, es = load(site, src)
        if not record['sources'][src['run']]['arithmetic']['valid']: raise SystemExit(f'{src["run"]}: a retained certificate is invalid')
        key = json.dumps(show(coefficient_map(es)), sort_keys=True); reps.setdefault((site, key), (src, packet, rows))
        plan.append(spec(f'{site}-deterministic', site, src))
    learned = [s for s in record['sources'].values() if s['arm'] == 'learned' and s['site'] in TARGETS]
    both = [s for s in record['sources'].values() if s['site'] in TARGETS]
    units = {'learned': {'orderings': len({json.dumps([s['site'], s['ordering']]) for s in learned}),
                         'maps': len({json.dumps([s['site'], s['map']], sort_keys=True) for s in learned}),
                         'classes': len({json.dumps([s['site'], s['class']], sort_keys=True) for s in learned})},
             'both': {'maps': len({json.dumps([s['site'], s['map']], sort_keys=True) for s in both}),
                      'classes': len({json.dumps([s['site'], s['class']], sort_keys=True) for s in both})}}
    record['units'] = units
    if units != PROPOSAL_COUNTS: raise SystemExit(f'units differ from the proposal: {units}')

    # controls 1 and 2: the mutation sets of the six maps
    for (site, key), (src, packet, rows) in sorted(reps.items(), key=lambda kv: (kv[0][0], kv[1][0]['arm'])):
        tag = f"{site}-{src['arm']}"
        record['maps'][tag] = {'site': site, 'representative': src['run'], 'map': json.loads(key)}
        muts = mutation_set(tools, site, rows, packet); record['mutations'][tag] = muts
        for name, lab in muts['invalid'].items():
            if 'not_applicable' not in lab: plan.append(spec(f'{tag}-{name}', site, src, lab['coefficients'], inject=True))
        for name, lab in muts['valid'].items():
            if 'not_applicable' not in lab: plan.append(spec(f'{tag}-{name}', site, src, lab['coefficients']))
    l166 = {k: v for k, v in record['maps'].items() if v['site'] == 'l166'}
    det = reps[next(k for k in reps if k[0] == 'l166' and reps[k][0]['arm'] == 'deterministic')]
    dropped = [e for e in entries(det[1]) if e['hypothesis'] != 'hrec']
    lab = labelled(tools, det[2], det[1], dropped)
    if not lab['valid'] or show(coefficient_map(dropped)) != l166['l166-learned']['map']: raise SystemExit('l166: hrec dropped is not the learned map')
    record['mutations']['l166-deterministic']['valid']['hrec_dropped'] = {'chosen': 'hrec', **lab, 'equals_learned_map': True}
    plan.append(spec('l166-deterministic-hrec_dropped', 'l166', det[0], dropped))

    # control 5: every distinct (source, map) of the six proved obligations
    for site in PROVED:
        seen = {}
        for draw in range(1, 9):
            src = source(site, 'learned', draw); packet, rows, es = load(site, src)
            key = json.dumps(show(coefficient_map(es)), sort_keys=True); seen.setdefault(key, []).append(draw)
        learned_maps = dict(seen)
        for key, draws in learned_maps.items():
            src = source(site, 'learned', draws[0]); slots = {f'bracket-{site}/{d}': audit[f'bracket-{site}/{d}']['audit']['local']['classification'] for d in draws}
            label = expectation(site, draws, slots)
            record['control_5'].append({'site': site, 'source': src, 'map': json.loads(key), 'draws': draws, 'audited_slots': slots, 'expectation': label})
            plan.append(spec(f'{site}-control5-learned-draw{draws[0]}', site, src))
        src = source(site, 'deterministic')
        absent = deterministic_absence(src)
        if absent is not None:
            record['control_5'].append({'site': site, 'source': src, 'retained': False, 'reason': absent}); continue
        packet, rows, es = load(site, src)
        key = json.dumps(show(coefficient_map(es)), sort_keys=True)
        match = learned_maps.get(key)
        if match:
            slots = {f'bracket-{site}/{d}': audit[f'bracket-{site}/{d}']['audit']['local']['classification'] for d in match}
            label = expectation(site, match, slots)
        else:
            slots, label = {}, 'no_expectation: not identical to an audited learned map'
        record['control_5'].append({'site': site, 'source': src, 'map': json.loads(key), 'identical_to_learned_draws': match or [],
                                    'audited_slots': slots, 'expectation': label})
        plan.append(spec(f'{site}-control5-deterministic', site, src))

    # control 4: l170's retained proposals, checked; the first also injected
    for draw in range(1, 9):
        src = source('l170', 'learned', draw); packet = packet_of(src); rows = tools.rows(packet)
        lab = labelled(tools, rows, packet, entries(packet))
        if lab['valid']: raise SystemExit(f'l170 draw {draw}: a retained proposal is valid')
        record['control_4'].append({'source': src, 'ordering': [[e['hypothesis'], e['coefficient']] for e in entries(packet)],
                                    'arithmetic': lab['arithmetic'], 'checker': lab['checker']})
        plan.append(spec(f'l170-learned-draw{draw}', 'l170', src))
    plan.append(spec('l170-learned-draw1-injected', 'l170', source('l170', 'learned', 1), None, inject=True))

    for s in plan: record['episodes'][s['id']] = frozen_expectation(s)
    tied(record, plan)
    qualification_audit.verify_live_evaluation()
    plan_path.write_text(json.dumps({'schema_version': 'r6-015-plan-1', 'episodes': plan}, indent=1) + '\n')
    record['plan_sha256'] = r6.sha(plan_path)
    record['tools_sha256'] = {'proposal_driver': r6.sha(tools.driver), 'verify_certificate': r6.sha(tools.verifier)}
    record['sources_sha256'] = {str(f.relative_to(R6)): r6.sha(f) for f in (Path(__file__).resolve(), HERE/'replay_episode.py', HERE/'replay_lock.py')}
    record_path.write_text(json.dumps(record, indent=1) + '\n')
    print(json.dumps({'episodes': len(plan), 'units': units}, indent=1))


def deterministic_absence(src):
    """`None` if the deterministic run retained a certificate. Absence is recorded only when its sealed, chain-verified events show
    exactly one dispatch, received with no certificate; a seal, chain or decoding failure propagates."""
    rows = events.read(replay_episode.sealed(R6/src['run'], 'events.ndjson'))
    child = [(r['event'], r['payload']['data']) for r in rows if r['source'] == 'child_report' and r['stage'] == 'search']
    started = [d for e, d in child if e == 'dispatch_started']; received = [d for e, d in child if e == 'dispatch_received']
    if len(started) == 1 and len(received) == 1 and 'certificate' in received[0] and received[0]['certificate'] is None:
        return 'one dispatch, received with no certificate (sealed, chain-verified events)'
    return None


def map_of(src):
    return show(coefficient_map(entries(packet_of(src))))


def tied(record, plan):
    """Regression checks: every reported map is its packet's, every match and non-match is recomputed from the packets, and
    control 5 covers exactly what R6-014 retained."""
    for tag, m in record['maps'].items():
        if map_of({'arm': tag.split('-')[1], 'run': m['representative']}) != m['map']: raise SystemExit(f'{tag}: map is not its packet\'s')
    for run, s in record['sources'].items():
        if map_of({'arm': s['arm'], 'run': run}) != s['map']: raise SystemExit(f'{run}: map is not its packet\'s')
    analysis = r6.read_json(R6/'reviews/2026-09-29/R6-014-BLOCK2-ANALYSIS.json')
    proofs = {s.removeprefix('bracket-') for s in analysis['arms']['deterministic']['proofs']}
    retained, absent, learned_draws = set(), set(), Counter()
    for c in record['control_5']:
        site = c['site']
        if c['source']['arm'] == 'learned':
            if map_of(c['source']) != c['map']: raise SystemExit(f'{site}: control-5 map is not its packet\'s')
            for d in c['draws']:
                learned_draws[site] += 1
                if map_of(source(site, 'learned', d)) != c['map']: raise SystemExit(f'{site} draw {d}: not this map')
        elif c.get('retained') is False:
            absent.add(site)
        else:
            retained.add(site)
            if map_of(c['source']) != c['map']: raise SystemExit(f'{site}: deterministic control-5 map is not its packet\'s')
            for d in range(1, 9):
                same = map_of(source(site, 'learned', d)) == c['map']
                if same != (d in c['identical_to_learned_draws']): raise SystemExit(f'{site}: the deterministic match is wrong at draw {d}')
    if retained != proofs or absent != set(PROVED) - proofs: raise SystemExit(f'control-5 coverage: retained {retained}, absent {absent}')
    if any(learned_draws[s] != 8 for s in PROVED): raise SystemExit(f'control-5 learned coverage: {dict(learned_draws)}')
    episodes = [s for s in plan if '-control5-' in s['id']]
    if len(episodes) != sum(1 for c in record['control_5'] if c.get('retained') is not False): raise SystemExit('control-5 plan coverage')


def expectation(site, draws, slots):
    """Revision 5's control-5 expectation labels."""
    if site in ('l096', 'l099'): return 'no_expectation: not classified by the audit'
    if site == 'l070' and 5 in draws: return 'no_fixed_prediction: sufficiency not established (draw 5)'
    if all(c in ('certificate_alone', 'sufficient_but_context_referenced') for c in slots.values()): return 'expected_pass'
    return 'no_expectation'


def frozen_expectation(s):
    """The frozen expectation of each episode; `None` where the episode is the measurement."""
    i = s['id']
    if '-control5-' in i: return 'control_5: see control_5 labels'
    if i == 'l170-learned-draw1-injected': return 'control_4: not proved (the closer fails)'
    if i.startswith('l170-'): return 'control_4: certificate_rejected'
    if s['coefficients'] is None: return None
    return 'control_1: certificate rejected by the checker, and not proved (the closer fails)' if s['inject_unverified'] \
        else 'control_2: proved, with the constrained receipt and kernel acceptance'


if __name__ == '__main__':
    main()
