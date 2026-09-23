"""R6-014 frozen executable analysis for the census cohort: the learned arm's collected slots, beside the deterministic arm. Read-only.

Frozen before any provider call (`LOCK`); its definitions are the R6-014 decision's and do not change after outputs are seen.

Input (`r6-analysis-input-1`, emitted per slot by the reviewed live auditor, or constructed for the canned controls):
* `campaign`: the authorized schedule, the planned design, the ledger state (slots consumed/released, transmissions, committed money);
* `slots`: one record per attempted (site, draw), every fact observed or `None` (unobserved, never counted as failure);
* `deterministic`: the deterministic arm's frozen summary; `classification`: the fifteen-site representability record.

Definitions (each a separate column; audit/publication status is separate from mathematical success):
* witness **returned** (a schema-valid response) → **verified** (the independent certificate checker accepted it) → **consumed** (the
  closer's own receipt) → **local** closure → **whole** declaration validated → **axioms** unchanged. A stage is counted only over slots
  where the previous stage is observed true; unobserved stages are reported as unobserved.
* slot dispositions: pre-send releases (with attempt counts), exhausted slots (the pre-send limit reached), unknown or partial sends
  (consumed, outcome unknown), sent with a response, and planned-but-not-collected (reported, never evidence).
* witnesses are compared up to positive scaling (the primitive integer vector over row names): duplicates across draws and agreement
  with the classification's certificate are reported; a rescaled witness is the same witness.
* the negative control (l170): a **false certificate acceptance** is any verifier or consumer acceptance of a Farkas contradiction for its
  satisfiable emitted rows. A correctly rejected proposal is not one; a proof of the original obligation by another route is not one. A
  false acceptance is an **integrity stop**: collection stops and further blocks need review.
* operational pause, independent of proof success and witness novelty: any unknown/partial send, any audit rejection, any publication
  failure, any transport-binding failure, any exhausted slot, or committed money above the authorized limit pauses collection.
* costs: reserved money per slot and total (a reservation, not a bill); provider-reported usage including cached input tokens, priced at
  the frozen rates as a ceiling estimate.
* populations: 15 primary / 11 posed / 10 certificate-feasible / 1 negative control / 6 closer-reachable / 4 closer-unreachable; exposure
  sensitivities (excluding l070; excluding the `lift_cell` family) and declaration-family grouping; prefix tables by draw index.
Any population or denominator inconsistency refuses the whole input (`Malformed`).

Revision 2 (R6-014 review, findings 5-7; lock `analysis-v2`):
* populations are bound to their exact reviewed membership (`REVIEWED`), unique, and partitioned; the classification must reproduce it,
  and schedules may select within the posed sites but never redefine membership;
* the integrity predicate and every stage observation are read raw, before the conditional stage tables censor them. An observation
  past a stage not observed true, or on a slot that was not sent with a response, is a **contradictory observation**: it is reported and
  pauses collection. On the negative control, any raw verifier, consumer or kernel acceptance is a false acceptance and an integrity stop;
* usage is kept per field and per slot; unknown usage is never zero. A slot's cost ceiling needs its input and output counts (unknown cached
  input is bounded by pricing all input uncached). The campaign ceiling exists only when every consumed slot is priced; otherwise the known
  subtotal and its coverage are reported. Money is exact in nano-USD, and a micro-USD ceiling rounds up;
* proposal diversity (every returned vector) is reported apart from verified-witness diversity.
"""
import argparse
import json
from math import gcd
from pathlib import Path

import run as r6

LOCK = r6.ROOT/'policies/analysis-v2.sha256.json'
FILES = ('analysis_r6.py', 'test_analysis_r6.py')
PRIMARY = 15
NEGATIVE_CONTROL = 'bracket-l170'
CLOSER_UNREACHABLE = ('bracket-l166', 'bracket-l175', 'bracket-l178', 'bracket-l204')  # R6-013 outcome decision, predeclared
# Revision 2: the reviewed membership (representability v4, R6-013), exact. The classification must reproduce it; nothing supplied redefines it.
REVIEWED = {'primary': ('bracket-l069', 'bracket-l070', 'bracket-l071', 'bracket-l078', 'bracket-l096', 'bracket-l098', 'bracket-l099', 'bracket-l101',
                        'bracket-l158', 'bracket-l166', 'bracket-l170', 'bracket-l175', 'bracket-l178', 'bracket-l180', 'bracket-l204'),
            'certificate_feasible': ('bracket-l069', 'bracket-l070', 'bracket-l071', 'bracket-l078', 'bracket-l096', 'bracket-l099', 'bracket-l166',
                                     'bracket-l175', 'bracket-l178', 'bracket-l204'),
            'negative_control': ('bracket-l170',), 'not_posed': ('bracket-l098', 'bracket-l101', 'bracket-l158', 'bracket-l180')}
EXPOSURE_SENSITIVITIES = {'excluding_l070': lambda site, family: site != 'bracket-l070',
                          'excluding_lift_cell': lambda site, family: family != 'Bracket.lift_cell'}
LADDER = ('returned', 'verified', 'consumed', 'local', 'whole', 'axioms')
DISPOSITIONS = ('sent_with_response', 'unknown_or_partial_send', 'pre_send_released', 'exhausted', 'refused_before_reservation')


class Malformed(ValueError):
    pass


def check(condition, message):
    if not condition: raise Malformed(message)


def verify_lock():
    lock = json.loads(LOCK.read_bytes())
    if set(lock) != set(FILES) or any(r6.sha(r6.ROOT/p) != h for p, h in lock.items()): raise ValueError('analysis requires its frozen sources')


def primitive(coefficients):
    """A Farkas witness up to positive scaling: {name: integer} divided by the gcd; zero entries dropped; None if not a witness vector."""
    try: values = {c['hypothesis']: int(c['coefficient']) for c in coefficients}
    except (KeyError, TypeError, ValueError): return None
    values = {k: v for k, v in values.items() if v != 0}
    if not values: return None
    g = 0
    for v in values.values(): g = gcd(g, abs(v))
    return tuple(sorted((k, v//g) for k, v in values.items()))


def populations(classification):
    classes = classification['classes']; ids = [r['site_id'] for r in classification['results']]; results = {r['site_id']: r for r in classification['results']}
    check(len(ids) == len(set(ids)), 'duplicate site in the classification')
    primary = sorted(results); check(len(primary) == PRIMARY, f'primary population is {len(primary)}, not {PRIMARY}')
    feasible = sorted(classes['posable_certificate']); negative = sorted(classes['posable_negative_control'])
    check(negative == [NEGATIVE_CONTROL], 'the negative control is not l170')
    check(all(s in feasible for s in CLOSER_UNREACHABLE), 'the closer-unreachable stratum is not certificate-feasible')
    posed = sorted(feasible+negative)
    unposed = sorted(s for k, v in classes.items() if k not in ('posable_certificate', 'posable_negative_control') for s in v)
    check(len(feasible) == len(set(feasible)) and not set(feasible) & set(negative) and sorted(posed+unposed) == primary,
          'the classes do not partition the primary population')
    check(tuple(primary) == REVIEWED['primary'] and tuple(feasible) == REVIEWED['certificate_feasible'] and tuple(negative) == REVIEWED['negative_control']
          and tuple(unposed) == REVIEWED['not_posed'], 'the classification does not reproduce the reviewed membership')
    return {'primary': primary, 'posed': posed, 'certificate_feasible': feasible, 'negative_control': negative,
            'closer_reachable': sorted(s for s in feasible if s not in CLOSER_UNREACHABLE), 'closer_unreachable': sorted(CLOSER_UNREACHABLE),
            'not_posed': sorted(set(primary)-set(posed)), 'family': {s: results[s]['family'] for s in primary},
            'certificates': {s: primitive(results[s].get('certificate') or []) for s in feasible}}


def disposition(slot):
    ledger = slot['ledger']
    if ledger['disposition'] is None: return 'refused_before_reservation'
    if ledger['disposition'] == 'unknown': return 'unknown_or_partial_send'
    if ledger['disposition'] == 'release': return 'exhausted' if ledger['presend_attempts'] >= ledger['maximum_presend_attempts'] else 'pre_send_released'
    check(ledger['disposition'] == 'send_grant', 'unknown ledger disposition '+str(ledger['disposition']))
    return 'sent_with_response' if slot['transport']['response_received'] is True else 'unknown_or_partial_send'


def raw_stages(slot):
    return {'returned': slot['witness']['present'], 'verified': slot['verification']['accepted'], 'consumed': slot['reconstruction']['consumed'],
            'local': slot['kernel']['local'], 'whole': slot['kernel']['whole'], 'axioms': slot['kernel']['axioms_clean']}


def ladder(slot):
    """Each stage True/False/None, None past the first stage that is not observed true; and the stages observed past that point (contradictions)."""
    values = raw_stages(slot); out, open_, contradictions = {}, True, []
    for stage in LADDER:
        out[stage] = values[stage] if open_ else None
        if not open_ and values[stage] is not None: contradictions.append(stage)
        if out[stage] is not True: open_ = False
    return out, contradictions


def validate(data, pops):
    check(data.get('schema_version') == 'r6-analysis-input-1', 'input schema')
    campaign = data['campaign']; schedule = campaign['authorized_schedule']; planned = campaign['planned_schedule']
    check(set(schedule) <= set(pops['posed']) and set(planned) == set(pops['posed']), 'schedule sites are not the posed sites')
    check(all(1 <= n <= planned[s] for s, n in schedule.items()), 'authorized schedule exceeds the plan')
    keys = []
    for key, slot in data['slots'].items():
        site, draw = slot['task_id'], slot['draw']
        check(key == f'{site}/{draw}' and site in schedule and 1 <= draw <= schedule[site], f'{key}: outside the authorized schedule')
        for part, fields in (('ledger', ('disposition', 'presend_attempts', 'maximum_presend_attempts', 'reserved_micro_usd')), ('transport', ('response_received',)),
                             ('witness', ('present', 'coefficients')), ('verification', ('accepted',)), ('reconstruction', ('attempted', 'closer', 'consumed', 'refusal')),
                             ('kernel', ('local', 'whole', 'axioms_clean')), ('usage', ('input_tokens', 'output_tokens', 'cached_tokens')), ('audit', ('accepted', 'publication'))):
            check(isinstance(slot.get(part), dict) and set(fields) <= set(slot[part]), f'{key}: {part} fields')
        for field in ('input_tokens', 'output_tokens', 'cached_tokens'):
            value = slot['usage'][field]
            check(value is None or (isinstance(value, int) and not isinstance(value, bool) and value >= 0), f'{key}: usage {field}')
        u = slot['usage']
        check(u['cached_tokens'] is None or u['input_tokens'] is None or u['cached_tokens'] <= u['input_tokens'], f'{key}: cached input exceeds input')
        keys.append(key)
    check(len(keys) == len(set(keys)), 'duplicate slot')
    ledger = campaign['ledger']
    consumed = sorted(k for k, s in data['slots'].items() if s['ledger']['disposition'] in ('send_grant', 'unknown'))
    check(sorted(ledger['consumed_slots']) == consumed, 'ledger consumption differs from the slot records')
    check(ledger['transmissions_consumed'] == len(consumed), 'transmission count differs')
    check(ledger['committed_micro_usd'] == sum(s['ledger']['reserved_micro_usd'] for s in data['slots'].values() if s['ledger']['disposition'] in ('send_grant', 'unknown')),
          'committed money differs from the consumed reservations')


def usage_costs(slots, keys, rates):
    """Per field and per slot over the consumed slots (a pre-send release sent nothing). Unknown stays unknown; nano-USD exact; ceilings round up."""
    consumed = [k for k in keys if slots[k]['ledger']['disposition'] in ('send_grant', 'unknown')]
    fields = {}
    for f in ('input_tokens', 'output_tokens', 'cached_tokens'):
        known = [slots[k]['usage'][f] for k in consumed if slots[k]['usage'][f] is not None]
        fields[f] = {'reported_slots': len(known), 'unreported_slots': len(consumed)-len(known), 'known_total': sum(known)}
    per_slot = {}
    for k in consumed:
        u = slots[k]['usage']
        if rates is None or u['input_tokens'] is None or u['output_tokens'] is None: per_slot[k] = None; continue
        cached = u['cached_tokens'] or 0  # unknown cached input: all input at the uncached rate, which bounds it from above
        per_slot[k] = (u['input_tokens']-cached)*rates['input'] + cached*rates['cached_input'] + u['output_tokens']*rates['output']
    priced = [k for k in consumed if per_slot[k] is not None]; complete = rates is not None and len(priced) == len(consumed)
    subtotal = sum(per_slot[k] for k in priced)
    return {'usage_fields': fields, 'consumed_slots': len(consumed), 'priced_slots': len(priced), 'unpriced_slots': sorted(set(consumed)-set(priced)),
            'known_priced_subtotal_nano_usd': subtotal if rates is not None else None,
            'priced_ceiling_nano_usd': subtotal if complete else None,
            'priced_ceiling_micro_usd': -(-subtotal//1000) if complete else None,
            'cached_unreported_bounded_as_uncached': sorted(k for k in priced if slots[k]['usage']['cached_tokens'] is None),
            'complete': complete}


def analyse(data, deterministic, classification, rates=None):
    pops = populations(classification); validate(data, pops); slots = data['slots']; campaign = data['campaign']
    per_slot = {}
    for key, slot in sorted(slots.items()):
        d = disposition(slot)
        if d == 'sent_with_response': steps, contradictions = ladder(slot)
        else: steps, contradictions = {s: None for s in LADDER}, [s for s, v in raw_stages(slot).items() if v is not None]
        witness = primitive(slot['witness']['coefficients']) if slot['witness']['present'] and slot['witness']['coefficients'] else None
        per_slot[key] = {'site': slot['task_id'], 'draw': slot['draw'], 'disposition': d, **steps, 'witness_primitive': witness, 'contradictions': contradictions,
                         'audit_accepted': slot['audit']['accepted'], 'publication': slot['audit']['publication'],
                         'closer': slot['reconstruction']['closer'], 'refusal': slot['reconstruction']['refusal']}

    def table(selected):
        rows = [per_slot[k] for k in selected]; sent = [r for r in rows if r['disposition'] == 'sent_with_response']
        counts = {d: sum(r['disposition'] == d for r in rows) for d in DISPOSITIONS}
        stages = {}
        for stage in LADDER:
            stages[stage] = {'true': sum(r[stage] is True for r in sent), 'false': sum(r[stage] is False for r in sent), 'unobserved': sum(r[stage] is None for r in sent)}
        return {'slots': len(rows), 'dispositions': counts, 'stages_over_sent': stages, 'sent': len(sent)}

    keys = sorted(per_slot)
    by_site = {}
    for k in keys: by_site.setdefault(per_slot[k]['site'], []).append(k)
    site_table = {s: {**table(ks), 'distinct_proposals': len({per_slot[k]['witness_primitive'] for k in ks if per_slot[k]['witness_primitive']}),
                      'distinct_verified_witnesses': len({per_slot[k]['witness_primitive'] for k in ks if per_slot[k]['witness_primitive'] and per_slot[k]['verified'] is True}),
                      'verified_matching_classification_certificate': sum(per_slot[k]['verified'] is True and per_slot[k]['witness_primitive'] is not None
                                                                          and per_slot[k]['witness_primitive'] == pops['certificates'].get(s) for k in ks),
                      'family': pops['family'][s]} for s, ks in sorted(by_site.items())}
    strata = {name: table([k for k in keys if per_slot[k]['site'] in members])
              for name, members in (('posed', pops['posed']), ('certificate_feasible', pops['certificate_feasible']), ('negative_control', pops['negative_control']),
                                    ('closer_reachable', pops['closer_reachable']), ('closer_unreachable', pops['closer_unreachable']))}
    sensitivities = {name: table([k for k in keys if keep(per_slot[k]['site'], pops['family'][per_slot[k]['site']])]) for name, keep in EXPOSURE_SENSITIVITIES.items()}
    families = {}
    for k in keys: families.setdefault(pops['family'][per_slot[k]['site']], []).append(k)
    prefixes = {f'draws_1_to_{n}': table([k for k in keys if per_slot[k]['draw'] <= n]) for n in range(1, max([per_slot[k]['draw'] for k in keys] or [0])+1)}

    negative = [k for k in keys if per_slot[k]['site'] == NEGATIVE_CONTROL]
    false_acceptance = [k for k in negative if any(raw_stages(slots[k])[stage] is True for stage in ('verified', 'consumed', 'local', 'whole'))]  # raw, before censoring
    contradictory = {k: per_slot[k]['contradictions'] for k in keys if per_slot[k]['contradictions']}
    pause = sorted({reason for k in keys for reason, hit in (
        ('contradictory_observations', bool(per_slot[k]['contradictions'])),
        ('unknown_or_partial_send', per_slot[k]['disposition'] == 'unknown_or_partial_send'), ('exhausted_slot', per_slot[k]['disposition'] == 'exhausted'),
        ('audit_rejected', slots[k]['audit']['accepted'] is False), ('publication_failed', slots[k]['audit']['publication'] == 'rejected'),
        ('transport_binding_failure', slots[k].get('transport', {}).get('failure_category') == 'transport_binding_failure')) if hit})
    if campaign['ledger']['committed_micro_usd'] > campaign['authorized_micro_usd']: pause.append('money_above_authorized')

    costs = usage_costs(slots, keys, rates)
    planned = campaign['planned_schedule']; authorized = campaign['authorized_schedule']
    not_collected = sorted(f'{s}/{d}' for s, n in authorized.items() for d in range(1, n+1) if f'{s}/{d}' not in slots)
    det = deterministic['results']
    arms = {'learned': {'slots': table(keys), 'by_site': site_table},
            'deterministic': {'route': deterministic.get('routes', {}).get('arm') or 'site_cvc4_term_mode_v1',
                              'by_site': {s: r['outcome'] for s, r in sorted(det['site_cvc4_term_mode_v1'].items())},
                              'proofs': sorted(s for s, r in det['site_cvc4_term_mode_v1'].items() if r['outcome'] == 'proof'),
                              'cost_cpu_seconds': round(sum(r['resources']['cpu_seconds'] for r in det['site_cvc4_term_mode_v1'].values()), 3)},
            'deterministic_reference': {'route': 'site_cvc4_default_closer_v1', 'status': 'reference, never pooled',
                                        'by_site': {s: r['outcome'] for s, r in sorted(det['site_cvc4_default_closer_v1'].items())},
                                        'closers': {s: r.get('closer') for s, r in sorted(det['site_cvc4_default_closer_v1'].items())}}}
    check(sorted(arms['deterministic']['by_site']) == pops['primary'], 'the deterministic arm does not cover the fifteen sites')
    return {'schema_version': 'r6-analysis-2', 'populations': {k: v for k, v in pops.items() if k not in ('family', 'certificates')},
            'denominators': {'primary': len(pops['primary']), 'posed': len(pops['posed']), 'certificate_feasible': len(pops['certificate_feasible']),
                             'negative_control': len(pops['negative_control']), 'closer_reachable': len(pops['closer_reachable']), 'closer_unreachable': len(pops['closer_unreachable'])},
            'collection': {'authorized_slots': sum(authorized.values()), 'planned_slots': sum(planned.values()), 'collected_slots': len(keys),
                           'authorized_not_collected': not_collected, 'partial': bool(not_collected),
                           'planned_beyond_authorization': sum(planned.values())-sum(authorized.values()), 'note': 'planned draws are neither evidence nor permission'},
            'arms': arms, 'strata': strata, 'sensitivities': sensitivities, 'families': {f: table(ks) for f, ks in sorted(families.items())}, 'prefixes': prefixes,
            'negative_control': {'slots': len(negative), 'false_certificate_acceptances': false_acceptance,
                                 'definition': 'a verifier or consumer acceptance of a Farkas contradiction for the satisfiable emitted rows, read from the raw observations'},
            'contradictory_observations': contradictory,
            'integrity_stop': bool(false_acceptance), 'operational_pause': pause, 'continue_permitted': not false_acceptance and not pause,
            'costs': {'reserved_micro_usd': campaign['ledger']['committed_micro_usd'], 'authorized_micro_usd': campaign['authorized_micro_usd'], **costs,
                      'scope': 'reservations and provider-reported usage at frozen rates; not a bill'},
            'per_slot': {k: {x: (list(map(list, v)) if x == 'witness_primitive' and v else v) for x, v in r.items()} for k, r in per_slot.items()}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lock', action='store_true', help='freeze this analysis and its controls, once, before any call')
    parser.add_argument('--input', type=Path)
    parser.add_argument('--policy', type=Path, help='the signed cohort policy whose frozen rates price the reported usage')
    parser.add_argument('--deterministic', type=Path, default=r6.ROOT/'census-runs/deterministic-v1/deterministic.json')
    parser.add_argument('--classification', type=Path, default=r6.ROOT/'census-runs/representability-v4/representability.json')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.lock:
        with LOCK.open('x') as f: f.write(json.dumps({p: r6.sha(r6.ROOT/p) for p in FILES}, indent=2)+'\n')
        print(r6.sha(LOCK)); return
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    verify_lock()
    rates = r6.read_json(args.policy)['pricing']['nano_usd_per_token'] if args.policy else None
    result = analyse(r6.read_json(args.input), r6.read_json(args.deterministic), r6.read_json(args.classification), rates)
    r6.write_json(args.output, {**result, 'program_sha256': r6.sha(Path(__file__)), 'input_sha256': r6.sha(args.input)})
    print(json.dumps({k: result[k] for k in ('denominators', 'collection', 'integrity_stop', 'operational_pause', 'continue_permitted')}, indent=1))


if __name__ == '__main__':
    main()
