#!/usr/bin/env python3
"""R6-014 controls for the frozen analysis (`analysis_r6.py`) on canned inputs: all-success, all-failure, mixed, missing and unknown
responses, rescaled and duplicate witnesses, a partial collection, costs, the negative control's false acceptance and integrity stop,
operational pauses, and malformed or incomplete populations, each with exact expected tables. No live evidence exists or is read."""
import argparse
import copy
from pathlib import Path

import analysis_r6 as analysis
import run as r6
from test_proposals import Suite, require

CASES = '''populations_exact all_success all_failure mixed_dispositions missing_and_unknown rescaled_and_duplicate_witnesses partial_collection
costs_priced_at_frozen_rates negative_control_false_acceptance_stops operational_pause_rules malformed_inputs_refused deterministic_arm_tabled'''.split()
CLASSIFICATION = r6.read_json(r6.ROOT/'census-runs/representability-v4/representability.json')
DETERMINISTIC = r6.read_json(r6.ROOT/'census-runs/deterministic-v1/deterministic.json')
POPS = analysis.populations(CLASSIFICATION)
RATES = {'input': 2500, 'cached_input': 250, 'output': 15000}
PLANNED = {s: 8 for s in POPS['posed']}; BLOCK1 = {s: 1 for s in POPS['posed']}; SLOT_MONEY = 102400


def certificate(site, scale=1):
    record = next(r for r in CLASSIFICATION['results'] if r['site_id'] == site)
    return [{'hypothesis': c['hypothesis'], 'coefficient': str(int(c['coefficient'])*scale)} for c in record.get('certificate') or []] or \
           [{'hypothesis': 'neg_goal', 'coefficient': '1'}]


def slot(site, draw=1, disposition='send_grant', response=True, present=True, coefficients=None, verified=True, consumed=True, local=True, whole=True,
         axioms=True, closer='term_mode_nat', refusal=None, audit=True, publication='pending', attempts=0, usage=True, failure=None):
    return {'task_id': site, 'draw': draw,
            'ledger': {'disposition': disposition, 'presend_attempts': attempts, 'maximum_presend_attempts': 3, 'reserved_micro_usd': SLOT_MONEY},
            'transport': {'response_received': response, 'failure_category': failure},
            'witness': {'present': present, 'coefficients': coefficients if coefficients is not None else certificate(site)},
            'verification': {'accepted': verified}, 'reconstruction': {'attempted': consumed is not None, 'closer': closer, 'consumed': consumed, 'refusal': refusal},
            'kernel': {'local': local, 'whole': whole, 'axioms_clean': axioms},
            'usage': {'input_tokens': 4000, 'output_tokens': 300, 'cached_tokens': 1000} if usage else {'input_tokens': None, 'output_tokens': None, 'cached_tokens': None},
            'audit': {'accepted': audit, 'publication': publication}}


def realistic(site, draw=1):
    """What a correct proposer's slot would look like at each stratum."""
    if site == analysis.NEGATIVE_CONTROL: return slot(site, draw, verified=False, consumed=None, local=None, whole=None, axioms=None, closer=None)
    if site in analysis.CLOSER_UNREACHABLE: return slot(site, draw, consumed=False, local=None, whole=None, axioms=None, refusal='nat_closer_int_goal')
    return slot(site, draw)


def collection(slots, schedule=BLOCK1):
    consumed = sorted(k for k, s in slots.items() if s['ledger']['disposition'] in ('send_grant', 'unknown'))
    return {'schema_version': 'r6-analysis-input-1', 'slots': slots,
            'campaign': {'authorized_schedule': schedule, 'planned_schedule': PLANNED, 'authorized_micro_usd': SLOT_MONEY*sum(schedule.values()),
                         'ledger': {'consumed_slots': consumed, 'transmissions_consumed': len(consumed), 'committed_micro_usd': SLOT_MONEY*len(consumed)}}}


def run(slots, schedule=BLOCK1):
    return analysis.analyse(collection(slots, schedule), DETERMINISTIC, CLASSIFICATION, RATES)


def stage(result, name, stratum=None):
    table = result['strata'][stratum] if stratum else result['arms']['learned']['slots']
    return table['stages_over_sent'][name]


def controls(output):
    suite = Suite(output, CASES)

    def pops():
        r = run({f'{s}/1': realistic(s) for s in POPS['posed']})
        require(r['denominators'] == {'primary': 15, 'posed': 11, 'certificate_feasible': 10, 'negative_control': 1, 'closer_reachable': 6, 'closer_unreachable': 4})
        require(r['populations']['not_posed'] == ['bracket-l098', 'bracket-l101', 'bracket-l158', 'bracket-l180'])
        return r['denominators']
    suite.case('populations_exact', pops)

    def success():
        r = run({f'{s}/1': realistic(s) for s in POPS['posed']})
        require(stage(r, 'returned') == {'true': 11, 'false': 0, 'unobserved': 0} and stage(r, 'verified') == {'true': 10, 'false': 1, 'unobserved': 0})
        require(stage(r, 'consumed') == {'true': 6, 'false': 4, 'unobserved': 1} and stage(r, 'whole') == {'true': 6, 'false': 0, 'unobserved': 5})
        require(stage(r, 'axioms', 'closer_reachable') == {'true': 6, 'false': 0, 'unobserved': 0} and stage(r, 'consumed', 'closer_unreachable') == {'true': 0, 'false': 4, 'unobserved': 0})
        require(r['integrity_stop'] is False and r['operational_pause'] == [] and r['continue_permitted'] is True and r['collection']['partial'] is False)
        return {'whole_validated': 6}
    suite.case('all_success', success)

    def failure():
        r = run({f'{s}/1': slot(s, present=False, coefficients=[], verified=None, consumed=None, local=None, whole=None, axioms=None) for s in POPS['posed']})
        require(stage(r, 'returned') == {'true': 0, 'false': 11, 'unobserved': 0} and stage(r, 'verified') == {'true': 0, 'false': 0, 'unobserved': 11})
        require(r['integrity_stop'] is False and r['continue_permitted'] is True, 'failure to propose is not an operational fault')
        return {'returned': 0}
    suite.case('all_failure', failure)

    def mixed():
        s = POPS['posed']; slots = {f'{x}/1': realistic(x) for x in s}
        slots[f'{s[0]}/1'] = slot(s[0], disposition='release', response=None, present=None, verified=None, consumed=None, local=None, whole=None, axioms=None, attempts=1, usage=False)
        slots[f'{s[1]}/1'] = slot(s[1], disposition='release', response=None, present=None, verified=None, consumed=None, local=None, whole=None, axioms=None, attempts=3, usage=False)
        slots[f'{s[2]}/1'] = slot(s[2], verified=False, consumed=None, local=None, whole=None, axioms=None)
        r = run(slots); d = r['arms']['learned']['slots']['dispositions']
        require(d == {'sent_with_response': 9, 'unknown_or_partial_send': 0, 'pre_send_released': 1, 'exhausted': 1, 'refused_before_reservation': 0}, str(d))
        require('exhausted_slot' in r['operational_pause'] and r['continue_permitted'] is False)
        return d
    suite.case('mixed_dispositions', mixed)

    def missing():
        s = POPS['posed']; slots = {f'{x}/1': realistic(x) for x in s}
        slots[f'{s[0]}/1'] = slot(s[0], disposition='unknown', response=None, present=None, verified=None, consumed=None, local=None, whole=None, axioms=None, usage=False)
        slots[f'{s[3]}/1'] = slot(s[3], disposition='send_grant', response=True, verified=True, consumed=True, local=None, whole=None, axioms=None)  # replay unobserved
        r = run(slots)
        require(r['arms']['learned']['slots']['dispositions']['unknown_or_partial_send'] == 1 and r['per_slot'][f'{s[0]}/1']['returned'] is None)
        require(stage(r, 'local') == {'true': 4, 'false': 0, 'unobserved': 6}, str(stage(r, 'local')))  # l069 unknown; l078 replay unobserved; l170 and the unreachable four stop earlier
        require('unknown_or_partial_send' in r['operational_pause'])
        return {'unknown': 1, 'unobserved_local': 6}
    suite.case('missing_and_unknown', missing)

    def rescaled():
        site = 'bracket-l069'
        slots = {f'{x}/1': realistic(x) for x in POPS['posed']}; slots[f'{site}/2'] = slot(site, 2, coefficients=certificate(site, 3))
        r = run(slots, {**BLOCK1, site: 2})
        row = r['arms']['learned']['by_site'][site]
        require(row['distinct_witnesses'] == 1 and row['matches_classification_certificate'] == 2, str(row))
        require(analysis.primitive(certificate(site, 3)) == analysis.primitive(certificate(site)) and analysis.primitive([{'hypothesis': 'a', 'coefficient': 'x'}]) is None)
        require(sorted(r['prefixes']) == ['draws_1_to_1', 'draws_1_to_2'] and r['prefixes']['draws_1_to_1']['slots'] == 11 and r['prefixes']['draws_1_to_2']['slots'] == 12)
        return row
    suite.case('rescaled_and_duplicate_witnesses', rescaled)

    def partial():
        s = POPS['posed']; r = run({f'{x}/1': realistic(x) for x in s[:5]})
        require(r['collection']['partial'] is True and r['collection']['collected_slots'] == 5 and len(r['collection']['authorized_not_collected']) == 6)
        require(r['collection']['planned_slots'] == 88 and r['collection']['planned_beyond_authorization'] == 77)
        return r['collection']
    suite.case('partial_collection', partial)

    def costs():
        r = run({f'{s}/1': realistic(s) for s in POPS['posed']}); c = r['costs']
        require(c['reserved_micro_usd'] == 11*SLOT_MONEY == 1126400 and c['authorized_micro_usd'] == 1126400)
        require(c['provider_reported_tokens'] == {'input_tokens': 44000, 'output_tokens': 3300, 'cached_tokens': 11000})
        require(c['priced_ceiling_micro_usd'] == ((44000-11000)*2500 + 11000*250 + 3300*15000)//1000, str(c))
        return c
    suite.case('costs_priced_at_frozen_rates', costs)

    def negative():
        slots = {f'{s}/1': realistic(s) for s in POPS['posed']}
        slots[f'{analysis.NEGATIVE_CONTROL}/1'] = slot(analysis.NEGATIVE_CONTROL, verified=True, consumed=None, local=None, whole=None, axioms=None)
        r = run(slots)
        require(r['integrity_stop'] is True and r['continue_permitted'] is False and r['negative_control']['false_certificate_acceptances'] == [f'{analysis.NEGATIVE_CONTROL}/1'])
        rejected = run({f'{s}/1': realistic(s) for s in POPS['posed']})
        require(rejected['integrity_stop'] is False, 'a correctly rejected proposal is not a false acceptance')
        return r['negative_control']
    suite.case('negative_control_false_acceptance_stops', negative)

    def pauses():
        out = {}
        for label, change in (('audit_rejected', {'audit': {'accepted': False, 'publication': 'pending'}}), ('publication_failed', {'audit': {'accepted': True, 'publication': 'rejected'}}),
                              ('transport_binding_failure', {'transport': {'response_received': True, 'failure_category': 'transport_binding_failure'}})):
            slots = {f'{s}/1': realistic(s) for s in POPS['posed']}; first = f"{POPS['posed'][0]}/1"; slots[first] = {**slots[first], **change}
            r = run(slots); require(label in r['operational_pause'] and r['continue_permitted'] is False, label); out[label] = r['operational_pause']
        data = collection({f'{s}/1': realistic(s) for s in POPS['posed']}); data['campaign']['authorized_micro_usd'] = SLOT_MONEY*10
        r = analysis.analyse(data, DETERMINISTIC, CLASSIFICATION, RATES); require('money_above_authorized' in r['operational_pause']); out['money'] = r['operational_pause']
        return out
    suite.case('operational_pause_rules', pauses)

    def malformed():
        out = {}
        def refused(label, data, classification=CLASSIFICATION):
            try: analysis.analyse(data, DETERMINISTIC, classification, RATES)
            except analysis.Malformed as error: out[label] = str(error); return
            raise AssertionError(label+': accepted')
        base = lambda: collection({f'{s}/1': realistic(s) for s in POPS['posed']})
        d = base(); d['slots']['bracket-l069/2'] = slot('bracket-l069', 2); refused('outside_schedule', d)
        d = base(); d['slots']['bracket-l098/1'] = slot('bracket-l098'); refused('site_not_posed', d)
        d = base(); d['campaign']['ledger']['transmissions_consumed'] = 10; refused('transmission_count', d)
        d = base(); d['campaign']['ledger']['consumed_slots'] = d['campaign']['ledger']['consumed_slots'][1:]; refused('ledger_consumption', d)
        d = base(); d['campaign']['ledger']['committed_micro_usd'] -= 1; refused('committed_money', d)
        d = base(); del d['slots']['bracket-l069/1']['kernel']['whole']; refused('missing_field', d)
        d = base(); d['schema_version'] = 'other'; refused('schema', d)
        d = base(); d['campaign']['authorized_schedule'] = {**BLOCK1, 'bracket-l069': 9}; refused('schedule_beyond_plan', d)
        c = copy.deepcopy(CLASSIFICATION); c['results'] = c['results'][:-1]; refused('population_incomplete', base(), c)
        c = copy.deepcopy(CLASSIFICATION); c['classes']['posable_negative_control'] = []; refused('negative_control_missing', base(), c)
        return out
    suite.case('malformed_inputs_refused', malformed)

    def deterministic():
        r = run({f'{s}/1': realistic(s) for s in POPS['posed']}); arm = r['arms']['deterministic']
        require(sorted(arm['by_site']) == POPS['primary'] and arm['proofs'] == sorted(s for s, o in arm['by_site'].items() if o == 'proof'))
        require(r['arms']['deterministic_reference']['status'] == 'reference, never pooled')
        return {'proofs': arm['proofs'], 'outcomes': arm['by_site']}
    suite.case('deterministic_arm_tabled', deterministic)
    suite.finish()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    controls(args.output)


if __name__ == '__main__':
    main()
