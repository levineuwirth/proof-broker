#!/usr/bin/env python3
"""R6-010 exposure addendum: what earlier checkpoints actually showed a model, per census site, derived from retained bytes.

The frozen census records one coarse field, `exposure`, whose `model_visible_in` wording is too strong: line 70 was the only
prior *target*, but the rows sent with it carried other hypotheses, and the witnesses returned were generated responses, not
reference answers supplied to the model. This addendum supersedes that field's reading without editing the frozen records.
It is derived, not asserted: every prior provider transmission is read from its retained outbound body; the request inside
the user message is parsed; every request row is joined, by name, to the D1 control's captured local context, and a site is
a *prior input premise* when a captured hypothesis type of a prior request equals that site's captured target exactly. A
site in the family of a prior target is flagged as related. Everything else is `none_recorded`, which means only that no
recorded experiment used or showed it — not unseen mathematics, not an uncontaminated task.

The next protocol consumes this file: its strata and sensitivity sets are the review's population decision
(`R6-010-MEMBERSHIP-REVIEW.json`), recomputed here and required to agree with that record.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import run as r6

CENSUS_DIR = ROOT/'tasks/census-v1'
ADDENDUM = 'exposure-addendum.json'
DECISION = Path(__file__).with_name('R6-010-MEMBERSHIP-REVIEW.json')
# Every provider transmission any earlier checkpoint made. The ledgers and live audits of R6-007 and R6-008 v7 establish that
# these are the only two; both carried the D1 control.
PRIOR_TRANSMISSIONS = ('pilot-runs/live-2', 'campaign-runs-v7/live-1')
D1_CONTEXT = ROOT/'tasks/verinf-d1-70/context/local-context.json'
CLASSES = ('prior_direct_target', 'prior_input_premise_formula', 'prior_target_family', 'none_recorded')


def sha(data): return hashlib.sha256(data).hexdigest()


def prior_transmission(relative):
    """The request the model saw, parsed from the outbound body itself, and what came back."""
    d = ROOT/relative; out = d/'stages/proposal-1/output'
    body_bytes = (out/'outbound-body.json').read_bytes(); body = json.loads(body_bytes)
    system, user = body['input'][0]['content'], body['input'][1]['content']
    request_text = user[user.index('{'):]; request = json.loads(request_text)
    if request_text.encode() != (d/'transport-request.json').read_bytes(): raise ValueError(f'{relative}: outbound request differs from the retained request')
    if 'witness' in request or 'witness' in json.dumps(request['binding']): raise ValueError(f'{relative}: a witness was supplied in the request')
    if sha(system.encode()) != sha((d/'prompt.txt').read_bytes()): raise ValueError(f'{relative}: system message is not the retained instruction')
    returned = json.loads((d/'validated-response.json').read_bytes())['witness']
    return {'run': relative, 'outbound_sha256': sha(body_bytes), 'request_sha256': sha(request_text.encode()),
            'instruction_sha256': sha(system.encode()), 'direct_task': request['binding']['task_id'], 'rows': request['problem']['rows'],
            'reference_witness_supplied': False, 'generated_response_witness': returned}


def derive(census_dir=CENSUS_DIR, decision_path=DECISION):
    census = json.loads((census_dir/'census.json').read_bytes()); membership_bytes = (census_dir/'membership.json').read_bytes()
    decision_bytes = decision_path.read_bytes(); decision = json.loads(decision_bytes)
    targets = {s['site_id']: json.loads((census_dir/s['site_id']/'context/local-context.json').read_bytes())['target'] for s in census['sites']}
    d1 = json.loads(D1_CONTEXT.read_bytes()); hypothesis_type = {e['name']: e['type'] for e in d1['telescope'] if e['kind'] != 'declaration_placeholder'}
    transmissions = [prior_transmission(r) for r in PRIOR_TRANSMISSIONS]
    direct = {'verinf-d1-70': 'bracket-l070'}  # the R6-000 control is census line 70 (same span, same context, same local type)
    sites = {}
    for s in census['sites']:
        sid = s['site_id']; premises = []
        for t in transmissions:
            for row in t['rows']:
                if row['name'] in hypothesis_type and hypothesis_type[row['name']] == targets[sid] and direct.get(t['direct_task']) != sid:
                    premises.append({'run': t['run'], 'outbound_sha256': t['outbound_sha256'], 'row_name': row['name'], 'row': row,
                                     'captured_hypothesis_type': hypothesis_type[row['name']]})
        is_direct = any(direct.get(t['direct_task']) == sid for t in transmissions)
        family = s['declaration'] in {c['declaration'] for c in census['sites'] if any(direct.get(t['direct_task']) == c['site_id'] for t in transmissions)}
        cls = 'prior_direct_target' if is_direct else 'prior_input_premise_formula' if premises else 'prior_target_family' if family else 'none_recorded'
        sites[sid] = {'class': cls, 'prior_direct_target': is_direct, 'prior_input_premise': premises, 'prior_target_family': family,
                      'direct_runs': [t['run'] for t in transmissions if direct.get(t['direct_task']) == sid]}
    strata = {'prior_direct_target': [s for s in sites if sites[s]['prior_direct_target']],
              'prior_input_premise_formula': [s for s in sites if sites[s]['prior_input_premise']],
              'prior_target_family': [s for s in sites if sites[s]['prior_target_family']],
              'refutation_targets': [s for s in sites if targets[s] == 'False'],
              'symmetric_target_pairs': decision['strata']['symmetric_target_pairs']}
    primary = json.loads(membership_bytes)['primary']
    sensitivity = {'omit_prior_direct_target': [s for s in primary if s not in strata['prior_direct_target']],
                   'omit_prior_target_family': [s for s in primary if s not in strata['prior_target_family']]}
    if {k: v for k, v in strata.items()} != decision['strata'] or sensitivity != decision['reporting']['sensitivity_sets'] or primary != decision['primary']:
        raise ValueError('derived strata or sensitivity sets differ from the review decision')
    return {'schema_version': 'r6-census-exposure-1', 'census_id': census['census_id'],
            'census_sha256': sha((census_dir/'census.json').read_bytes()), 'membership_sha256': sha(membership_bytes),
            'decision_sha256': sha(decision_bytes), 'decision': decision['decision'],
            'supersedes_reading_of': 'census.json sites[].exposure (retained unchanged; its model_visible_in wording overstated what was shown)',
            'classes': {'prior_direct_target': 'the site obligation was the target of a recorded provider transmission',
                        'prior_input_premise_formula': 'a hypothesis sent in a recorded request has exactly this site\'s captured target as its type; shown as a premise, not posed as a goal',
                        'prior_target_family': 'same containing declaration as a prior target; related, not shown',
                        'none_recorded': 'no recorded experiment posed or showed it; not unseen mathematics, not an uncontaminated task'},
            'prior_transmissions': [{k: v for k, v in t.items() if k != 'rows'} | {'row_names': [r['name'] for r in t['rows']]} for t in transmissions],
            'witness_note': 'no request supplied a witness; the pilot returned hwidth + 32769*neg_goal and the later live run 2*hZ + neg_goal: generated responses, not reference answers',
            'sites': sites, 'strata': strata, 'primary': primary,
            'reporting': {'family_summaries': 'report every site and each of the four families; families are clusters, not independent samples',
                          'symmetric_pairs': 'keep both branches; do not present paired sites or repeated draws as independent mathematical samples',
                          'sensitivity_sets': sensitivity, 'uncontaminated_claim': 'none; no subset supports it',
                          'prior_live_samples': decision['reporting']['prior_live_samples']},
            'program_sha256': sha(Path(__file__).read_bytes())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='write tasks/census-v1/exposure-addendum.json (refuses to overwrite)')
    args = parser.parse_args()
    value = derive()
    if args.write:
        target = CENSUS_DIR/ADDENDUM
        if target.exists(): raise SystemExit('addendum already recorded: '+str(target))
        target.write_bytes(json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False).encode()+b'\n')
    print(json.dumps({s: v['class'] for s, v in value['sites'].items()}, indent=1))


if __name__ == '__main__':
    main()
