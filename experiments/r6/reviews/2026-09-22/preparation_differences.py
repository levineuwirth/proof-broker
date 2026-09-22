#!/usr/bin/env python3
"""R6-013: the exact before/after differences of the preparation repair, for all fifteen sites. Non-locked; read-only.

Before is representability revision 2 (the frozen R6-001 preparation overlay); after is revision 4 (site harness v4, whose preparation
equals revision 3's byte for byte). For each site: the input IR's differing top-level fields and user directives, the renamed search
context, the Farkas rows (equal, equal up to names, or different), the policy C request before and after (or its refusal), and whether
the classification changed. Nothing is inferred from outcomes.
"""
import argparse
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import cohort_budget as budget
import run as r6
import site_request
import site_task

BEFORE, AFTER = ROOT/'census-runs/representability-v2', ROOT/'census-runs/representability-v4'


def request(task, run):
    path = run/'prepared.json'
    if not path.exists(): return {'posed': False, 'code': 'interface_refused'}
    try: body, evidence = budget.request(task, r6.read_json(path))
    except site_request.Refusal as refusal: return {'posed': False, 'code': refusal.code}
    value = json.loads(body)
    return {'posed': True, 'request_sha256': r6.hashlib.sha256(body).hexdigest(), 'row_names': [r['name'] for r in value['problem']['rows']],
            'binding_input_ir_sha256': value['binding']['input_ir_sha256'], 'omitted': evidence['omitted_names']}


def site(site_id):
    task = site_task.get(site_id); a, b = BEFORE/site_id, AFTER/site_id
    old, new = r6.read_json(a/'representability.json'), r6.read_json(b/'representability.json')
    record = {'class_before': old['class'], 'class_after': new['class']}
    ir_a, ir_b = r6.read_json(a/'input-ir.json'), r6.read_json(b/'input-ir.json')
    record['input_ir'] = {'equal': ir_a == ir_b, 'differing_fields': sorted(k for k in set(ir_a) | set(ir_b) if ir_a.get(k) != ir_b.get(k)),
                          'user_directives_before': ir_a.get('user_directives'), 'user_directives_after': ir_b.get('user_directives')}
    record['renamed'] = [e for e in r6.read_json(b/'stages/preparation/output/reification.json')['search_context'] if e['original_name'] != e['search_name']]
    if (a/'prepared.json').exists() and (b/'prepared.json').exists():
        pa, pb = r6.read_json(a/'prepared.json'), r6.read_json(b/'prepared.json')
        strip = lambda rows: [{**r, 'name': None, 'terms': [(t['coefficient'],) for t in r['terms']]} for r in rows]
        record['rows'] = {'equal': pa['rows'] == pb['rows'], 'equal_up_to_names': strip(pa['rows']) == strip(pb['rows']),
                          'names_before': [r['name'] for r in pa['rows']], 'names_after': [r['name'] for r in pb['rows']],
                          'final_ir_equal': pa['final_ir'] == pb['final_ir'], 'farkas_omissions_equal': pa['farkas_omissions'] == pb['farkas_omissions']}
    else:
        record['rows'] = {'prepared_before': (a/'prepared.json').exists(), 'prepared_after': (b/'prepared.json').exists()}
    before, after = request(task, a), request(task, b)
    posed = before['posed'] and after['posed']  # None: not posed on both sides, so there are no bytes to compare
    record['request'] = {'before': before, 'after': after, 'bytes_equal': before['request_sha256'] == after['request_sha256'] if posed else None}
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    site_task.verify_lock()
    sites = {s: site(s) for s in site_task.primary()}
    summary = {'sites': len(sites), 'input_ir_changed': sorted(s for s, r in sites.items() if not r['input_ir']['equal']),
               'rows_changed': sorted(s for s, r in sites.items() if 'equal' in r['rows'] and not r['rows']['equal']),
               'rows_changed_in_meaning': sorted(s for s, r in sites.items() if 'equal_up_to_names' in r['rows'] and not r['rows']['equal_up_to_names']),
               'renamed': {s: [(e['original_name'], e['search_name']) for e in r['renamed']] for s, r in sites.items() if r['renamed']},
               'request_changed': sorted(s for s, r in sites.items() if r['request']['bytes_equal'] is False),
               'request_posed_only_after': sorted(s for s, r in sites.items() if r['request']['after']['posed'] and not r['request']['before']['posed']),
               'request_not_posed': sorted(s for s, r in sites.items() if not r['request']['after']['posed']),
               'class_changed': {s: [r['class_before'], r['class_after']] for s, r in sites.items() if r['class_before'] != r['class_after']}}
    r6.write_json(args.output, {'schema_version': 'r6-preparation-differences-1', 'before': str(BEFORE.relative_to(ROOT)), 'after': str(AFTER.relative_to(ROOT)),
                                'summary': summary, 'sites': sites, 'program_sha256': r6.sha(Path(__file__)),
                                'scope': 'retained classification runs only; no native execution'})
    print(json.dumps(summary, indent=1))


if __name__ == '__main__':
    main()
