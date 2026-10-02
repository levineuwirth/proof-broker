#!/usr/bin/env python3
"""R6-016 control 5's labels (`R6-016-PROPOSAL.md`, revision 2, section 5).

    labels.py write        write the labels record, once, before the R6-016 lock

"Control 5's labels are computed by R6-015's frozen rule from the qualification audit's classifications as recorded at R6-016's
lock: addendum 1, and the amendment's addendum 2 if it exists by then."

**The entries** are R6-015's step-3 record's (`R6-015-MUTATIONS-2.json`): the same 16 rows, sources, maps and matched draws, in the
same order. Only the classifications and the labels are recomputed.

**The classifications** are each slot's local-target classification:
- **addendum 1** (`qualification-audit-v1`'s record) for the slots it classified;
- **addendum 2** (`qualification-audit-v2`'s record) for the 16 it left unbound, at l096 and l099. That record must be
  `qualification-audit-v2`'s, under its lock, gated on a regression record that passed (`regression_passed`, the approved gate).

**The rule** is R6-015's (`r6-015/mutations.py`, `expectation`), read as a rule over classifications. Its first clause, written
there for the sites l096 and l099, says why: "not classified by the audit". It is applied as that condition:
1. a slot without a classification gives `no_expectation: not classified by the audit`;
2. l070 with draw 5 gives `no_fixed_prediction: sufficiency not established (draw 5)`;
3. every slot `certificate_alone` or `sufficient_but_context_referenced` gives `expected_pass`;
4. otherwise `no_expectation`.

A deterministic map identical to no learned map keeps `no_expectation: not identical to an audited learned map`, as in R6-015.

**A regression check:** wherever every slot's classification comes from addendum 1, the label must equal R6-015's. Only the l096
and l099 entries may change.
"""
import argparse
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
if str(R6) not in sys.path: sys.path.insert(0, str(R6))

import run as r6  # noqa: E402

RECORD = R6/'reviews/2026-10-02/R6-016-CONTROL-5-LABELS.json'
STEP3 = R6/'reviews/2026-10-01/R6-015-MUTATIONS-2.json'
ADDENDUM1 = R6/'reviews/2026-10-01/R6-QUALIFICATION-1-AUDIT.json'
ADDENDUM2 = R6/'reviews/2026-10-02/R6-QUALIFICATION-1-AUDIT-V2-ADDENDUM-2.json'
REGRESSION = R6/'reviews/2026-10-02/R6-QUALIFICATION-1-AUDIT-V2-REGRESSION.json'
V2_LOCK = R6/'policies/qualification-audit-v2.sha256.json'
UNBOUND = 'unbound_residual_mismatch'
PASSING = ('certificate_alone', 'sufficient_but_context_referenced')
SCHEMA = 'r6-016-control-5-labels-1'


def expectation(site, draws, slots):
    """R6-015's frozen rule, over classifications (see above)."""
    if any(c is None or c == UNBOUND for c in slots.values()): return 'no_expectation: not classified by the audit'
    if site == 'l070' and 5 in draws: return 'no_fixed_prediction: sufficiency not established (draw 5)'
    if all(c in PASSING for c in slots.values()): return 'expected_pass'
    return 'no_expectation'


def addendum2():
    """Addendum 2's record, checked: the application, its lock, and its regression gate (the approved `regression_passed`)."""
    sys.path.insert(0, str(R6/'qualification-audit-v2'))
    import qualification_audit_v2 as v2
    record = r6.read_json(ADDENDUM2)
    if record.get('application') != 'addendum2' or record.get('lock_sha256') != r6.sha(V2_LOCK) or v2.LOCK != V2_LOCK:
        raise ValueError("addendum 2's record is not qualification-audit-v2's, under its lock")
    if v2.regression_passed(REGRESSION, r6.read_json(V2_LOCK)) != record.get('regression_record_sha256'):
        raise ValueError("addendum 2's record is not gated on the passing regression record")
    return record['results']


def classifications():
    """Each slot's local classification, and the record it comes from."""
    first, second = r6.read_json(ADDENDUM1)['slots'], addendum2()
    out = {}
    for slot, s in first.items():
        c = s['audit']['local']['classification']
        out[slot] = {'classification': c, 'record': 'addendum_1'}
        if c == UNBOUND and slot in second:
            out[slot] = {'classification': (second[slot].get('audit') or {}).get('local', {}).get('classification'), 'record': 'addendum_2'}
    if set(second) - set(first): raise ValueError("addendum 2 names slots addendum 1 does not")
    return out


def compute():
    step3, cls = r6.read_json(STEP3), classifications()
    entries = []
    for c in step3['control_5']:
        if c.get('retained') is False:
            entries.append({k: c[k] for k in ('site', 'source', 'retained', 'reason')}); continue
        site = c['site']; arm = c['source']['arm']
        draws = c['draws'] if arm == 'learned' else c['identical_to_learned_draws']
        row = {k: c[k] for k in ('site', 'source', 'map')}
        row['draws' if arm == 'learned' else 'identical_to_learned_draws'] = draws
        if arm == 'deterministic' and not draws:
            slots, sources, label = {}, {}, 'no_expectation: not identical to an audited learned map'
        else:
            keys = [f'bracket-{site}/{d}' for d in draws]
            slots = {k: cls[k]['classification'] for k in keys}; sources = {k: cls[k]['record'] for k in keys}
            label = expectation(site, draws, slots)
        if all(s == 'addendum_1' for s in sources.values()) and label != c['expectation']:
            raise ValueError(f"{site} {arm}: the rule does not reproduce R6-015's label from addendum 1")
        entries.append({**row, 'audited_slots': slots, 'classified_by': sources, 'expectation': label,
                        'r6_015_expectation': c['expectation']})
    if len(entries) != len(step3['control_5']): raise ValueError('control 5 coverage')
    return {'schema_version': SCHEMA, 'control_5': entries,
            'expected_pass': sum(e.get('expectation') == 'expected_pass' for e in entries),
            'changed_from_r6_015': [f"{e['site']} {e['source']['arm']}" for e in entries
                                    if 'expectation' in e and e['expectation'] != e['r6_015_expectation']],
            'inputs_sha256': {str(p.relative_to(R6)): r6.sha(p) for p in (STEP3, ADDENDUM1, ADDENDUM2, REGRESSION, V2_LOCK)},
            'sources_sha256': {str(Path(__file__).resolve().relative_to(R6)): r6.sha(Path(__file__).resolve())}}


def verify(plan_path=None):
    """The labels record is exactly what the rule computes now, from the same inputs."""
    if not RECORD.exists(): raise ValueError('the control-5 labels record does not exist')
    if r6.read_json(RECORD) != compute(): raise ValueError('the control-5 labels record does not verify')
    return r6.read_json(RECORD)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('command', choices=['write'])
    p.parse_args()
    if RECORD.exists(): raise SystemExit(f'refusing to overwrite {RECORD}')
    record = compute()
    RECORD.write_text(json.dumps(record, indent=1) + '\n')
    print(json.dumps({'expected_pass': record['expected_pass'], 'changed_from_r6_015': record['changed_from_r6_015']}))


if __name__ == '__main__':
    main()
