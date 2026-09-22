#!/usr/bin/env python3
"""Read-only arithmetic review of R6-011 at 27579e5; no native run or model call."""
import argparse
import collections
import copy
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import site_representability as rep
import site_task


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite')
    site_task.verify_lock()
    runs = ROOT/'census-runs/representability-v1'
    duplicate_rows = {}
    for path in sorted(runs.glob('*/prepared.json')):
        rows = json.loads(path.read_bytes())['rows']
        dup = {n: c for n, c in collections.Counter(r['name'] for r in rows).items() if c > 1}
        if dup: duplicate_rows[path.parent.name] = dup
    assert duplicate_rows == {'bracket-l178': {'this': 2}}
    p178 = runs/'bracket-l178/prepared.json'
    rows = json.loads(p178.read_bytes())['rows']
    selected = [7, 8, 11]
    assert [rows[i]['name'] for i in selected] == ['this', 'this', 'neg_goal']
    assert all(rows[i]['relation'] == 'le' for i in selected)
    coefficients = {}
    constant = 0
    for i in selected:
        constant += int(rows[i]['constant'])
        for t in rows[i]['terms']:
            v = t['variable']
            coefficients[v] = coefficients.get(v, 0) + int(t['coefficient'])
    assert constant == 1 and all(v == 0 for v in coefficients.values())
    assert rep.farkas(rows) is None
    indexed = copy.deepcopy(rows)
    for i, row in enumerate(indexed): row['name'] = f'row_{i}'
    witness = rep.primitive(rep.farkas(indexed))
    assert rep.check_certificate(indexed, witness)
    p170 = runs/'bracket-l170/prepared.json'
    rows170 = json.loads(p170.read_bytes())['rows']
    assignment = {t['variable']: 0 for row in rows170 for t in row['terms']}
    assignment['Zmax'] = 1
    evaluated = []
    for row in rows170:
        value = int(row['constant']) + sum(int(t['coefficient'])*assignment[t['variable']] for t in row['terms'])
        assert row['relation'] in ('eq', 'le')
        assert value == 0 if row['relation'] == 'eq' else value <= 0
        evaluated.append({'name': row['name'], 'relation': row['relation'], 'value': value})
    locks = {}
    for name in ('fixture-harness-v1', 'cohort-harness-v3', 'census-harness-v1', 'site-harness-v1'):
        path = ROOT/'policies'/f'{name}.sha256.json'
        entries = json.loads(path.read_bytes())
        assert all(sha(ROOT/k) == v for k, v in entries.items()), name
        locks[name] = {'sha256': sha(path), 'files': len(entries), 'matched': True}
    result = {'complete': True, 'reviewed_commit': '27579e5', 'duplicate_row_names': duplicate_rows,
              'l178': {'prepared_sha256': sha(p178), 'selected_zero_based_indices': selected,
                       'selected_rows': [rows[i] for i in selected], 'multipliers': [1, 1, 1],
                       'sum_constant': constant, 'sum_terms': coefficients,
                       'current_classifier_returns_no_certificate': True,
                       'index_named_arithmetic_witness': witness,
                       'scope': 'arithmetic contradiction over actual distinct rows; not a name-addressed SDK certificate or Lean reconstruction'},
              'l170': {'prepared_sha256': sha(p170), 'exact_feasible_assignment': assignment,
                       'evaluated_rows': evaluated,
                       'scope': 'satisfies all emitted rows including neg_goal, independently excludes a rational Farkas contradiction over these rows'},
              'locks': locks, 'program_sha256': sha(Path(__file__)),
              'native_runs': 0, 'provider_calls': 0, 'credentials_read': 0}
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'duplicate_row_names': duplicate_rows, 'l178_constant': constant,
                      'l170_feasible': True, 'locks_matched': len(locks)}))


if __name__ == '__main__':
    main()
