"""R6-012 representability, revision 2: what the frozen IR and Farkas interface make of each reviewed census site.

Revision 1 (R6-011) keyed the exact Farkas computation by row *name*; two distinct l178 rows are both named `this`, the first
was silently overwritten, and the classifier reported no certificate where one exists. Revision 2 separates three questions
that revision 1 conflated, each decided exactly and each recorded per site:

- **Arithmetic.** Over the rows as emitted, addressed by *index*: a rational Farkas certificate (phase-one simplex over
  fractions on the dual system, Bland's rule, checked exactly by index), or, when there is none, an exhibited rational point
  satisfying every row (phase one on the primal system, checked exactly). Nonexistence is never reported without that point.
- **Name addressing.** Whether every row name is unique. The model, the SDK assembler and verifier and the Lean
  reconstruction address rows by name, so a certificate is only name-addressable over unique names; the name-addressed
  checker refuses an ambiguous row set rather than choosing a row.
- **Admission.** The frozen request policy (`payload.request`) as before, and policy C (`site_request.admit`), the reviewed
  choice for the learned arm.

The headline class is policy C's: `posable_certificate`, `posable_negative_control` (posable, no certificate over the rows,
feasible point exhibited), `ambiguous_reference`, another `policy_c_refused` code, `interface_refused` (the SDK's own refusal
at pipeline preparation), or `preparation_failed`. The fifteen-site denominator is kept; nothing is selected on success. The
certificate or point is evaluator-only: an existence fact and a rehearsal fixture, never model-visible, not the deterministic
arm's result. What the learned interface cannot pose says nothing, by itself, about the deterministic arm's evidence path.
"""
import argparse
from fractions import Fraction
import json
from math import gcd, lcm
from pathlib import Path
import time

import episode
import events
import payload
import run as r6
import site_request
import site_task

RUNS = r6.ROOT/'census-runs/representability-v2'
CLASSES = ('preparation_failed', 'interface_refused', 'ambiguous_reference', 'policy_c_refused', 'posable_negative_control', 'posable_certificate')
FROZEN_POLICY_CLASSES = ('not_lia', 'farkas_omissions', 'projection_unsupported', 'projection_mismatch', 'admissible')


def phase_one(A, b):
    """Exact: a nonnegative y with A y = b (b >= 0), or None. Artificial basis, Bland's rule, fractions throughout."""
    m, n = len(A), len(A[0]) if A else 0
    tableau = [[Fraction(x) for x in A[i]] + [Fraction(int(i == k)) for k in range(m)] + [Fraction(b[i])] for i in range(m)]
    basis = [n+i for i in range(m)]
    cost = [Fraction(0)]*n + [Fraction(1)]*m + [Fraction(0)]
    for _ in range(100000):
        z = [cost[j] - sum(cost[basis[i]]*tableau[i][j] for i in range(m)) for j in range(n+m)]
        entering = next((j for j in range(n+m) if z[j] < 0), None)
        if entering is None: break
        ratios = [(tableau[i][-1]/tableau[i][entering], basis[i], i) for i in range(m) if tableau[i][entering] > 0]
        if not ratios: raise ValueError('phase one unbounded')
        _, _, leave = min(ratios)
        pivot = tableau[leave][entering]; tableau[leave] = [x/pivot for x in tableau[leave]]
        for i in range(m):
            if i != leave and tableau[i][entering] != 0:
                f = tableau[i][entering]; tableau[i] = [x - f*y for x, y in zip(tableau[i], tableau[leave])]
        basis[leave] = entering
    else: raise ValueError('simplex did not terminate')
    if sum(tableau[i][-1] for i in range(m) if basis[i] >= n) != 0: return None
    y = [Fraction(0)]*n
    for i in range(m):
        if basis[i] < n: y[basis[i]] = tableau[i][-1]
    return y


def coefficient(row, variable):
    return next((int(t['coefficient']) for t in row['terms'] if t['variable'] == variable), 0)


def farkas(rows):
    """Multipliers by row *index*: nonnegative for `le`, free for `eq`, cancelling every variable with sum(c_i y_i) = 1."""
    variables = sorted({t['variable'] for r in rows for t in r['terms']})
    columns = [(i, s) for i, r in enumerate(rows) for s in ((1,) if r['relation'] == 'le' else (1, -1))]
    A = [[s*coefficient(rows[i], v) for i, s in columns] for v in variables] + [[s*int(rows[i]['constant']) for i, s in columns]]
    y = phase_one(A, [0]*len(variables) + [1])
    if y is None: return None
    multipliers = {}
    for (i, s), value in zip(columns, y): multipliers[i] = multipliers.get(i, Fraction(0)) + s*value
    return {k: v for k, v in multipliers.items() if v != 0}


def feasible_point(rows):
    """An exact rational assignment satisfying every row (`le` rows <= 0, `eq` rows = 0), or None. Variables are free: x = p - q."""
    variables = sorted({t['variable'] for r in rows for t in r['terms']})
    slack = [i for i, r in enumerate(rows) if r['relation'] == 'le']
    A, b = [], []
    for i, r in enumerate(rows):
        line = [coefficient(r, v) for v in variables] + [-coefficient(r, v) for v in variables] + [int(i == k) for k in slack]
        rhs = -int(r['constant'])
        if rhs < 0: line, rhs = [-x for x in line], -rhs
        A.append(line); b.append(rhs)
    y = phase_one(A, b) if A else []
    if y is None: return None
    return {v: y[j] - y[len(variables)+j] for j, v in enumerate(variables)}


def primitive(multipliers):
    """Scale to integers and divide by the positive gcd; sign is preserved."""
    scale = lcm(*[v.denominator for v in multipliers.values()]); ints = {k: int(v*scale) for k, v in multipliers.items()}
    g = 0
    for v in ints.values(): g = gcd(g, abs(v))
    return {k: v//g for k, v in ints.items()}


def check_indexed(rows, witness):
    """Exact check of an integer witness addressed by row index."""
    if not witness or any(not (0 <= i < len(rows)) for i in witness): return False
    if any(rows[i]['relation'] == 'le' and c < 0 for i, c in witness.items()): return False
    total = {}
    for i, c in witness.items():
        for t in rows[i]['terms']: total[t['variable']] = total.get(t['variable'], 0) + c*int(t['coefficient'])
    return all(v == 0 for v in total.values()) and sum(c*int(rows[i]['constant']) for i, c in witness.items()) > 0


class Ambiguous(ValueError):
    pass


def check_certificate(rows, witness):
    """The name-addressed check the proposal interface implies: refuses an ambiguous row set instead of choosing a row."""
    names = [r['name'] for r in rows]
    duplicates = sorted({n for n in names if names.count(n) > 1})
    if duplicates: raise Ambiguous('ambiguous row names: '+', '.join(duplicates))
    if any(n not in names for n in witness): return False
    return check_indexed(rows, {names.index(n): c for n, c in witness.items()})


def check_point(rows, point):
    for r in rows:
        value = int(r['constant']) + sum(int(t['coefficient'])*point.get(t['variable'], 0) for t in r['terms'])
        if (r['relation'] == 'le' and value > 0) or (r['relation'] == 'eq' and value != 0): return False
    return True


def failure_record(run):
    """The first stage that did not return, with its output digests and heads."""
    for stage in ('preparation-build', 'preparation', 'pipeline-prepare'):
        process = run/'stages'/stage/(stage+'.process.json')
        if not process.exists(): return {'stage': stage, 'recorded': False}
        record = r6.read_json(process)
        if record['exit_code'] != 0 or record.get('resource_exhausted') or record.get('monitor_error'):
            streams = {}
            for s in ('stdout', 'stderr'):
                p = run/'stages'/stage/f'{stage}.{s}'; data = p.read_bytes() if p.exists() else b''
                streams[s+'_sha256'] = r6.hashlib.sha256(data).hexdigest(); streams[s+'_head'] = data[:2000].decode('utf-8', 'replace')
            return {'stage': stage, 'exit_code': record['exit_code'], 'resource_exhausted': record.get('resource_exhausted'), **streams}
    return {'stage': 'unknown'}


def frozen_policy(prepared):
    """The frozen request policy's verdict, reported beside policy C's."""
    if prepared['fragment'] != 'LIA': return 'not_lia'
    if prepared['farkas_omissions']: return 'farkas_omissions'
    try: projected = payload.arithmetic_rows(prepared['final_ir'])
    except ValueError: return 'projection_unsupported'
    names = [r['name'] for r in prepared['rows']]
    if projected != prepared['rows'] or names.count('neg_goal') != 1 or len(names) != len(set(names)): return 'projection_mismatch'
    return 'admissible'


def classify(prepared, reified):
    omissions = reified['skipped_locals']
    rows = prepared['rows']; names = [r['name'] for r in rows]
    duplicates = sorted({n for n in names if names.count(n) > 1})
    base = {'fragment': prepared['fragment'], 'row_count': len(rows), 'row_names': names, 'neg_goal_rows': names.count('neg_goal'),
            'variables': sorted({t['variable'] for r in rows for t in r['terms']}),
            'reifier_data_locals': [o['name'] for o in omissions if o['reason'].startswith('data local')],
            'reifier_dropped_propositions': [o for o in omissions if not o['reason'].startswith('data local')],
            'farkas_omissions': prepared['farkas_omissions'], 'names_unique': not duplicates, 'duplicate_names': duplicates,
            'frozen_policy_class': frozen_policy(prepared)}
    multipliers = farkas(rows) if rows else None
    if multipliers is not None:
        witness = primitive(multipliers)
        if not check_indexed(rows, witness): raise ValueError('exact certificate failed its own check')
        base.update(arithmetic_certificate=True, certificate_rows=[{'index': i, 'name': rows[i]['name'], 'coefficient': str(witness[i])} for i in sorted(witness)],
                    certificate_support=len(witness), certificate_uses_neg_goal=any(rows[i]['name'] == 'neg_goal' for i in witness))
        if not duplicates:
            named = {rows[i]['name']: c for i, c in witness.items()}
            if not check_certificate(rows, named): raise ValueError('name-addressed certificate failed its check')
            base['certificate'] = [{'hypothesis': rows[i]['name'], 'coefficient': str(witness[i])} for i in sorted(witness)]
    else:
        point = feasible_point(rows)
        if point is None or not check_point(rows, point): raise ValueError('neither a certificate nor a feasible point: the exact computation is inconsistent')
        base.update(arithmetic_certificate=False, feasible_point={k: str(v) for k, v in sorted(point.items())})
    base['evidence_scope'] = 'exact arithmetic over the emitted rows; evaluator-only; not model-visible; not the deterministic arm; not a reconstruction'
    try:
        posed, evidence = site_request.admit(prepared)
        base.update(policy_c='posable', policy_c_evidence=evidence)
        return {'class': 'posable_certificate' if base['arithmetic_certificate'] else 'posable_negative_control', **base}
    except site_request.Refusal as refusal:
        base.update(policy_c=refusal.code, policy_c_detail=str(refusal))
        return {'class': 'ambiguous_reference' if refusal.code == 'policy_ambiguous_reference' else 'policy_c_refused', **base}


def seal(run):
    """`episode.seal` without its event-schema check, whose task enumeration names only the two registered controls; the chain
    itself is verified by `events.read`."""
    rows = events.read(run/'events.ndjson')
    if not rows or rows[-1]['event'] != 'episode_finished': raise ValueError('Cannot seal an incomplete classification')
    retained, ephemeral = {}, {}
    for p in sorted(run.rglob('*')):
        if not p.is_file() or p.name == 'seal.json': continue
        name = str(p.relative_to(run))
        target = ephemeral if ('.olean' in p.name or p.suffix in {'.ilean', '.c', '.o'}) else retained
        target[name] = r6.sha(p)
    r6.write_json(run/'seal.json', {'schema_version': 'r6-seal-1', 'event_count': len(rows), 'last_event_hash': rows[-1]['event_hash'],
                                    'retained_sha256': retained, 'ephemeral_sha256': ephemeral})


def classify_site(site_id, packages, runs=RUNS):
    task = site_task.get(site_id); run = runs/site_id; run.mkdir(parents=True, exist_ok=False)
    manifest, expected = site_task.frozen_site(task)
    events.append(run, 'episode', 'episode_started', {'task_manifest_sha256': r6.sha(task.path/'manifest.json'),
                  'challenge_sha256': expected['challenge_sha256'], 'purpose': 'representability classification; no proposal, no search, no provider'}, task_id=site_id)
    tools = site_task.setup(run, task, packages)
    started = time.monotonic()
    try:
        prepared, reified = site_task.prepare(run, task, tools)
        result = classify(prepared, reified)
    except (episode.StageFailure, ValueError, RuntimeError) as error:
        reason = failure_record(run)
        # the SDK's own deliberate refusal (an OCaml `Failure` on stderr, exit 1, at pipeline-prepare) is an interface limit, not a harness failure
        refused = reason['stage'] == 'pipeline-prepare' and reason.get('exit_code') == 1 and not reason.get('resource_exhausted') \
                  and reason.get('stderr_head', '').startswith('Failure(')
        result = {'class': 'interface_refused' if refused else 'preparation_failed', 'reason': reason, 'error': type(error).__name__+': '+str(error)[:500]}
    result = {'site_id': site_id, 'family': task.family, 'exposure_class': r6.read_json(site_task.ADDENDUM)['sites'][site_id]['class'],
              **result, 'seconds': round(time.monotonic()-started, 1)}
    r6.write_json(run/'representability.json', result)
    events.append(run, 'representability', 'classified', {'class': result['class'], 'representability_sha256': r6.sha(run/'representability.json')})
    events.append(run, 'episode', 'episode_finished', {'representability_sha256': r6.sha(run/'representability.json')})
    seal(run)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packages-dir', type=Path, default=r6.ROOT.parents[1]/'lean-bridge/.lake/packages')
    parser.add_argument('--runs', type=Path, default=RUNS)
    args = parser.parse_args()
    site_task.verify_lock(); runs = args.runs.resolve()
    if (runs/'representability.json').exists(): raise SystemExit('representability already recorded: '+str(runs))
    results = []
    for site_id in site_task.primary():
        result = classify_site(site_id, args.packages_dir.resolve(), runs); results.append(result)
        print(json.dumps({k: result[k] for k in ('site_id', 'class', 'seconds')}), flush=True)
    summary = {'schema_version': 'r6-representability-2', 'population': list(site_task.primary()), 'denominator': len(results),
               'classes': {c: [r['site_id'] for r in results if r['class'] == c] for c in CLASSES},
               'results': results, 'runs_sha256': {r['site_id']: r6.sha(runs/r['site_id']/'seal.json') for r in results},
               'site_lock_sha256': r6.sha(site_task.LOCK), 'site_task_sha256': r6.sha(r6.ROOT/'site_task.py'), 'program_sha256': r6.sha(Path(__file__)),
               'scope': 'the frozen IR and Farkas interface on every reviewed site; no proposal, no deterministic search, no provider call'}
    r6.write_json(runs/'representability.json', summary)
    print(json.dumps({c: len(v) for c, v in summary['classes'].items()}, indent=1))


if __name__ == '__main__':
    main()
