"""R6-011 representability: what the frozen IR and Farkas interface make of each reviewed census site, before either arm.

For every primary site the frozen preparation stages run on the site (`site_task`): the reifier builds the IR from the goal
state at the site and records every local it skips, the SDK pipeline compiles the IR into Farkas rows and records its own
omissions, and the context captured there must equal the frozen one. The prepared problem is then classified, with the
fifteen-site denominator preserved and no site removed for any outcome:

- `preparation_failed`: a stage did not return; the failing stage and its output digests are the reason.
- `not_lia` / `farkas_omissions`: the frozen request policy refuses the problem (fragment, or rows the compiler dropped).
- `projection_mismatch`: the SDK rows differ from the independent arithmetic projection of the final IR.
- `rational_certificate` / `no_rational_certificate`: whether the rows, as sent, admit a Farkas certificate over the rationals
  — decided exactly (a phase-one simplex over fractions on the dual system, Bland's rule), not by any search route, and the
  certificate checked exactly. Without a rational certificate the frozen certificate path cannot close the site however the
  witness is proposed; with one, the reconstruction path is still unexercised until the deterministic arm runs.

Every class records the reifier's omissions split into data locals (undeclarable types) and dropped propositions: a dropped
proposition is a hypothesis the model will never see, and is reported as such, never as a model failure. The certificate found
here is an existence proof and a canned rehearsal fixture; it is never model-visible and is not the deterministic arm's result.
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
import site_task

RUNS = r6.ROOT/'census-runs/representability-v1'
CLASSES = ('preparation_failed', 'interface_refused', 'not_lia', 'farkas_omissions', 'projection_unsupported', 'projection_mismatch', 'no_rational_certificate', 'rational_certificate')


def farkas(rows):
    """Exact: nonnegative multipliers for `le` rows and free ones for `eq` rows whose combination cancels every variable and leaves
    a positive constant, i.e. sum(c_i y_i) = 1 and sum(a_ij y_i) = 0 for every variable j. Returns {row name: Fraction} or None."""
    variables = sorted({t['variable'] for r in rows for t in r['terms']})
    columns = []  # (row name, sign)
    for r in rows:
        columns.append((r['name'], 1))
        if r['relation'] == 'eq': columns.append((r['name'], -1))
    by_name = {r['name']: r for r in rows}
    def coefficient(col, var):
        name, sign = col; t = next((t for t in by_name[name]['terms'] if t['variable'] == var), None)
        return sign*int(t['coefficient']) if t else 0
    A = [[Fraction(coefficient(c, v)) for c in columns] for v in variables] + [[Fraction(sign*int(by_name[n]['constant'])) for n, sign in columns]]
    b = [Fraction(0)]*len(variables) + [Fraction(1)]
    m, n = len(A), len(columns)
    # phase one: minimize the sum of artificials a_k in A y + a = b, y, a >= 0
    tableau = [A[i] + [Fraction(int(i == k)) for k in range(m)] + [b[i]] for i in range(m)]
    basis = [n+i for i in range(m)]
    cost = [Fraction(0)]*n + [Fraction(1)]*m + [Fraction(0)]
    def reduced():
        return [cost[j] - sum(cost[basis[i]]*tableau[i][j] for i in range(m)) for j in range(n+m+1)]
    for _ in range(10000):
        z = reduced(); entering = next((j for j in range(n+m) if z[j] < 0), None)  # Bland: lowest index
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
    multipliers = {}
    for (name, sign), value in zip(columns, y): multipliers[name] = multipliers.get(name, Fraction(0)) + sign*value
    return {k: v for k, v in multipliers.items() if v != 0}


def primitive(multipliers):
    """Scale to integers and divide by the positive gcd; sign is preserved."""
    scale = lcm(*[v.denominator for v in multipliers.values()]); ints = {k: int(v*scale) for k, v in multipliers.items()}
    g = 0
    for v in ints.values(): g = gcd(g, abs(v))
    return {k: v//g for k, v in ints.items()}


def check_certificate(rows, witness):
    """Exact check of an integer witness against the rows: `le` multipliers nonnegative, every variable cancelled, positive constant."""
    by_name = {r['name']: r for r in rows}
    if not witness or any(n not in by_name for n in witness): return False
    if any(by_name[n]['relation'] == 'le' and c < 0 for n, c in witness.items()): return False
    total = {}
    for n, c in witness.items():
        for t in by_name[n]['terms']: total[t['variable']] = total.get(t['variable'], 0) + c*int(t['coefficient'])
    return all(v == 0 for v in total.values()) and sum(c*int(by_name[n]['constant']) for n, c in witness.items()) > 0


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


def classify(prepared, reified):
    omissions = reified['skipped_locals']
    data_locals = [o for o in omissions if o['reason'].startswith('data local')]
    dropped = [o for o in omissions if not o['reason'].startswith('data local')]
    rows = prepared['rows']; names = [r['name'] for r in rows]
    base = {'fragment': prepared['fragment'], 'row_count': len(rows), 'row_names': names, 'neg_goal_rows': names.count('neg_goal'),
            'variables': sorted({t['variable'] for r in rows for t in r['terms']}), 'reifier_data_locals': [o['name'] for o in data_locals],
            'reifier_dropped_propositions': dropped, 'farkas_omissions': prepared['farkas_omissions']}
    # the SDK rows always get the exact certificate question answered, whatever the frozen request policy says about them
    multipliers = farkas(rows) if rows else None
    if multipliers is None: certificate = {'sdk_rows_rational_certificate': False}
    else:
        witness = primitive(multipliers)
        if not check_certificate(rows, witness): raise ValueError('exact certificate failed its own check')
        certificate = {'sdk_rows_rational_certificate': True,
                       'certificate': [{'hypothesis': n, 'coefficient': str(witness[n])} for n in names if n in witness],
                       'certificate_support': len(witness), 'certificate_uses_neg_goal': 'neg_goal' in witness,
                       'certificate_scope': 'existence proof over Q by exact simplex on the SDK rows; rehearsal fixture only; never model-visible; not the deterministic arm'}
    base.update(certificate)
    # then the frozen request policy (`payload.request`): LIA, no compilation omissions, rows equal to the independent projection
    if prepared['fragment'] != 'LIA': return {'class': 'not_lia', **base}
    if prepared['farkas_omissions']: return {'class': 'farkas_omissions', **base}
    try: projected = payload.arithmetic_rows(prepared['final_ir'])
    except ValueError as error: return {'class': 'projection_unsupported', 'detail': str(error), **base}
    if projected != rows: return {'class': 'projection_mismatch', 'detail': 'SDK rows differ from the independent projection', **base}
    if names.count('neg_goal') != 1: return {'class': 'projection_mismatch', 'detail': 'the request policy requires exactly one neg_goal row', **base}
    return {'class': 'rational_certificate' if certificate['sdk_rows_rational_certificate'] else 'no_rational_certificate', **base}


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
    summary = {'schema_version': 'r6-representability-1', 'population': list(site_task.primary()), 'denominator': len(results),
               'classes': {c: [r['site_id'] for r in results if r['class'] == c] for c in CLASSES},
               'results': results, 'runs_sha256': {r['site_id']: r6.sha(runs/r['site_id']/'seal.json') for r in results},
               'site_lock_sha256': r6.sha(site_task.LOCK), 'site_task_sha256': r6.sha(r6.ROOT/'site_task.py'), 'program_sha256': r6.sha(Path(__file__)),
               'scope': 'the frozen IR and Farkas interface on every reviewed site; no proposal, no deterministic search, no provider call'}
    r6.write_json(runs/'representability.json', summary)
    print(json.dumps({c: len(v) for c, v in summary['classes'].items()}, indent=1))


if __name__ == '__main__':
    main()
