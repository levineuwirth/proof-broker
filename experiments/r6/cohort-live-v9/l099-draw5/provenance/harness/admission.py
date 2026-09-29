"""Pre-search diagnostic membership, independent of proposer/solver success.

The rule is sufficient, not complete. Unknown evidence stays unresolved. P6's
truth and weakened-IR satisfiability are re-derived with integer arithmetic;
the recorded dropped-local observation remains a trusted-host observation.
"""
import re

import events
import instrument
import payload
import run as r6

RULE = 'dropped_proposition_and_original_true_and_checked_ir_counterexample_v1'
FROZEN = r6.ROOT/'policies/admission-v1.json'
PREFIX = 'experiments/c1-cert-recovery/'
P6_FILES = {
    'source': PREFIX+'runs/20260907-113052/lean/P6_hyp_le.omega.lean',
    'reification_log': PREFIX+'runs/20260907-113052/irlogs/P6_hyp_le.capture.log',
    'final_ir': PREFIX+'raw/20260907-113052/P6_hyp_le.final_ir.json',
}


def classify(dropped_proposition, original_true, ir_counterexample_checked):
    values = (dropped_proposition, original_true, ir_counterexample_checked)
    if any(v is not None and type(v) is not bool for v in values):
        raise ValueError('Admission evidence must be true, false, or unknown')
    if all(v is True for v in values):
        return 'translation_loss_diagnostic'
    if any(v is False for v in values):
        return 'criterion_not_established'
    return 'unresolved'


def counterexample(rows, assignment):
    variables = {term['variable'] for row in rows for term in row['terms']}
    if set(assignment) != variables or any(type(v) is not int for v in assignment.values()):
        raise ValueError('Counterexample must assign every IR variable exactly once')
    checked = []
    for row in rows:
        total = int(row['constant']) + sum(int(t['coefficient'])*assignment[t['variable']] for t in row['terms'])
        relation = row['relation']
        if relation not in {'le', 'lt', 'eq'}:
            raise ValueError('Unknown row relation')
        satisfied = total <= 0 if relation == 'le' else total < 0 if relation == 'lt' else total == 0
        checked.append({'name': row['name'], 'result': str(total), 'satisfied': satisfied})
    if not rows or [r['name'] for r in rows].count('neg_goal') != 1:
        raise ValueError('Missing or ambiguous negated target')
    return checked, all(row['satisfied'] for row in checked)


def p6_evidence(source, log, ir):
    # Exactly one concrete source shape, with all mathematical parameters parsed
    # from it. This is an evidence producer for P6, not a general Lean parser.
    pattern = (r'example \(g_hi : ZMod P\) \(hhi : g_hi.val ≤ 2\^(\d+) - 1\) '
               r'\(hP : P = (\d+)\) :\s+2\^(\d+) \* g_hi.val < P := by\s+omega\s*\Z')
    matches = list(re.finditer(pattern, source))
    if len(matches) != 1 or source.count('example (') != 1:
        raise ValueError('P6 source truth anchor absent or ambiguous')
    power, modulus, coefficient_power = map(int, matches[0].groups())
    bound, multiplier = 2**power-1, 2**coefficient_power
    dropped = 'hhi — proposition outside the reifiable fragment (g_hi.val ≤ 2 ^ '+str(power)+' - 1)'
    if log.count(dropped) != 1:
        raise ValueError('P6 dropped proposition anchor absent or ambiguous')
    rows = payload.arithmetic_rows(ir)
    # Independently bind the translated shape to the source's multiplier and P.
    expected_rows = [
        {'name': 'hP', 'relation': 'eq', 'constant': '0', 'terms': []},
        {'name': '_pb_nonneg_atom_0', 'relation': 'le', 'constant': '0',
         'terms': [{'variable': '_pb_atom_0', 'coefficient': '-1'}]},
        {'name': 'neg_goal', 'relation': 'le', 'constant': str(modulus),
         'terms': [{'variable': '_pb_atom_0', 'coefficient': str(-multiplier)}]},
    ]
    if rows != expected_rows:
        raise ValueError('P6 weakened IR changed')
    assignment = {'_pb_atom_0': (modulus+multiplier-1)//multiplier}
    evaluations, satisfiable = counterexample(rows, assignment)
    true = bound >= 0 and multiplier*bound < modulus
    return {'dropped_propositions': ['hhi'], 'original_true': true,
        'truth_method': 'integer upper bound using the explicit hP equality and hhi bound',
        'maximum_lhs': str(multiplier*bound), 'rhs': str(modulus),
        'strict_margin': str(modulus-multiplier*bound), 'satisfying_original_value': '0',
        'ir_counterexample': {k: str(v) for k, v in assignment.items()}, 'row_evaluations': evaluations,
        'ir_counterexample_checked': satisfiable,
        'classification': classify(True, true, satisfiable)}


def derive():
    data = {name: instrument.original(path) for name, path in P6_FILES.items()}
    evidence = p6_evidence(data['source'].decode(), data['reification_log'].decode(),
                           payload.strict_json(data['final_ir']))
    return {'schema_version': 'r6-admission-1', 'rule': RULE,
        'criterion': ['at least one recorded dropped proposition', 'independently established original truth',
                      'independently checked satisfying assignment for all IR hypotheses and negated goal'],
        'unknown_evidence': 'unresolved; never inferred from lack of solver/model success',
        'rule_scope': 'sufficient diagnostic criterion; not a completeness test for reification',
        'controls': {task.id: {'stratum': 'development_control', 'manifest_sha256': r6.sha(task.path/'manifest.json')}
                     for task in (r6.D1, r6.C8)},
        'P6_hyp_le': {'stratum': 'translation_loss_diagnostic', 'dispatch_in_this_policy': False,
            'repository': 'https://github.com/levineuwirth/proof-broker.git', 'commit': instrument.BASE,
            'inputs': {name: {'path': P6_FILES[name], 'sha256': r6.hashlib.sha256(content).hexdigest()}
                       for name, content in data.items()}, 'evidence': evidence},
        'qualification': 'P6 is diagnosed before requests, not registered as a runnable task. '
                         'Reifier logs are observations, not computation attestations. '
                         'The criterion does not isolate dropping from other abstraction effects.'}


def verify():
    record = r6.read_json(FROZEN)
    if events.canonical(record) != events.canonical(derive()):
        raise ValueError('Frozen pre-search admission evidence changed')
    return record


if __name__ == '__main__':
    # Explicit creation only; a frozen cohort is never silently overwritten.
    with FROZEN.open('x') as f:
        f.write(__import__('json').dumps(derive(), indent=2)+'\n')
