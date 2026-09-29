"""R6-012 request policy C: which prepared problems may be posed to the learned arm, decided from the problem alone.

The frozen request policy (`payload.request`) poses a problem only when the source fragment is LIA, the SDK compiler omitted
nothing, and the rows equal an independent projection that has no case for a negated comparison. The reviewed decision
(R6-011-CONTRACT-DECISION.json, choice C) keeps every other admission check and relaxes exactly those three:

- A hypothesis the independent projection cannot express (a quantifier, an uninterpreted function, a disequality) is
  *omitted*; the omissions are derived here from the final IR, and must equal the SDK compiler's own omission list. Trusting
  that list and skipping its names would not be independent.
- A negated order comparison is expressed by negating its operand: `¬ a ≤ b` is `b < a`, `¬ a < b` is `b ≤ a`, with strict
  bounds tightened by one as elsewhere. No other negation is expressed.
- The source fragment is kept in evaluator evidence; the posed rows are LIA by construction, and the request says `LIA`.

Unchanged: canonical integer rows with sorted distinct variables, `le`/`eq` relations only, the rows equal to the SDK's own
rows in order, unique row names, and exactly one `neg_goal`. Distinct rows that share a name make the problem unposable:
the model, the SDK assembler and verifier, and the Lean reconstruction all address a row by its name, so an ambiguous name
cannot be carried through them by renaming the payload alone. Nothing here depends on whether a certificate exists.
"""
import re

import events

INTEGER = re.compile(r'-?(0|[1-9][0-9]*)')
ORDER = {'LE.le', 'LT.lt', 'GE.ge', 'GT.gt'}


class Refusal(ValueError):
    """The problem cannot be posed under policy C; `code` names the admission check."""
    def __init__(self, code, detail=''):
        super().__init__(code+(': '+detail if detail else '')); self.code = code


def arithmetic(node):
    """`payload.arithmetic_rows`' term projection, unchanged: integer literals, variables, opaque atoms, +, -, negation, scalar *."""
    def add(a, b, scale=1):
        terms = a[0].copy()
        for name, coefficient in b[0].items(): terms[name] = terms.get(name, 0)+scale*coefficient
        return {k: v for k, v in terms.items() if v}, a[1]+scale*b[1]
    def mul(a, n): return {k: v*n for k, v in a[0].items() if v*n}, a[1]*n
    kind = node['node']
    if kind == 'NumLit':
        if node['type'] not in {'Int', 'Nat'} or not INTEGER.fullmatch(node['value']): raise ValueError('Noninteger arithmetic input')
        return {}, int(node['value'])
    if kind in {'Var', 'Opaque'}: return {node['name'] if kind == 'Var' else node['payload_id']: 1}, 0
    if kind != 'App': raise ValueError('Unsupported arithmetic input')
    symbol, args = node['symbol'], node['args']
    if symbol == 'Int.ofNat' and len(args) == 1: return arithmetic(args[0])
    if symbol in {'Neg.neg', 'Int.neg'} and len(args) == 1: return mul(arithmetic(args[0]), -1)
    if len(args) != 2: raise ValueError('Unsupported arithmetic arity')
    a, b = map(arithmetic, args)
    if symbol in {'HAdd.hAdd', 'Int.add', 'Add.add'}: return add(a, b)
    if symbol in {'HSub.hSub', 'Int.sub', 'Sub.sub'}: return add(a, b, -1)
    if symbol in {'HMul.hMul', 'Int.mul', 'Mul.mul'}:
        if not a[0]: return mul(b, a[1])
        if not b[0]: return mul(a, b[1])
    raise ValueError('Unsupported or nonlinear arithmetic input')


def row(name, term, negate=False):
    """One proposition as a row `constant + sum(coefficient*variable) (le|eq) 0`; `negate` compiles its negation."""
    def combine(a, b):
        terms = a[0].copy()
        for k, v in b[0].items(): terms[k] = terms.get(k, 0)-v
        return {k: v for k, v in terms.items() if v}, a[1]-b[1]
    if term['node'] == 'Not' and term['operand']['node'] == 'App' and term['operand']['symbol'] in ORDER:
        return row(name, term['operand'], not negate)  # the one added case: a negated order comparison
    if term['node'] == 'Eq' and not negate:
        form, relation = combine(arithmetic(term['left']), arithmetic(term['right'])), 'eq'
    elif term['node'] == 'App' and term['symbol'] in ORDER:
        a, b = term['args']
        if term['symbol'] in {'GE.ge', 'GT.gt'}: a, b = b, a
        strict = term['symbol'] in {'LT.lt', 'GT.gt'}
        if negate: a, b, strict = b, a, not strict
        form = combine(arithmetic(a), arithmetic(b)); form = (form[0], form[1]+int(strict)); relation = 'le'
    else:
        raise ValueError('Unsupported proposition in arithmetic projection')
    return {'name': name, 'relation': relation, 'constant': str(form[1]),
            'terms': [{'variable': k, 'coefficient': str(v)} for k, v in sorted(form[0].items())]}


def project(final_ir):
    """The independent projection of the final IR: included rows in IR order, the omitted hypotheses with their reasons, and the
    negated goal. The goal must be expressible; an inexpressible hypothesis is omitted."""
    rows, omitted = [], []
    for h in final_ir['context']['hypotheses']:
        try: rows.append(row(h['name'], h['shell']))
        except ValueError as error: omitted.append({'name': h['name'], 'reason': str(error)})
    try: goal = row('neg_goal', final_ir['goal']['shell'], True)
    except ValueError as error: raise Refusal('policy_goal_inexpressible', str(error))
    return rows+[goal], omitted


def admit(prepared):
    """Policy C over a prepared problem. Returns the posable rows and the evaluator-only record of what the rows leave out."""
    rows, omitted = project(prepared['final_ir'])
    if [o['name'] for o in omitted] != list(prepared['farkas_omissions']):
        raise Refusal('policy_omissions_differ', f"derived {[o['name'] for o in omitted]}, SDK {prepared['farkas_omissions']}")
    if rows != prepared['rows']: raise Refusal('policy_rows_differ', 'SDK rows differ from the independent projection')
    names = [r['name'] for r in rows]
    duplicates = sorted({n for n in names if names.count(n) > 1})
    if duplicates: raise Refusal('policy_ambiguous_reference', ', '.join(duplicates))
    if names.count('neg_goal') != 1 or names[-1] != 'neg_goal': raise Refusal('policy_neg_goal', 'exactly one final neg_goal row')
    for r in rows:
        variables = [t['variable'] for t in r['terms']]
        if r['relation'] not in ('le', 'eq') or not INTEGER.fullmatch(r['constant']) or variables != sorted(set(variables)) \
                or not all(INTEGER.fullmatch(t['coefficient']) and t['coefficient'] != '0' for t in r['terms']):
            raise Refusal('policy_row_noncanonical', r['name'])
    return rows, {'source_fragment': prepared['fragment'], 'omitted': omitted, 'omitted_names': [o['name'] for o in omitted],
                  'posed_fragment': 'LIA', 'input_ir_sha256': events.digest(prepared['input_ir']), 'final_ir_sha256': events.digest(prepared['final_ir'])}
