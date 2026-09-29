"""Explicit, separately validated projections for R6-001.

The model-facing request contains compiled arithmetic rows only. The Lean
context projection is evaluator reference data, separately hashed and audited.
Proof-body exclusion never removes the type of a legitimate let-bound fact.
"""
import json
import re

import jsonschema
import events
import run as r6

CONTRACT = r6.ROOT/'policies/fixture-farkas-v1.json'
FIELDS = {'name', 'type', 'binder_info', 'index'}


def strict_json(text):
    def pairs(items):
        out = {}
        for key, value in items:
            if key in out:
                raise ValueError('Duplicate JSON field: '+key)
            out[key] = value
        return out
    def constant(value):
        raise ValueError('Non-JSON constant: '+value)
    return json.loads(text, object_pairs_hook=pairs, parse_constant=constant)


def no_proof_material(value):
    if isinstance(value, dict):
        for key, child in value.items():
            if key == 'value':
                raise ValueError('Proof-body value field is forbidden in payload projections')
            no_proof_material(key)
            no_proof_material(child)
    elif isinstance(value, list):
        for child in value:
            no_proof_material(child)
    elif isinstance(value, str) and ('_proof_' in value or 'declaration_placeholder' in value):
        raise ValueError('Proof auxiliary or declaration placeholder in payload projection')


def validate_context(projected, original):
    if set(projected) != {'target', 'hypotheses'} or projected['target'] != original['target']:
        raise ValueError('Context projection target or fields changed')
    allowed = {row['index']: row for row in original['telescope'] if row['kind'] != 'declaration_placeholder'}
    rows = projected['hypotheses']
    if not isinstance(rows, list) or len(rows) != len(allowed):
        raise ValueError('Context projection dropped a genuine binder or let fact')
    seen = set()
    for row in rows:
        if not isinstance(row, dict) or set(row) != FIELDS:
            raise ValueError('Context projection is not the four-field allowlist')
        index = row['index']
        if type(index) is not int or index in seen or index not in allowed:
            raise ValueError('Duplicate, unknown, or declaration-placeholder context entry')
        seen.add(index)
        if any(row[k] != allowed[index][k] for k in FIELDS):
            raise ValueError('Context projection changed a binder or fact type')
    if [r['index'] for r in rows] != list(allowed):
        raise ValueError('Context projection changed binder order')
    no_proof_material(projected)


def project_context(original):
    result = {'target': original['target'], 'hypotheses': [
        {key: row[key] for key in sorted(FIELDS)} for row in original['telescope']
        if row['kind'] != 'declaration_placeholder']}
    validate_context(result, original)
    return result


def request(task, prepared):
    if prepared['fragment'] != 'LIA' or prepared['farkas_omissions']:
        raise ValueError('Initial policy requires LIA rows without further Farkas compilation omissions')
    if prepared['rows'] != arithmetic_rows(prepared['final_ir']):
        raise ValueError('SDK rows differ from independent arithmetic projection')
    result = {'schema_version': 'r6-farkas-request-1',
        'policy_sha256': r6.sha(CONTRACT),
        'binding': {'task_id': task.id, 'manifest_sha256': r6.sha(task.path/'manifest.json'),
                    'challenge_sha256': r6.read_json(task.path/'expected.json')['challenge_sha256'],
                    'input_ir_sha256': events.digest(prepared['input_ir']),
                    'final_ir_sha256': events.digest(prepared['final_ir'])},
        'problem': {'fragment': prepared['fragment'], 'rows': prepared['rows']}}
    validate_request(result)
    return result


def validate_request(value):
    jsonschema.validate(value, r6.read_json(r6.ROOT/'schema/proposal-request.schema.json'))
    no_proof_material(value)
    names = [row['name'] for row in value['problem']['rows']]
    if len(names) != len(set(names)) or names.count('neg_goal') != 1:
        raise ValueError('Ambiguous arithmetic input references')
    for row in value['problem']['rows']:
        terms = [t['variable'] for t in row['terms']]
        if terms != sorted(set(terms)):
            raise ValueError('Arithmetic row variables are not canonical')


def response(raw, request_bytes):
    config = r6.read_json(CONTRACT)
    if len(raw) > config['request_output_bytes']:
        raise ValueError('Response exceeds frozen byte budget')
    value = strict_json(raw)
    jsonschema.validate(value, r6.read_json(r6.ROOT/'schema/proposal-response.schema.json'))
    if value['request_sha256'] != r6.hashlib.sha256(request_bytes).hexdigest():
        raise ValueError('Response is bound to a different request')
    given = strict_json(request_bytes)
    allowed = {row['name'] for row in given['problem']['rows']}
    coefficients = value['witness']['coefficients']
    names = [row['hypothesis'] for row in coefficients]
    if len(names) != len(set(names)) or not set(names) <= allowed:
        raise ValueError('Unknown or repeated witness hypothesis')
    if len(coefficients) > config['maximum_support']:
        raise ValueError('Witness exceeds frozen support budget')
    for row in coefficients:
        literal = row['coefficient']
        if len(literal) > config['maximum_coefficient_characters'] or not re.fullmatch(r'-?(0|[1-9][0-9]*)', literal):
            raise ValueError('Coefficient is outside the frozen integer grammar')
    # Mathematical correctness is intentionally not decided here.
    return value


def arithmetic_rows(ir):
    """Independent integer polynomial projection for the frozen LIA interface.

    Unsupported syntax fails closed. This is a consistency check on the payload,
    not a replacement for the SDK verifier or the Lean reconstruction/kernel.
    """
    def add(a, b, scale=1):
        terms = a[0].copy()
        for name, coefficient in b[0].items():
            terms[name] = terms.get(name, 0)+scale*coefficient
        return {k: v for k, v in terms.items() if v}, a[1]+scale*b[1]
    def mul(a, n):
        return {k: v*n for k, v in a[0].items() if v*n}, a[1]*n
    def arithmetic(node):
        kind = node['node']
        if kind == 'NumLit':
            if node['type'] not in {'Int', 'Nat'} or not re.fullmatch(r'-?(0|[1-9][0-9]*)', node['value']):
                raise ValueError('Noninteger arithmetic input')
            return {}, int(node['value'])
        if kind in {'Var', 'Opaque'}:
            return {node['name'] if kind == 'Var' else node['payload_id']: 1}, 0
        if kind != 'App':
            raise ValueError('Unsupported arithmetic input')
        symbol, args = node['symbol'], node['args']
        if symbol == 'Int.ofNat' and len(args) == 1:
            return arithmetic(args[0])
        if symbol in {'Neg.neg', 'Int.neg'} and len(args) == 1:
            return mul(arithmetic(args[0]), -1)
        if len(args) != 2:
            raise ValueError('Unsupported arithmetic arity')
        a, b = map(arithmetic, args)
        if symbol in {'HAdd.hAdd', 'Int.add', 'Add.add'}:
            return add(a, b)
        if symbol in {'HSub.hSub', 'Int.sub', 'Sub.sub'}:
            return add(a, b, -1)
        if symbol in {'HMul.hMul', 'Int.mul', 'Mul.mul'}:
            if not a[0]: return mul(b, a[1])
            if not b[0]: return mul(a, b[1])
        raise ValueError('Unsupported or nonlinear arithmetic input')
    def compile_row(name, term, negate=False):
        if term['node'] == 'Eq' and not negate:
            form, relation = add(arithmetic(term['left']), arithmetic(term['right']), -1), 'eq'
        elif term['node'] == 'App' and term['symbol'] in {'LE.le', 'LT.lt', 'GE.ge', 'GT.gt'}:
            a, b = term['args']
            if term['symbol'] in {'GE.ge', 'GT.gt'}: a, b = b, a
            strict = term['symbol'] in {'LT.lt', 'GT.gt'}
            if negate: a, b, strict = b, a, not strict
            form = add(arithmetic(a), arithmetic(b), -1)
            form = (form[0], form[1]+int(strict))
            relation = 'le'
        else:
            raise ValueError('Unsupported proposition in arithmetic projection')
        return {'name': name, 'relation': relation, 'constant': str(form[1]),
                'terms': [{'variable': k, 'coefficient': str(v)} for k, v in sorted(form[0].items())]}
    return [*[compile_row(h['name'], h['shell']) for h in ir['context']['hypotheses']],
            compile_row('neg_goal', ir['goal']['shell'], True)]
