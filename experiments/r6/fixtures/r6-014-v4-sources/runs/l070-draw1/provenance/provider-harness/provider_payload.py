"""LIA admission, component diagnostics and strict Responses decoding."""
import copy
import hashlib
import json

import envelope_payload as old
import events
import payload as legacy
import provider_contract as contract
import run as r6

PREFIX, SEPARATOR = old.PREFIX, old.SEPARATOR
MISSING = object()


class Failure(ValueError):
    def __init__(self, category, stage, detail, evidence=None):
        super().__init__(detail)
        self.category, self.stage, self.evidence = category, stage, evidence
        self.phase = contract.PHASES[stage]


def sha(data): return hashlib.sha256(data).hexdigest()


def admit(prepared):
    bad = prepared['fragment'] != 'LIA' or any(r['relation'] not in {'le', 'eq'} for r in prepared['rows'])
    def real(value):
        if isinstance(value, dict):
            return value.get('type') == 'Real' or any(real(x) for x in value.values())
        return isinstance(value, list) and any(real(x) for x in value)
    for key in ['input_ir', 'final_ir']:
        ir = prepared[key]
        bad |= real(ir) or any(v['type'] not in {'Nat', 'Int'} for v in ir['context']['free_vars'])
        bad |= ir['logic_classification']['first_order_fragment'] == 'LRA'
    if bad:
        raise Failure('unsupported_theory', 'provider-admission', 'First provider policy requires integer le/eq rows; non-LIA or strict rows need admission')


def request(task, prepared):
    admit(prepared)
    value = legacy.request(task, prepared)
    value['schema_version'] = 'r6-farkas-request-3'
    value['policy_sha256'] = r6.sha(contract.CONFIG)
    value['binding']['prompt_sha256'] = r6.sha(contract.PROMPT)
    validate_request(value)
    return events.canonical(value)+b'\n'


def validate_request(value):
    if any(r.get('relation') not in {'le', 'eq'} for r in value.get('problem', {}).get('rows', [])):
        raise Failure('unsupported_theory', 'provider-admission', 'Request contains an unadmitted row relation')
    r6.jsonschema.validate(value, r6.read_json(r6.ROOT/'schema/provider-request.schema.json'))
    if value['policy_sha256'] != r6.sha(contract.CONFIG) or value['binding']['prompt_sha256'] != r6.sha(contract.PROMPT):
        raise Failure('request_binding_failure', 'payload', 'Frozen provider policy/prompt binding differs')
    prior = copy.deepcopy(value); prior['schema_version'] = 'r6-farkas-request-1'; prior['binding'].pop('prompt_sha256')
    legacy.validate_request(prior)


def arguments(request):
    value = legacy.strict_json(request); validate_request(value)
    if request != events.canonical(value)+b'\n': raise Failure('request_binding_failure', 'payload', 'Noncanonical request bytes')
    c = contract.config()
    return {'model': c['wire_model'], 'input': [
        {'role': 'system', 'content': contract.PROMPT.read_text()},
        {'role': 'user', 'content': PREFIX+sha(request)+SEPARATOR+request.decode()}],
        'store': False, 'stream': False, 'background': False, 'tools': [], 'tool_choice': 'none',
        'parallel_tool_calls': False, 'truncation': 'disabled', 'max_output_tokens': c['max_output_tokens']}


def fingerprint(value):
    if value is MISSING: return {'present': False, 'type': None, 'bytes': None, 'sha256': None}
    raw = value if isinstance(value, bytes) else value.encode() if isinstance(value, str) else events.canonical(value)
    return {'present': True, 'type': 'bytes' if isinstance(value, bytes) else type(value).__name__, 'bytes': len(raw), 'sha256': sha(raw)}


def envelope_report(captured, request):
    expected = arguments(request)
    differences = []
    def compare(component, a, b):
        x, y = fingerprint(a), fingerprint(b)
        if x != y: differences.append({'component': component, 'expected': x, 'observed': y})
    try:
        if len(captured) > contract.config()['maximum_request_bytes']: raise ValueError('Envelope exceeds byte limit')
        actual = legacy.strict_json(captured)
        if not isinstance(actual, dict): raise ValueError('Envelope is not an object')
    except (ValueError, UnicodeError) as error:
        differences.append({'component': 'envelope_decode', 'expected': fingerprint(expected),
                            'observed': fingerprint(captured), 'detail': str(error)[:512]})
    else:
        compare('request_options', {k:v for k,v in expected.items() if k != 'input'},
                {k:v for k,v in actual.items() if k != 'input'})
        inputs = actual.get('input', MISSING)
        def layout(items):
            if not isinstance(items, list): return items
            return [{'role': item.get('role'), 'fields': sorted(item)} if isinstance(item, dict) else item for item in items]
        compare('message_layout', layout(expected['input']), layout(inputs))
        def content(role):
            if not isinstance(inputs, list): return MISSING
            rows = [x for x in inputs if isinstance(x, dict) and x.get('role') == role]
            return rows[0].get('content', MISSING) if len(rows) == 1 else MISSING
        compare('system_message', expected['input'][0]['content'], content('system'))
        user = content('user')
        if isinstance(user, str):
            head, separator, tail = user.partition(SEPARATOR)
            observed_prefix, observed_suffix = head+separator, tail if separator else MISSING
        else: observed_prefix = observed_suffix = user
        compare('user_prefix', PREFIX+sha(request)+SEPARATOR, observed_prefix)
        compare('request_suffix', request.decode(), observed_suffix)
    return {'accepted': not differences, 'category': None if not differences else 'outbound_envelope_binding',
        'mismatches': differences, 'captured_body_sha256': sha(captured), 'request_sha256': sha(request),
        'prompt_sha256': r6.sha(contract.PROMPT),
        'evidence_scope': 'observed HTTP body consistency; no remote-input or inference attestation'}


def check_envelope(captured, request):
    report = envelope_report(captured, request)
    if not report['accepted']:
        raise Failure('outbound_envelope_binding', 'envelope-audit',
            'Envelope components differ: '+', '.join(x['component'] for x in report['mismatches']), report)
    return report


def usage(response):
    value = response.get('usage')
    if value is None: value = {}
    if not isinstance(value, dict): raise Failure('usage_decode', 'provider-response', 'Usage is not an object or null')
    result = {'status': 'unreported' if not value else 'provider_reported', 'cost_usd': None}
    for field in ['input_tokens', 'output_tokens', 'total_tokens']:
        n = value.get(field)
        if n is not None and (type(n) is not int or n < 0): raise Failure('usage_decode', 'provider-response', 'Invalid '+field)
        result[field] = n
    for parent, key in [('input_tokens_details', 'cached_tokens'), ('output_tokens_details', 'reasoning_tokens')]:
        detail = value.get(parent)
        if detail is None: detail = {}
        if not isinstance(detail, dict): raise Failure('usage_decode', 'provider-response', 'Invalid token details')
        n = detail.get(key)
        if n is not None and (type(n) is not int or n < 0): raise Failure('usage_decode', 'provider-response', 'Invalid '+key)
        result[key] = n
    known = [result[k] for k in ['input_tokens','output_tokens','total_tokens']]
    if all(x is not None for x in known) and known[0]+known[1] != known[2]:
        raise Failure('usage_decode', 'provider-response', 'Reported token totals disagree')
    for sub, parent in [('cached_tokens','input_tokens'),('reasoning_tokens','output_tokens')]:
        if result[sub] is not None and result[parent] is not None and result[sub] > result[parent]:
            raise Failure('usage_decode', 'provider-response', 'Reported token detail exceeds its total')
    return result


def provider_response(raw, status):
    if status != 200:
        raise Failure('provider_http_error', 'provider-response', 'Provider HTTP status '+str(status), {'status': status})
    try:
        if len(raw) > contract.config()['maximum_provider_response_bytes']: raise ValueError('Provider response too large')
        obj = legacy.strict_json(raw)
        if not isinstance(obj, dict) or obj.get('object') != 'response': raise ValueError('Missing Responses object')
    except (ValueError, UnicodeError) as error:
        raise Failure('provider_decode', 'provider-response', str(error)) from error
    reported = usage(obj)
    if obj.get('status') == 'incomplete':
        raise Failure('provider_incomplete', 'provider-response', 'Provider response is incomplete', {'usage': reported, 'incomplete_details': obj.get('incomplete_details')})
    if obj.get('status') != 'completed' or obj.get('error') is not None:
        raise Failure('provider_status', 'provider-response', 'Provider response is not completed successfully', {'usage': reported})
    if obj.get('model') != contract.MODEL:
        raise Failure('provider_model_binding', 'provider-response', 'Reported model differs from requested wire model', {'usage': reported})
    output = obj.get('output')
    if not isinstance(output, list): raise Failure('provider_decode', 'provider-response', 'Output is not an array')
    messages = []
    for item in output:
        if not isinstance(item, dict): raise Failure('provider_decode', 'provider-response', 'Output item is not an object')
        if item.get('type') == 'reasoning': continue
        if item.get('type') != 'message' or item.get('role') != 'assistant' or item.get('status') != 'completed':
            raise Failure('provider_output_shape', 'provider-response', 'Unexpected provider output item', {'usage': reported})
        messages.append(item)
    if len(messages) != 1: raise Failure('provider_output_shape', 'provider-response', 'Expected exactly one completed assistant message', {'usage': reported})
    content = messages[0].get('content')
    if not isinstance(content, list): raise Failure('provider_decode', 'provider-response', 'Message content is not an array')
    parts = []
    for part in content:
        if isinstance(part, dict) and part.get('type') == 'refusal':
            raise Failure('provider_refusal', 'provider-response', 'Provider returned a refusal', {'usage': reported})
        if not isinstance(part, dict) or part.get('type') != 'output_text' or not isinstance(part.get('text'), str):
            raise Failure('provider_output_shape', 'provider-response', 'Unexpected assistant content', {'usage': reported})
        parts.append(part['text'])
    if not parts: raise Failure('provider_output_shape', 'provider-response', 'No output text', {'usage': reported})
    if reported['output_tokens'] is not None and reported['output_tokens'] > contract.config()['max_output_tokens']:
        raise Failure('provider_output_budget', 'provider-response', 'Reported output exceeds requested limit', {'usage': reported})
    return ''.join(parts).encode(), {'response_id': obj.get('id'), 'model': obj['model'], 'status': obj['status'],
        'usage': reported, 'output_text_parts': len(parts), 'reasoning_items': sum(x.get('type') == 'reasoning' for x in output),
        'identity_scope': 'provider-reported fields; no model-computation attestation'}


def response(raw, request):
    try: return old.response(raw, request)
    except old.BoundaryFailure as error:
        raise Failure(error.category, error.stage, str(error), error.evidence) from error


def transport(outbound, captured, raw, http, request):
    """Recompute each predicate from bytes, preserving unobserved results."""
    envelope = envelope_report(captured if captured is not None else outbound, request)
    envelope['observation'] = 'local_server_received' if captured is not None else 'client_serialized_only'
    consistency = {'checked': captured is not None, 'accepted': None if captured is None else captured == outbound}
    echo = {'checked': False, 'accepted': None, 'scope': 'response_request_association'}
    proposed = text = metadata = None
    failure = None
    provider = {'accepted': None, 'failure_category': None}
    response_ok, response_failure = None, None
    if http['failure_category']:
        failure = Failure(http['failure_category'], 'proposal-1', 'HTTP adapter: '+http['failure_category'])
    elif raw is None:
        failure = Failure('transport_capture_failure', 'proposal-1', 'Completed HTTP attempt lacks a response body')
    else:
        try:
            text, metadata = provider_response(raw, http['http_status'])
            provider['accepted'] = True
        except Failure as error:
            failure = error
            provider = {'accepted': False, 'failure_category': error.category}
            metadata = {'usage': error.evidence['usage']} if isinstance(error.evidence, dict) and 'usage' in error.evidence else None
        if text is not None:
            echo = old.echo(text, request)
            try: proposed = response(text, request); response_ok = True
            except Failure as error:
                failure = error; response_ok = False; response_failure = error.category
    validation = {'outbound_envelope': envelope, 'capture_consistency': consistency,
        'provider_response': provider, 'response_request_binding': echo,
        'response_validated': response_ok, 'response_failure_category': response_failure,
        'evidence_scope': 'local HTTP observations; no remote receipt, compilation or inference attestation'}
    if consistency['accepted'] is False:
        failure = Failure('transport_capture_failure', 'envelope-audit', 'Server capture differs from client body', consistency)
    elif not envelope['accepted']:
        failure = Failure('outbound_envelope_binding', 'envelope-audit',
            'Envelope components differ: '+', '.join(x['component'] for x in envelope['mismatches']), envelope)
    elif captured is None and not http['failure_category']:
        failure = Failure('transport_capture_failure', 'envelope-audit', 'Successful HTTP exchange lacks server capture')
    return proposed, text, metadata, validation, failure
