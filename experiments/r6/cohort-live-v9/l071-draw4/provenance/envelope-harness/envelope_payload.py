"""Exact message construction, post-serialization audit, and narrow binding claims."""
import copy
import hashlib
import json

import envelope_contract as contract
import events
import payload as legacy
import run as r6

PREFIX = 'Request SHA-256: '
SEPARATOR = '\nRequest JSON (exact UTF-8 bytes follow):\n'


class BoundaryFailure(ValueError):
    def __init__(self, category, stage, detail, evidence=None):
        super().__init__(detail)
        self.category, self.stage = category, stage
        self.phase = contract.PHASES[stage]
        self.evidence = evidence


def sha(data):
    return hashlib.sha256(data).hexdigest()


def context(original, projected=None):
    allowed = {'target': original['target'], 'hypotheses': [
        {key: row[key] for key in sorted(legacy.FIELDS)} for row in original['telescope']
        if row['kind'] != 'declaration_placeholder']}
    projected = allowed if projected is None else projected
    if events.canonical(projected) != events.canonical(allowed):
        raise BoundaryFailure('payload_integrity_failure', 'context-admission',
                              'Context projection differs from the complete field allowlist')
    barred = []
    def inspect(value, path):
        if isinstance(value, dict):
            for key, child in value.items(): inspect(child, path+'/'+key)
        elif isinstance(value, list):
            for index, child in enumerate(value): inspect(child, path+'/'+str(index))
        elif isinstance(value, str) and ('_proof_' in value or 'declaration_placeholder' in value):
            barred.append({'field': path, 'field_sha256': sha(value.encode())})
    inspect(allowed, '')
    if barred:
        raise BoundaryFailure('context_admission_review_required', 'context-admission',
            'Original context contains a barred auxiliary/reference; task admission needs review',
            {'source_context_sha256': events.digest(original), 'fields': barred})
    try:
        legacy.validate_context(projected, original)
    except (ValueError, TypeError, KeyError) as error:
        raise BoundaryFailure('payload_integrity_failure', 'context-admission', str(error)) from error
    return projected


def request(task, prepared):
    # Reuse the frozen arithmetic projection/shape checks, then add the new
    # policy and prompt binding. No source types or proof bodies are sent.
    value = legacy.request(task, prepared)
    value['schema_version'] = 'r6-farkas-request-2'
    value['policy_sha256'] = r6.sha(contract.CONFIG)
    value['binding']['prompt_sha256'] = contract.config()['prompt_sha256']
    validate_request(value)
    return events.canonical(value)+b'\n'


def validate_request(value):
    r6.jsonschema.validate(value, r6.read_json(r6.ROOT/'schema/envelope-request.schema.json'))
    if value['policy_sha256'] != r6.sha(contract.CONFIG) or value['binding']['prompt_sha256'] != r6.sha(contract.PROMPT):
        raise BoundaryFailure('request_binding_failure', 'payload', 'Frozen policy/prompt binding differs')
    old = copy.deepcopy(value)
    old['schema_version'] = 'r6-farkas-request-1'
    old['binding'].pop('prompt_sha256')
    legacy.validate_request(old)


def arguments(request_bytes):
    value = legacy.strict_json(request_bytes)
    validate_request(value)
    if request_bytes != events.canonical(value)+b'\n':
        raise BoundaryFailure('request_binding_failure', 'payload', 'Request bytes are not canonical')
    prompt = contract.PROMPT.read_bytes()
    user = PREFIX+sha(request_bytes)+SEPARATOR+request_bytes.decode('utf-8')
    return {'schema_version': 'r6-model-messages-1', 'messages': [
        {'role': 'system', 'content': prompt.decode('utf-8')}, {'role': 'user', 'content': user}]}


def serialize(arguments, *, variant='standard'):
    """Local canned serializer, not a claim about any provider SDK or HTTP body."""
    if variant == 'standard':
        return (json.dumps(arguments, ensure_ascii=True, indent=2)+'\n').encode()
    if variant == 'alternate':
        return events.canonical(arguments)+b'\n'
    raise ValueError('Unknown serialization variant')


def audit_envelope(captured_bytes, request_bytes):
    try:
        if len(captured_bytes) > contract.config()['maximum_request_bytes']:
            raise ValueError('Serialized envelope exceeds byte limit')
        captured = legacy.strict_json(captured_bytes)
        expected = arguments(request_bytes)
        if events.canonical(captured) != events.canonical(expected):
            raise ValueError('Serialized messages differ from the frozen prompt and exact request bytes')
    except (ValueError, UnicodeError, r6.jsonschema.ValidationError) as error:
        raise BoundaryFailure('outbound_envelope_binding', 'envelope-audit', str(error)) from error
    return {'accepted': True, 'prompt_sha256': r6.sha(contract.PROMPT), 'request_sha256': sha(request_bytes),
        'captured_envelope_sha256': sha(captured_bytes), 'messages_sha256': events.digest(captured['messages']),
        'evidence_scope': 'local serialized-envelope consistency; no model-input or inference attestation'}


def response(raw, request_bytes):
    try:
        if len(raw) > contract.config()['maximum_response_bytes']:
            raise ValueError('Response exceeds byte budget')
        value = legacy.strict_json(raw)
        r6.jsonschema.validate(value, r6.read_json(r6.ROOT/'schema/proposal-response.schema.json'))
    except (ValueError, UnicodeError, r6.jsonschema.ValidationError) as error:
        raise BoundaryFailure('response_decode', 'response-decode', str(error)) from error
    if value['request_sha256'] != sha(request_bytes):
        raise BoundaryFailure('transport_binding_failure', 'response-binding',
            'Response request digest does not match the recorded request bytes',
            {'expected_request_sha256': sha(request_bytes), 'received_request_sha256': value['request_sha256']})
    try:
        # The frozen response checker also checks support and integer grammar.
        legacy.response(raw, request_bytes)
    except (ValueError, r6.jsonschema.ValidationError) as error:
        raise BoundaryFailure('response_decode', 'response-decode', str(error)) from error
    return value


def echo(raw, request_bytes):
    """A deliberately narrow check, independent of envelope and witness validity."""
    try:
        if len(raw) > contract.config()['maximum_response_bytes']:
            raise ValueError('Oversized response')
        value = legacy.strict_json(raw)
        received = value['request_sha256']
        if not isinstance(received, str): raise ValueError('Digest field is not a string')
    except (ValueError, TypeError, KeyError, UnicodeError):
        return {'checked': False, 'accepted': None, 'scope': 'response_request_association'}
    return {'checked': True, 'accepted': received == sha(request_bytes),
            'scope': 'response_request_association', 'expected_request_sha256': sha(request_bytes),
            'received_request_sha256': received}


def usage(provider_report=None):
    """Unknown fields remain null. Explicit zero is a separately reported value."""
    report = {} if provider_report is None else provider_report
    if not isinstance(report, dict) or set(report)-{'input_tokens', 'output_tokens', 'total_tokens'}:
        raise BoundaryFailure('usage_decode', 'response-decode', 'Unsupported reported usage fields')
    result = {}
    for key in ('input_tokens', 'output_tokens', 'total_tokens'):
        value = report.get(key)
        if value is not None and (type(value) is not int or value < 0):
            raise BoundaryFailure('usage_decode', 'response-decode', 'Usage must be a nonnegative integer or unknown')
        result[key] = value
    if all(v is not None for v in result.values()) and result['total_tokens'] != result['input_tokens']+result['output_tokens']:
        raise BoundaryFailure('usage_decode', 'response-decode', 'Reported token counts disagree')
    return {**result, 'cost_usd': None, 'status': 'unreported' if not report else 'provider_reported'}
