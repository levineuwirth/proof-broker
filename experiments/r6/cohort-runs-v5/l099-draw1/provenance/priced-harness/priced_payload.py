"""New request binding and Responses options; old arithmetic grammar unchanged."""
import copy
import json
from pathlib import Path

import envelope_payload
import events
import priced_contract as contract
import pricing_gate
import payload
import provider_payload as previous
import run as r6

sha = contract.bytes_hash


class Failure(ValueError):
    def __init__(self, category, phase, message):
        super().__init__(message)
        self.category, self.phase = category, phase


def request(task, prepared):
    # The frozen producer independently checks IR/row agreement and admission.
    value = payload.strict_json(previous.request(task, prepared))
    value['schema_version'] = 'r6-farkas-request-6'
    value['policy_sha256'] = r6.sha(contract.CONFIG)
    return events.canonical(value)+b'\n'


def arguments(request_bytes):
    opts = copy.deepcopy(contract.config()['request'])
    opts['input'] = [{'role': 'system', 'content': contract.PROMPT.read_text()},
        {'role': 'user', 'content': previous.PREFIX+sha(request_bytes)+previous.SEPARATOR+request_bytes.decode()}]
    return opts


def envelope_report(body, request_bytes):
    """Use frozen fingerprint semantics with this policy's own expected bytes."""
    expected=arguments(request_bytes); differences=[]; missing=previous.MISSING
    def compare(component,a,b):
        x,y=previous.fingerprint(a),previous.fingerprint(b)
        if x!=y: differences.append({'component':component,'expected':x,'observed':y})
    try:
        if len(body)>contract.config()['limits']['maximum_request_bytes']: raise ValueError('Envelope exceeds limit')
        actual=payload.strict_json(body)
        if not isinstance(actual,dict): raise ValueError('Envelope is not an object')
    except (ValueError,UnicodeError):
        differences.append({'component':'envelope_decode','expected':previous.fingerprint(expected),
                            'observed':previous.fingerprint(body)})
    else:
        compare('request_options',{k:v for k,v in expected.items() if k!='input'},
                {k:v for k,v in actual.items() if k!='input'})
        inputs=actual.get('input',missing)
        def layout(items):
            if not isinstance(items,list): return items
            return [{'role':item.get('role'),'fields':sorted(item)} if isinstance(item,dict) else item for item in items]
        compare('message_layout',layout(expected['input']),layout(inputs))
        def content(role):
            if not isinstance(inputs,list): return missing
            rows=[x for x in inputs if isinstance(x,dict) and x.get('role')==role]
            return rows[0].get('content',missing) if len(rows)==1 else missing
        compare('system_message',expected['input'][0]['content'],content('system'))
        user=content('user')
        if isinstance(user,str):
            head,separator,tail=user.partition(previous.SEPARATOR)
            prefix,suffix=head+separator,tail if separator else missing
        else: prefix=suffix=user
        compare('user_prefix',previous.PREFIX+sha(request_bytes)+previous.SEPARATOR,prefix)
        compare('request_suffix',request_bytes.decode(),suffix)
    return {'accepted':not differences,'category':'outbound_envelope_binding' if differences else None,
        'mismatches':differences,'captured_body_sha256':sha(body),'request_sha256':sha(request_bytes),
        'prompt_sha256':r6.sha(contract.PROMPT),'policy_sha256':r6.sha(contract.CONFIG),
        'evidence_scope':'local serialized entity-body consistency; no remote-input or inference attestation'}


def response(raw, status):
    c = contract.config()
    if status != 200: raise Failure('provider_http_error', 'provider_response', 'HTTP status '+str(status))
    try:
        obj = payload.strict_json(raw)
        if not isinstance(obj, dict) or obj.get('object') != 'response': raise ValueError()
    except (ValueError, UnicodeError): raise Failure('provider_decode', 'provider_response', 'Invalid Responses object')
    # Usage is independently checked even for incomplete or refused responses.
    try: usage = previous.usage(obj)
    except previous.Failure: raise Failure('usage_decode', 'provider_response', 'Malformed usage')
    if obj.get('model') not in c['model']['allowed_response_ids']:
        raise Failure('provider_model_binding', 'provider_response', 'Reported model is outside the frozen allowlist')
    if obj.get('service_tier') != c['request']['service_tier']:
        raise Failure('provider_service_tier', 'provider_response', 'Reported service tier differs from frozen pricing tier')
    if obj.get('status') == 'incomplete': raise Failure('provider_incomplete', 'provider_response', 'Provider response incomplete')
    if obj.get('status') != 'completed' or obj.get('error') is not None:
        raise Failure('provider_status', 'provider_response', 'Provider response not completed')
    if usage['output_tokens'] is not None and usage['output_tokens'] > c['limits']['output_tokens']:
        raise Failure('provider_output_budget', 'provider_response', 'Reported output exceeds reservation')
    if usage['input_tokens'] is not None and usage['input_tokens'] > c['limits']['input_tokens_reserved']:
        raise Failure('provider_input_budget', 'provider_response', 'Reported input exceeds reservation')
    output = obj.get('output')
    if not isinstance(output, list) or any(not isinstance(x, dict) for x in output):
        raise Failure('provider_output_shape', 'provider_response', 'Output is not an object array')
    messages = [x for x in output if x.get('type') != 'reasoning']
    if len(messages) != 1 or any(messages[0].get(k) != v for k, v in
            {'type':'message', 'role':'assistant', 'status':'completed'}.items()):
        raise Failure('provider_output_shape', 'provider_response', 'Expected one completed assistant message')
    parts = messages[0].get('content')
    if not isinstance(parts, list) or not parts: raise Failure('provider_output_shape', 'provider_response', 'Missing text')
    if any(isinstance(p, dict) and p.get('type') == 'refusal' for p in parts):
        raise Failure('provider_refusal', 'provider_response', 'Provider refusal')
    if any(not isinstance(p, dict) or p.get('type') != 'output_text' or not isinstance(p.get('text'), str) for p in parts):
        raise Failure('provider_output_shape', 'provider_response', 'Unexpected content')
    return ''.join(p['text'] for p in parts).encode(), {
        'response_id': obj.get('id'), 'reported_model': obj['model'], 'reported_service_tier': obj['service_tier'],
        'usage': usage, 'scope': 'canned provider-reported fields; no model revision or computation attestation'}


def interpret(root, request_bytes):
    """Every predicate is recomputed; a skipped certificate result is null."""
    out = Path(root)
    http = r6.read_json(out/'http.json')
    body = (out/'serialized-body.json').read_bytes()
    envelope = envelope_report(body, request_bytes)
    sent = (out/'outbound-body.json').read_bytes() if (out/'outbound-body.json').exists() else None
    received = (out/'received-body.json').read_bytes() if (out/'received-body.json').exists() else None
    consistency = {'checked': sent is not None and received is not None,
        'accepted': None if sent is None or received is None else sent == received == body}
    text = proposed = metadata = None
    error = None
    echo = {'checked': False, 'accepted': None, 'scope': 'response_request_association'}
    if http['failure_category']:
        error = Failure(http['failure_category'], 'pricing_admission' if http['failure_category']=='pricing_admission' else 'https_transport', 'Pricing admission: '+http['pricing_failure_code'] if http['failure_category']=='pricing_admission' else 'HTTPS adapter: '+http['failure_category'])
    else:
        try:
            text, metadata = response((out/'provider-response.json').read_bytes(), http['http_status'])
            echo = envelope_payload.echo(text, request_bytes)
            proposed = envelope_payload.response(text, request_bytes)
        except Failure as failure: error = failure
        except envelope_payload.BoundaryFailure as failure:
            error = Failure(failure.category, 'proposal', str(failure))
    if not envelope['accepted'] and http['failure_category'] != 'pricing_admission':
        error = Failure('outbound_envelope_binding', 'proposal', 'Envelope components differ: '+', '.join(x['component'] for x in envelope['mismatches']))
    elif consistency['accepted'] is False:
        error = Failure('transport_capture_failure', 'https_transport', 'Send/receive entity bodies differ')
    return proposed, text, metadata, {'outbound_envelope': envelope, 'body_consistency': consistency,
        'response_request_binding': echo, 'certificate_verified': None,
        'failure_category': error.category if error else None, 'failure_phase': error.phase if error else None}, error


def reservation(arguments_value, spent=0, attempts=0):
    c = contract.config(); limits = c['limits']
    if attempts >= limits['attempts_per_episode']: raise Failure('request_budget_exhaustion', 'admission', 'Request budget exhausted')
    size = sum(len(m['content'].encode()) for m in arguments_value['input'])
    if size > limits['message_utf8_bytes']: raise Failure('input_byte_budget', 'admission', 'Messages exceed frozen byte admission')
    # Integer micro-USD; rate ceiling includes cache writes and counts every
    # reserved attempt even when transport failed or usage is unavailable.
    rate = c['pricing']['nano_usd_per_token']
    reserve = pricing_gate.cost_micro(limits['input_tokens_reserved'], limits['output_tokens'], rate)
    if spent+reserve > limits['total_micro_usd']:
        raise Failure('monetary_budget_exhaustion', 'admission', 'Monetary reservation exhausted')
    return {'attempt': attempts+1, 'reserved_micro_usd': reserve, 'spent_plus_reserved_micro_usd': spent+reserve,
        'message_utf8_bytes': size, 'input_tokens_reserved': limits['input_tokens_reserved'],
        'output_tokens_reserved': limits['output_tokens'], 'input_token_bound_status': 'byte_ceiling_plus_framing_assumption',
        'billing_guarantee': False}
