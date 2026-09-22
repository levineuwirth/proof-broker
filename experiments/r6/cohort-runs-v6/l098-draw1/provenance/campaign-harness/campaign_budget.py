"""Request bytes, reservation shape and interpretation, bound to the campaign policy.

Same producer and interpretation as the pilot, re-bound to this policy's
digest, with two corrections: the ledger is the campaign ledger (one file per
authorization, reservations serialized), and interpretation checks the local
`serialized == outbound` relationship on its own. Remote receipt is recorded as
unobservable, never as `null` acceptance of a combined predicate.
"""
import copy
from pathlib import Path
import time

import campaign_contract as contract
import campaign_ledger as ledger
import events
import payload
import priced_payload_v2 as previous
import pricing_gate_v2 as gate
import run as r6


def request(task, prepared):
    value = payload.strict_json(previous.request(task, prepared))
    value['schema_version'] = 'r6-farkas-request-8'
    value['policy_sha256'] = contract.policy_sha256()
    return events.canonical(value)+b'\n'


def arguments(request_bytes):
    opts = copy.deepcopy(contract.config()['request'])
    opts['input'] = [{'role': 'system', 'content': contract.PROMPT.read_text()},
        {'role': 'user', 'content': previous.previous.PREFIX+gate.sha(request_bytes)
                                    +previous.previous.SEPARATOR+request_bytes.decode()}]
    return opts


def reservation(arguments_value):
    c = contract.config(); limits = c['limits']
    size = sum(len(m['content'].encode()) for m in arguments_value['input'])
    gate.require(size <= limits['message_utf8_bytes'], 'input_byte_budget')
    reserve = gate.cost_micro(limits['input_tokens_reserved'], limits['output_tokens'], c['pricing']['nano_usd_per_token'])
    gate.require(reserve <= limits['total_micro_usd'], 'money_budget_exhausted')
    return {'reserved_micro_usd': reserve, 'message_utf8_bytes': size, 'input_tokens_reserved': limits['input_tokens_reserved'],
            'output_tokens_reserved': limits['output_tokens'], 'input_token_bound_status': 'byte_ceiling_plus_framing_assumption',
            'billing_guarantee': False}


def reserve(episode_id, arguments_value, request_bytes, sources, live, attempt_id=None):
    """Pricing admission, then one atomic slot-and-money reservation in the mode's campaign ledger, under the caller's attempt identity."""
    c = contract.config()
    admitted = gate.admission(c, sources, arguments_value, request_bytes, time.time())
    bindings = {'request_sha256': gate.sha(request_bytes), 'arguments_sha256': gate.sha(gate.canonical(arguments_value))}
    row, raw = contract.campaign_ledger(live).reserve(episode_id, reservation(arguments_value), bindings, admitted, attempt_id)
    return row, raw, admitted


def envelope_report(body, request_bytes):
    base = previous.previous
    expected = arguments(request_bytes); differences = []; missing = base.MISSING
    def compare(component, a, b):
        x, y = base.fingerprint(a), base.fingerprint(b)
        if x != y: differences.append({'component': component, 'expected': x, 'observed': y})
    try:
        if len(body) > contract.config()['limits']['maximum_request_bytes']: raise ValueError('Envelope exceeds limit')
        actual = payload.strict_json(body)
        if not isinstance(actual, dict): raise ValueError('Envelope is not an object')
    except (ValueError, UnicodeError):
        differences.append({'component': 'envelope_decode', 'expected': base.fingerprint(expected),
                            'observed': base.fingerprint(body)})
    else:
        compare('request_options', {k: v for k, v in expected.items() if k != 'input'},
                {k: v for k, v in actual.items() if k != 'input'})
        inputs = actual.get('input', missing)
        def layout(items):
            if not isinstance(items, list): return items
            return [{'role': i.get('role'), 'fields': sorted(i)} if isinstance(i, dict) else i for i in items]
        compare('message_layout', layout(expected['input']), layout(inputs))
        def content(role):
            if not isinstance(inputs, list): return missing
            rows = [x for x in inputs if isinstance(x, dict) and x.get('role') == role]
            return rows[0].get('content', missing) if len(rows) == 1 else missing
        compare('system_message', expected['input'][0]['content'], content('system'))
        user = content('user')
        if isinstance(user, str):
            head, separator, tail = user.partition(base.SEPARATOR)
            prefix, suffix = head+separator, tail if separator else missing
        else: prefix = suffix = user
        compare('user_prefix', base.PREFIX+gate.sha(request_bytes)+base.SEPARATOR, prefix)
        compare('request_suffix', request_bytes.decode(), suffix)
    return {'accepted': not differences, 'category': None if not differences else 'outbound_envelope_binding',
            'mismatches': differences, 'captured_body_sha256': gate.sha(body), 'request_sha256': gate.sha(request_bytes),
            'prompt_sha256': r6.sha(contract.PROMPT),
            'evidence_scope': 'serialized entity-body consistency; no remote-input or inference attestation'}


def interpret(root, request_bytes, live):
    """Every predicate recomputed. Local send capture and remote receipt are two predicates, not one."""
    import envelope_payload
    out = Path(root)
    http = r6.read_json(out/'http.json')
    body = (out/'serialized-body.json').read_bytes()
    envelope = envelope_report(body, request_bytes)
    sent = (out/'outbound-body.json').read_bytes() if (out/'outbound-body.json').exists() else None
    received = (out/'received-body.json').read_bytes() if (out/'received-body.json').exists() else None
    local = {'checked': http['body_sends_started'] > 0,
             'accepted': None if http['body_sends_started'] == 0 else (sent == body and http['outbound_body_sha256'] == gate.sha(body)),
             'scope': 'the bytes handed to HTTPSConnection.send equal the admitted serialized body; not a remote-input attestation'}
    remote = {'checked': received is not None,
              'accepted': None if received is None else received == body,
              'scope': 'provider-side receipt is unobservable in live mode' if live else 'local canned TLS receiver'}
    text = proposed = metadata = None; error = None
    echo = {'checked': False, 'accepted': None, 'scope': 'response_request_association'}
    if http['failure_category']:
        phase = ('pricing_admission' if http['failure_category'] in ('pricing_admission', 'authorization')
                 else 'campaign_ledger' if http['failure_category'] == 'campaign_ledger'
                 else 'credential_delivery' if http['failure_category'] == 'credential_format' else 'https_transport')
        error = previous.Failure(http['failure_category'], phase,
                                 ('Admission: '+str(http['pricing_failure_code'])) if http['pricing_failure_code']
                                 else 'HTTPS adapter: '+http['failure_category'])
    else:
        try:
            text, metadata = previous.response((out/'provider-response.json').read_bytes(), http['http_status'])
            echo = envelope_payload.echo(text, request_bytes)
            proposed = envelope_payload.response(text, request_bytes)
        except previous.Failure as failure: error = failure
        except envelope_payload.BoundaryFailure as failure:
            error = previous.Failure(failure.category, 'proposal', str(failure))
    if not envelope['accepted'] and http['failure_category'] not in ('pricing_admission', 'authorization', 'campaign_ledger', 'credential_format'):
        error = previous.Failure('outbound_envelope_binding', 'proposal',
                                 'Envelope components differ: '+', '.join(x['component'] for x in envelope['mismatches']))
    elif local['accepted'] is False:
        error = previous.Failure('transport_capture_failure', 'https_transport', 'Sent entity body differs from the serialized body')
    elif remote['accepted'] is False:
        error = previous.Failure('transport_capture_failure', 'https_transport', 'Received entity body differs from the serialized body')
    return proposed, text, metadata, {'outbound_envelope': envelope, 'local_send_consistency': local, 'remote_receipt': remote,
        'response_request_binding': echo, 'certificate_verified': None, 'send_outcome': http.get('send_outcome'),
        'failure_category': error.category if error else None, 'failure_phase': error.phase if error else None}, error
