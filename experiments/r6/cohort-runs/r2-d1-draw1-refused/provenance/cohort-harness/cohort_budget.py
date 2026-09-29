"""Request bytes, envelope, reservation and interpretation under the scientific contract.

The request carries the contract digest and the task, challenge and exact-IR
bindings; no policy digest. The envelope is the contract's rendering rule over
those bytes and nothing else. Reservation names a (task, draw) slot in the
campaign ledger under the current policy revision. Interpretation is R6-008's,
with the envelope compared to the contract's rendering rather than a policy's.
"""
from pathlib import Path
import time

import campaign_budget as previous
import cohort_contract as contract
import events
import payload
import pricing_gate_v3 as gate
import priced_payload_v2 as v2
import provider_payload
import run as r6


def request(task, prepared):
    """The frozen arithmetic producer's row/IR checks, bound to the contract instead of a policy."""
    value = payload.strict_json(v2.request(task, prepared))
    value.pop('policy_sha256')
    value['schema_version'] = gate.REQUEST_SCHEMA
    value['contract_sha256'] = contract.contract_sha256()
    r6.jsonschema.validate(value, r6.read_json(r6.ROOT/'schema/cohort-request.schema.json'))
    return events.canonical(value)+b'\n'


def arguments(request_bytes):
    return gate.render_arguments(contract.contract(), contract.PROMPT.read_text(), request_bytes)


def reservation(arguments_value):
    c = contract.config(); limits = c['limits']
    size = sum(len(m['content'].encode()) for m in arguments_value['input'])
    gate.require(size <= limits['message_utf8_bytes'], 'input_byte_budget')
    reserve = gate.v2.cost_micro(limits['input_tokens_reserved'], limits['output_tokens'], c['pricing']['nano_usd_per_token'])
    return {'reserved_micro_usd': reserve, 'message_utf8_bytes': size, 'input_tokens_reserved': limits['input_tokens_reserved'],
            'output_tokens_reserved': limits['output_tokens'], 'input_token_bound_status': 'byte_ceiling_plus_framing_assumption', 'billing_guarantee': False}


def reserve(episode_id, task_id, draw, arguments_value, request_bytes, sources, live, attempt_id=None):
    """Contract-and-pricing admission, then one (task, draw) reservation under the current revision."""
    c = contract.config()
    admitted = gate.admission(c, contract.contract(), contract.PROMPT.read_text(), sources, arguments_value, request_bytes, time.time())
    bindings = {'request_sha256': gate.sha(request_bytes), 'arguments_sha256': gate.sha(gate.canonical(arguments_value)), 'contract_sha256': admitted['contract_sha256']}
    row, raw = contract.campaign_ledger(live, c).reserve(episode_id, c, task_id, draw, reservation(arguments_value), bindings, admitted, attempt_id)
    return row, raw, admitted


def envelope_report(body, request_bytes):
    """R6-006's fingerprint semantics against the contract's rendering of this request."""
    base = v2.previous
    expected = arguments(request_bytes); differences = []; missing = base.MISSING
    def compare(component, a, b):
        x, y = base.fingerprint(a), base.fingerprint(b)
        if x != y: differences.append({'component': component, 'expected': x, 'observed': y})
    try:
        if len(body) > contract.contract()['limits']['maximum_request_bytes']: raise ValueError('Envelope exceeds limit')
        actual = payload.strict_json(body)
        if not isinstance(actual, dict): raise ValueError('Envelope is not an object')
    except (ValueError, UnicodeError):
        differences.append({'component': 'envelope_decode', 'expected': base.fingerprint(expected), 'observed': base.fingerprint(body)})
    else:
        compare('request_options', {k: v for k, v in expected.items() if k != 'input'}, {k: v for k, v in actual.items() if k != 'input'})
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
            head, separator, tail = user.partition(base.SEPARATOR); prefix, suffix = head+separator, tail if separator else missing
        else: prefix = suffix = user
        compare('user_prefix', base.PREFIX+gate.sha(request_bytes)+base.SEPARATOR, prefix)
        compare('request_suffix', request_bytes.decode(), suffix)
    return {'accepted': not differences, 'category': None if not differences else 'outbound_envelope_binding', 'mismatches': differences,
            'captured_body_sha256': gate.sha(body), 'request_sha256': gate.sha(request_bytes), 'contract_sha256': contract.contract_sha256(),
            'evidence_scope': 'serialized entity-body consistency against the contract rendering; no remote-input or inference attestation'}


def interpret(root, request_bytes, live):
    """R6-008's interpretation with the contract's envelope report."""
    import envelope_payload
    out = Path(root); http = r6.read_json(out/'http.json'); body = (out/'serialized-body.json').read_bytes()
    envelope = envelope_report(body, request_bytes)
    sent = (out/'outbound-body.json').read_bytes() if (out/'outbound-body.json').exists() else None
    received = (out/'received-body.json').read_bytes() if (out/'received-body.json').exists() else None
    local = {'checked': http['body_sends_started'] > 0, 'accepted': None if http['body_sends_started'] == 0 else (sent == body and http['outbound_body_sha256'] == gate.sha(body)),
             'scope': 'the bytes handed to HTTPSConnection.send equal the admitted serialized body; not a remote-input attestation'}
    remote = {'checked': received is not None, 'accepted': None if received is None else received == body,
              'scope': 'provider-side receipt is unobservable in live mode' if live else 'local canned TLS receiver'}
    text = proposed = metadata = None; error = None
    echo = {'checked': False, 'accepted': None, 'scope': 'response_request_association'}
    if http['failure_category']:
        phase = ('pricing_admission' if http['failure_category'] in ('pricing_admission', 'authorization', 'contract_admission') else
                 'cohort_ledger' if http['failure_category'] == 'cohort_ledger' else 'credential_delivery' if http['failure_category'] == 'credential_format' else 'https_transport')
        error = v2.Failure(http['failure_category'], phase, ('Admission: '+str(http['pricing_failure_code'])) if http['pricing_failure_code'] else 'HTTPS adapter: '+http['failure_category'])
    else:
        try:
            text, metadata = v2.response((out/'provider-response.json').read_bytes(), http['http_status'])
            echo = envelope_payload.echo(text, request_bytes); proposed = envelope_payload.response(text, request_bytes)
        except v2.Failure as failure: error = failure
        except envelope_payload.BoundaryFailure as failure: error = v2.Failure(failure.category, 'proposal', str(failure))
    if not envelope['accepted'] and http['failure_category'] not in ('pricing_admission', 'authorization', 'contract_admission', 'cohort_ledger', 'credential_format'):
        error = v2.Failure('outbound_envelope_binding', 'proposal', 'Envelope components differ: '+', '.join(x['component'] for x in envelope['mismatches']))
    elif local['accepted'] is False: error = v2.Failure('transport_capture_failure', 'https_transport', 'Sent entity body differs from the serialized body')
    elif remote['accepted'] is False: error = v2.Failure('transport_capture_failure', 'https_transport', 'Received entity body differs from the serialized body')
    return proposed, text, metadata, {'outbound_envelope': envelope, 'local_send_consistency': local, 'remote_receipt': remote, 'response_request_binding': echo,
        'certificate_verified': None, 'send_outcome': http.get('send_outcome'), 'failure_category': error.category if error else None,
        'failure_phase': error.phase if error else None}, error
