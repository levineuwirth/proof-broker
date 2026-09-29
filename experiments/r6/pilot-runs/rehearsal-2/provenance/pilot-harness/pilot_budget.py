"""Request bytes and the durable ledger, bound to the pilot policy.

The frozen R6-006 v2 request builder and ledger bind to *their* policy by hash,
and the frozen gate refuses a request whose inner `policy_sha256` is not the
policy it is admitting under. So the pilot cannot borrow them: it rebuilds the
request with its own policy digest and keeps its own ledger, and hands both to
the unchanged gate. The gate then enforces the pilot's limits — including the
one-attempt campaign ceiling — rather than v2's.
"""
import copy
import fcntl
import os
from pathlib import Path
import time

import events
import payload
import pilot_contract as contract
import priced_payload_v2 as previous
import pricing_gate_v2 as gate
import run as r6


def request(task, prepared):
    """The v2 producer's row/IR checks, re-bound to this policy's digest."""
    value = payload.strict_json(previous.request(task, prepared))
    value['schema_version'] = 'r6-farkas-request-7'
    value['policy_sha256'] = r6.sha(contract.CONFIG)
    return events.canonical(value)+b'\n'


def arguments(request_bytes):
    opts = copy.deepcopy(contract.config()['request'])
    opts['input'] = [{'role': 'system', 'content': contract.PROMPT.read_text()},
        {'role': 'user', 'content': previous.previous.PREFIX+gate.sha(request_bytes)
                                    +previous.previous.SEPARATOR+request_bytes.decode()}]
    return opts


def reservation(arguments_value, spent, attempts):
    c = contract.config(); limits = c['limits']
    gate.require(attempts < limits['attempts_per_episode'], 'request_budget_exhaustion')
    size = sum(len(m['content'].encode()) for m in arguments_value['input'])
    gate.require(size <= limits['message_utf8_bytes'], 'input_byte_budget')
    reserve = gate.cost_micro(limits['input_tokens_reserved'], limits['output_tokens'], c['pricing']['nano_usd_per_token'])
    gate.require(spent+reserve <= limits['total_micro_usd'], 'money_budget_exhausted')
    return {'reserved_micro_usd': reserve, 'input_tokens_reserved': limits['input_tokens_reserved'],
            'output_tokens': limits['output_tokens'], 'message_utf8_bytes': size,
            'spent_before_micro_usd': spent, 'ceiling_micro_usd': limits['total_micro_usd'],
            'billing_guarantee': False,
            'scope': 'conditional reservation under the frozen rates; the ceiling funds exactly one attempt'}


def reserve(path, episode_id, arguments_value, request_bytes, sources):
    """Admission precedes every append; the ledger cannot fund a second attempt."""
    c = contract.config()
    gate.require(isinstance(episode_id, str) and bool(episode_id), 'missing_episode_identity')
    admitted = gate.admission(c, sources, arguments_value, request_bytes, time.time())
    path = Path(path)
    with path.open('a+b') as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        f.seek(0); raw = f.read()
        rows = []
        if raw:
            gate.require(raw.endswith(b'\n'), 'truncated_reservation_ledger')
            rows = [gate.strict(line) for line in raw.splitlines()]
        for index, row in enumerate(rows):
            gate.require(row['sequence'] == index and row['policy_sha256'] == admitted['policy_sha256'], 'ledger_identity')
            previous_hash = '0'*64 if index == 0 else gate.sha(gate.canonical(rows[index-1]))
            gate.require(row['previous_hash'] == previous_hash, 'ledger_chain')
            gate.require(row['reservation']['reserved_micro_usd'] == admitted['reserved_micro_usd'], 'ledger_price')
        attempts = sum(row['episode_id'] == episode_id for row in rows)
        spent = sum(row['reservation']['reserved_micro_usd'] for row in rows)
        gate.require(len(rows) < c['limits']['campaign_attempts'], 'campaign_request_budget')
        row = {'sequence': len(rows), 'previous_hash': gate.sha(gate.canonical(rows[-1])) if rows else '0'*64,
               'episode_id': episode_id, 'policy_sha256': admitted['policy_sha256'],
               'request_sha256': gate.sha(request_bytes), 'arguments_sha256': gate.sha(gate.canonical(arguments_value)),
               'reservation': reservation(arguments_value, spent, attempts), 'pricing_admission': admitted}
        f.seek(0, 2); f.write(gate.canonical(row)+b'\n'); f.flush(); os.fsync(f.fileno())
    return row


def envelope_report(body, request_bytes):
    """Frozen fingerprint semantics against this policy's own expected bytes."""
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
    """Every predicate recomputed; in live mode the endpoint capture is unobservable."""
    import envelope_payload
    out = Path(root)
    http = r6.read_json(out/'http.json')
    body = (out/'serialized-body.json').read_bytes()
    envelope = envelope_report(body, request_bytes)
    sent = (out/'outbound-body.json').read_bytes() if (out/'outbound-body.json').exists() else None
    received = (out/'received-body.json').read_bytes() if (out/'received-body.json').exists() else None
    consistency = {'checked': sent is not None and received is not None,
                   'accepted': None if sent is None or received is None else sent == received == body,
                   'scope': 'no local receiver in live mode; provider-side receipt is unobservable' if live
                            else 'local canned TLS receiver'}
    text = proposed = metadata = None; error = None
    echo = {'checked': False, 'accepted': None, 'scope': 'response_request_association'}
    if http['failure_category']:
        pricing = http['failure_category'] in ('pricing_admission', 'authorization')
        error = previous.Failure(http['failure_category'], 'pricing_admission' if pricing else 'https_transport',
                                 ('Admission: '+str(http['pricing_failure_code'])) if pricing
                                 else 'HTTPS adapter: '+http['failure_category'])
    else:
        try:
            text, metadata = previous.response((out/'provider-response.json').read_bytes(), http['http_status'])
            echo = envelope_payload.echo(text, request_bytes)
            proposed = envelope_payload.response(text, request_bytes)
        except previous.Failure as failure: error = failure
        except envelope_payload.BoundaryFailure as failure:
            error = previous.Failure(failure.category, 'proposal', str(failure))
    if not envelope['accepted'] and http['failure_category'] not in ('pricing_admission', 'authorization'):
        error = previous.Failure('outbound_envelope_binding', 'proposal',
                                 'Envelope components differ: '+', '.join(x['component'] for x in envelope['mismatches']))
    elif consistency['accepted'] is False:
        error = previous.Failure('transport_capture_failure', 'https_transport', 'Send/receive entity bodies differ')
    return proposed, text, metadata, {'outbound_envelope': envelope, 'body_consistency': consistency,
        'response_request_binding': echo, 'certificate_verified': None,
        'failure_category': error.category if error else None, 'failure_phase': error.phase if error else None}, error
