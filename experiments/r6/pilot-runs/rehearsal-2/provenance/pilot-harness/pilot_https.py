"""R6-007 actor: one rehearsed path, two destinations.

The rehearsal and the live attempt run the *same* admission, credential read,
TLS context, connection and handoff. `--mode live` differs only by having no
loopback seam and by trusting the pinned public bundle. The actor re-derives the
live authorization from the mounted policy rather than trusting the caller, so a
rehearsal-shaped invocation cannot reach the provider and a live invocation
cannot silently fall back to a fixture.
"""
import argparse
import http.client
import http.server
import importlib.util
import json
from pathlib import Path
import socket
import ssl
import threading
import time


def load(name):
    spec = importlib.util.spec_from_file_location('r6_pilot_'+name, Path(__file__).with_name(name+'.py'))
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


gate = load('pricing_gate_v2')
base = load('live_https')
sha, encode, write = base.sha, base.encode, base.write
read_credential, client_context, connection = base.read_credential, base.client_context, base.connection
handoff, serialize = base.handoff, base.serialize

LIVE_KEYS = {'approved_by', 'approved_utc', 'scope', 'maximum_attempts', 'maximum_micro_usd', 'model_id'}


def live_authorization(policy):
    """Re-derived here; a host-side decision is never sufficient on its own."""
    if policy.get('live_enabled') is not True: raise ValueError('pilot_live_disabled')
    record = policy.get('authorization')
    if not isinstance(record, dict) or set(record) != LIVE_KEYS: raise ValueError('pilot_authorization_absent')
    if record['maximum_attempts'] != 1: raise ValueError('pilot_authorization_scope')
    if record['model_id'] != policy['model']['requested_id']: raise ValueError('pilot_authorization_subject')
    return record


def execute(args):
    out = Path(args.out)
    policy = json.loads(Path(args.policy).read_bytes())
    arguments = json.loads(Path(args.arguments).read_bytes())
    live = args.mode == 'live'
    body = serialize(arguments, 'valid')
    if len(body) > policy['limits']['maximum_request_bytes']: raise ValueError('request_byte_budget')
    (out/'serialized-body.json').write_bytes(body)
    ca_digest = sha(Path(args.ca).read_bytes())
    record = {'schema_version': 'r6-live-pilot-observation-1', 'mode': args.mode,
        'connection_attempts': 0, 'header_sends_started': 0, 'header_sends_returned': 0,
        'body_sends_started': 0, 'body_sends_returned': 0, 'tls': None, 'tls_verified_at_ns': None,
        'header_send_at_ns': None, 'request_sha256': sha(body), 'request_bytes': len(body),
        'outbound_body_sha256': None, 'response_sha256': None, 'response_bytes': None,
        'http_status': None, 'response_headers': {}, 'failure_category': None, 'tls_verify_code': None,
        'maximum_response_bytes': policy['limits']['maximum_response_bytes'], 'endpoint': policy['endpoint'],
        'transport_scope': 'provider_request' if live else 'isolated_loopback_https_fixture',
        'openssl_version': ssl.OPENSSL_VERSION, 'ca_bundle_sha256': ca_digest,
        'authorization_present_in_policy': None, 'retries': 0, 'redirects_followed': 0,
        'pricing_failure_code': None, 'pricing_admitted_at_ns': None, 'connection_started_at_ns': None,
        'credential_read_at_ns': None, 'fixture_tcp_port': None,
        'verification_time_unix': int(time.time())}
    server_record = {'requests': [], 'server_names': [],
                     'scope': 'no local receiver in live mode' if live else 'local canned TLS receiver'}
    def persist(): write(out/'http.json', record)
    def server_persist(): write(out/'server.json', server_record)
    persist(); server_persist()

    evaluated = time.time()
    try:
        if live:
            approval = live_authorization(policy)
            record['authorization_present_in_policy'] = True
            if ca_digest != policy['tls']['public_ca_bundle']['sha256']:
                raise ValueError('pilot_ca_bundle_binding')
            if args.fixture_port is not None: raise ValueError('pilot_live_fixture_conflict')
            write(out/'authorization.json', {'approved_by': approval['approved_by'],
                'approved_utc': approval['approved_utc'], 'model_id': approval['model_id'],
                'maximum_attempts': approval['maximum_attempts'],
                'maximum_micro_usd': approval['maximum_micro_usd'],
                'scope': 'author authorization re-derived inside the actor before any connection'})
        permit = gate.strict(Path(args.permit).read_bytes())
        check = gate.transport_admission(policy, args.sources, arguments, Path(args.request).read_bytes(),
                                         permit, Path(args.ledger).read_bytes(), args.episode, evaluated)
        gate.require(check['current']['body_sha256'] == sha(body), 'pricing_serialized_body_binding')
    except (gate.Failure, ValueError, KeyError, TypeError, OSError, UnicodeError) as error:
        code = error.code if isinstance(error, gate.Failure) else str(error) or 'pilot_input_malformed'
        write(out/'pricing-check.json', {'accepted': False, 'failure_code': code, 'evaluated_at_unix': evaluated})
        record.update(failure_category='pricing_admission' if isinstance(error, gate.Failure) else 'authorization',
                      pricing_failure_code=code, elapsed_ns=0)
        persist(); server_persist(); return
    check.update(evaluated_at_unix=evaluated, admitted_at_ns=time.monotonic_ns())
    write(out/'pricing-check.json', check)
    record['pricing_admitted_at_ns'] = check['admitted_at_ns']
    record['credential_read_at_ns'] = time.monotonic_ns()
    authorization = read_credential(args.credential_file)
    persist()

    server = worker = None
    if not live:
        fixture = json.loads(Path(args.fixture).read_bytes())
        class Handler(http.server.BaseHTTPRequestHandler):
            def log_message(self, *unused): pass
            def do_POST(self):
                n = int(self.headers.get('Content-Length', '0'))
                if n < 1 or n > policy['limits']['maximum_request_bytes']:
                    self.send_error(413); return
                received = self.rfile.read(n)
                (out/'received-body.json').write_bytes(received)
                header = self.headers.get('Authorization')
                server_record['requests'].append({'method': self.command, 'path': self.path,
                    'host': self.headers.get('Host'), 'content_type': self.headers.get('Content-Type'),
                    'declared_bytes': n, 'observed_bytes': len(received), 'body_sha256': sha(received),
                    'authorization_present': header is not None,
                    'authorization_sha256': sha(header.encode()) if header is not None else None})
                server_persist()
                raw = fixture['body'].encode()
                self.send_response(fixture['status'])
                self.send_header('Content-Type', 'application/json')
                self.send_header('Content-Length', str(len(raw)))
                self.send_header('x-request-id', 'r6-local-canned-https')
                self.end_headers()
                self.wfile.write(raw)
        server = http.server.HTTPServer(('127.0.0.1', 0), Handler)
        context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        context.minimum_version = ssl.TLSVersion.TLSv1_2
        context.set_alpn_protocols(['http/1.1'])
        context.load_cert_chain(args.server_cert, args.server_key)
        context.set_servername_callback(lambda s, n, c: (server_record['server_names'].append(n), server_persist()))
        server.socket = context.wrap_socket(server.socket, server_side=True)
        worker = threading.Thread(target=server.serve_forever, kwargs={'poll_interval': 0.02}, daemon=True)
        worker.start(); server_persist()
        record['fixture_tcp_port'] = server.server_port

    conn = connection(policy, client_context(args.ca), fixture_port=record['fixture_tcp_port'])
    start = time.monotonic_ns(); persist()
    try:
        record['connection_started_at_ns'] = time.monotonic_ns(); persist()
        handoff(conn, body, authorization, out, record, persist)
    except ssl.SSLCertVerificationError as error:
        record['failure_category'] = 'tls_certificate_verification'
        record['tls_verify_code'] = error.verify_code  # Never dump exception or header content.
    except ssl.SSLError: record['failure_category'] = 'tls_protocol_failure'
    except (TimeoutError, socket.timeout): record['failure_category'] = 'transport_timeout'
    except (OSError, http.client.HTTPException): record['failure_category'] = 'transport_connection_failure'
    finally:
        conn.close()
        if server is not None:
            server.shutdown(); worker.join(timeout=2); server.server_close()
        record['elapsed_ns'] = time.monotonic_ns()-start
        persist(); server_persist()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode', required=True, choices=['rehearsal', 'live'])
    for name in ('policy', 'arguments', 'credential-file', 'ca', 'out', 'sources', 'permit',
                 'ledger', 'request', 'episode'):
        parser.add_argument('--'+name, required=True)
    for name in ('fixture', 'server-cert', 'server-key'):
        parser.add_argument('--'+name)
    parser.add_argument('--fixture-port', type=int)
    args = parser.parse_args()
    if args.mode == 'rehearsal' and not all([args.fixture, args.server_cert, args.server_key]):
        parser.error('rehearsal requires --fixture, --server-cert and --server-key')
    if args.mode == 'live' and any([args.fixture, args.server_cert, args.server_key, args.fixture_port]):
        parser.error('live refuses fixture inputs')
    execute(args)


if __name__ == '__main__':
    main()
