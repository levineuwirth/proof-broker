"""R6-009 actor: R6-008's sender under the scientific contract and the campaign ledger.

Differences from the pilot actor, each a reviewed defect: the complete
authorization scope is re-derived here by the same function the host used; the
permit is verified against the campaign ledger bytes, not a per-run copy; the
credential read sits inside the exception boundary and a bad format is a
classified record; the permit is checked against the authoritative ledger file
and its activation must serve this policy's authorization for this mode; the
reservation's authoritative slot must be open before any connection; a
single-use send grant is committed there with O_EXCL after certificate
verification and before the first header byte, and both its creation and its
durable completion are timed; the outcome after that grant is `returned` or
`unknown`, never inferred; and a commitment to the header actually sent is
recorded so an operator scan can be bound to it. Revision 4 (R6-012): gate v4, census sites as tasks.
"""
import argparse
import hashlib
import http.client
import http.server
import importlib.util
import json
from pathlib import Path
import socket
import ssl
import sys
import threading
import time


sys.path.insert(0, str(Path(__file__).resolve().parent))  # gate v3 and the cohort ledger import their v2/R6-008 bases by name; all are mounted beside this file


def load(name):
    spec = importlib.util.spec_from_file_location('r6_cohort_'+name, Path(__file__).with_name(name+'.py'))
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


gate = load('pricing_gate_v4')
ledger = load('cohort_ledger')
base = load('live_https')
sha, encode, write = base.sha, base.encode, base.write
read_credential, client_context, connection = base.read_credential, base.client_context, base.connection
serialize = base.serialize
COMMITMENT_DOMAIN = 'r6-campaign-credential-commitment-1'


def commitment(nonce, authorization):
    return hashlib.sha256((COMMITMENT_DOMAIN+':'+nonce+':'+authorization).encode()).hexdigest()


def pricing_check(policy, contract_value, instruction, sources, arguments, request_bytes, permit, now):
    """Contract-and-pricing admission recomputed here, then bound to the host's permit."""
    current = gate.admission(policy, contract_value, instruction, sources, arguments, request_bytes, now)
    host_time = permit['pricing_admission']['evaluated_at_unix']
    gate.require(0 <= now-host_time <= policy['pricing_admission']['maximum_permit_age_seconds'], 'pricing_permit_stale')
    gate.require(permit['pricing_admission'] == gate.admission(policy, contract_value, instruction, sources, arguments, request_bytes, host_time), 'pricing_permit_binding')
    gate.require(permit['request_sha256'] == current['request_sha256'] and permit['arguments_sha256'] == current['arguments_sha256']
                 and permit['contract_sha256'] == current['contract_sha256'], 'pricing_permit_request_binding')
    gate.require(permit['reservation']['reserved_micro_usd'] == current['reserved_micro_usd'] == permit['reserved_micro_usd'], 'pricing_reservation_amount')
    return current


def handoff(conn, body, authorization, permit, grant_dir, out, record, persist):
    """Certificate verification, then the grant, then the first header byte."""
    record['connection_attempts'] += 1; persist()
    conn.connect()
    peer = conn.sock.getpeercert(binary_form=True)
    record['tls'] = {'verified': True, 'peer_certificate_sha256': sha(peer), 'version': conn.sock.version(),
                     'cipher': list(conn.sock.cipher()), 'alpn': conn.sock.selected_alpn_protocol(),
                     'server_hostname': conn.sock.server_hostname}
    record['tls_verified_at_ns'] = time.monotonic_ns(); persist()
    grant = ledger.grant_record(permit, time.monotonic_ns())
    try:
        durable_at = ledger.commit_grant(grant_dir, grant)  # O_EXCL; every byte; returns after file and directory fsync
    except (ledger.Failure, OSError) as error:
        # Nothing is sent. Whatever reached the slot is a marker; reconciliation consumes the uncertainty.
        record.update(failure_category='cohort_grant_write_failure', grant_write_failed=True,
                      ledger_failure_code=error.code if isinstance(error, ledger.Failure) else type(error).__name__)
        persist(); return
    record.update(grant_committed=True, grant_id=grant['grant_id'], grant_created_at_ns=grant['at_ns'],
                  grant_durable_at_ns=durable_at, send_outcome='unknown')
    persist()
    conn.putrequest('POST', '/v1/responses', skip_accept_encoding=True)
    conn.putheader('Content-Type', 'application/json')
    conn.putheader('Content-Length', str(len(body)))
    conn.putheader('Authorization', authorization)
    record['header_sends_started'] += 1
    record['header_send_at_ns'] = time.monotonic_ns(); persist()
    conn.endheaders()
    record['header_sends_returned'] += 1
    (out/'outbound-body.json').write_bytes(body)
    record['body_sends_started'] += 1
    record['outbound_body_sha256'] = sha(body); persist()
    conn.send(body)
    record['body_sends_returned'] += 1; persist()
    response = conn.getresponse()
    record['http_status'] = response.status
    record['response_headers'] = {k: response.getheader(k) for k in ('Content-Type', 'Content-Length', 'x-request-id')
                                  if response.getheader(k) is not None}
    raw = response.read(record['maximum_response_bytes']+1)
    (out/'provider-response.json').write_bytes(raw)
    record['response_sha256'], record['response_bytes'] = sha(raw), len(raw)
    declared = response.getheader('Content-Length')
    if len(raw) > record['maximum_response_bytes']: record['failure_category'] = 'provider_response_budget'
    elif declared is not None and (not declared.isdigit() or int(declared) != len(raw)):
        record['failure_category'] = 'transport_incomplete_response'
    record['send_outcome'] = 'returned'
    persist()


def execute(args):
    out = Path(args.out)
    policy_bytes = Path(args.policy).read_bytes()
    policy = json.loads(policy_bytes)
    policy_sha256 = sha(policy_bytes)
    arguments = json.loads(Path(args.arguments).read_bytes())
    live = args.mode == 'live'
    body = serialize(arguments, 'valid')
    if len(body) > policy['limits']['maximum_request_bytes']: raise ValueError('request_byte_budget')
    (out/'serialized-body.json').write_bytes(body)
    ca_digest = sha(Path(args.ca).read_bytes())
    contract_value = json.loads(Path(args.contract).read_bytes()); contract_sha256 = sha(Path(args.contract).read_bytes())
    instruction = Path(args.instruction).read_text()
    record = {'schema_version': 'r6-cohort-observation-1', 'mode': args.mode, 'policy_sha256': policy_sha256, 'contract_sha256': contract_sha256,
        'task_id': args.task, 'draw': int(args.draw), 'slot': args.task+'/'+args.draw,
        'connection_attempts': 0, 'header_sends_started': 0, 'header_sends_returned': 0,
        'body_sends_started': 0, 'body_sends_returned': 0, 'tls': None, 'tls_verified_at_ns': None,
        'header_send_at_ns': None, 'request_sha256': sha(body), 'request_bytes': len(body),
        'outbound_body_sha256': None, 'response_sha256': None, 'response_bytes': None,
        'http_status': None, 'response_headers': {}, 'failure_category': None, 'tls_verify_code': None,
        'maximum_response_bytes': policy['limits']['maximum_response_bytes'], 'endpoint': policy['endpoint'],
        'transport_scope': 'provider_request' if live else 'isolated_loopback_https_fixture',
        'openssl_version': ssl.OPENSSL_VERSION, 'ca_bundle_sha256': ca_digest,
        'authorization_present_in_policy': None, 'retries': 0, 'redirects_followed': 0,
        'pricing_failure_code': None, 'ledger_failure_code': None, 'pricing_admitted_at_ns': None,
        'permit_verified_at_ns': None, 'connection_started_at_ns': None, 'credential_read_at_ns': None,
        'credential_commitment_sha256': None, 'commitment_nonce': args.commitment_nonce,
        'reservation_id': None, 'grant_committed': False, 'grant_write_failed': False, 'grant_id': None, 'grant_created_at_ns': None, 'grant_durable_at_ns': None,
        'send_outcome': 'not_started', 'fixture_tcp_port': None, 'verification_time_unix': int(time.time())}
    server_record = {'requests': [], 'server_names': [],
                     'scope': 'no local receiver in live mode' if live else 'local canned TLS receiver'}
    def persist(): write(out/'http.json', record)
    def server_persist(): write(out/'server.json', server_record)
    persist(); server_persist()

    evaluated = time.time()
    permit = authorization = None
    try:
        if live:
            approval = ledger.authorization_scope(policy)  # the host's function, run again here
            record['authorization_present_in_policy'] = True
            if ca_digest != policy['tls']['public_ca_bundle']['sha256']: raise ValueError('cohort_ca_bundle_binding')
            if args.fixture_port is not None: raise ValueError('cohort_live_fixture_conflict')
            write(out/'authorization.json', {**{k: approval[k] for k in ledger.AUTHORIZATION_KEYS},
                'scope_note': 'author authorization re-derived inside the actor before any connection'})
        permit = gate.strict(Path(args.permit).read_bytes())
        if permit['policy_sha256'] != policy_sha256: raise ledger.Failure('cohort_permit_policy_binding')
        if policy['contract_sha256'] != contract_sha256: raise ledger.Failure('cohort_policy_contract_binding')
        ledger.verify_permit(permit, Path(args.ledger).read_bytes(), policy, live, args.episode, args.task, int(args.draw))
        # The request's own identity must be the funded task's, joined here before the credential is read.
        gate.check_task_join(gate.check_request_grammar(gate.strict(Path(args.request).read_bytes())), args.task, permit['task_manifest_sha256'], permit['challenge_sha256'])
        ledger.slot_open(args.grant)  # the attempt's authoritative slot, not a run-local directory
        record['reservation_id'] = permit['reservation_id']; record['permit_verified_at_ns'] = time.monotonic_ns()
        check = pricing_check(policy, contract_value, instruction, args.sources, arguments, Path(args.request).read_bytes(), permit, evaluated)
        gate.require(check['body_sha256'] == sha(body), 'pricing_serialized_body_binding')
        check.update(evaluated_at_unix=evaluated, admitted_at_ns=time.monotonic_ns())
        write(out/'pricing-check.json', check)
        record['pricing_admitted_at_ns'] = check['admitted_at_ns']
        record['credential_read_at_ns'] = time.monotonic_ns()
        authorization = read_credential(args.credential_file)
        record['credential_commitment_sha256'] = commitment(args.commitment_nonce, authorization)
    except (gate.Failure, ledger.Failure, ValueError, KeyError, TypeError, OSError, UnicodeError) as error:
        if isinstance(error, gate.Failure):
            category, code = ('contract_admission' if error.code.startswith(('contract_', 'policy_', 'cohort_request_')) else 'pricing_admission'), error.code
            write(out/'pricing-check.json', {'accepted': False, 'failure_code': code, 'evaluated_at_unix': evaluated})
            record['pricing_failure_code'] = code
        elif isinstance(error, ledger.Failure):
            category, code = ('authorization' if error.code.startswith('cohort_authorization') or error.code == 'cohort_live_disabled'
                              else 'cohort_ledger'), error.code
            record['ledger_failure_code'] = code
        elif str(error) == 'credential_format':
            category = 'credential_format'
        else:
            category = 'authorization'
        record.update(failure_category=category, elapsed_ns=0)
        if category == 'authorization': record['pricing_failure_code'] = record['pricing_failure_code'] or (str(error) or 'cohort_input_malformed')
        persist(); server_persist(); return
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
        def sni(sock, name, ctx):
            server_record['server_names'].append(name); server_persist()
        context.set_servername_callback(sni)
        server.socket = context.wrap_socket(server.socket, server_side=True)
        worker = threading.Thread(target=server.serve_forever, kwargs={'poll_interval': 0.02}, daemon=True)
        worker.start(); server_persist()
        record['fixture_tcp_port'] = server.server_port

    conn = connection(policy, client_context(args.ca), fixture_port=record['fixture_tcp_port'])
    start = time.monotonic_ns(); persist()
    try:
        record['connection_started_at_ns'] = time.monotonic_ns(); persist()
        handoff(conn, body, authorization, permit, Path(args.grant), out, record, persist)
    except ssl.SSLCertVerificationError as error:
        record['failure_category'] = 'tls_certificate_verification'
        record['tls_verify_code'] = error.verify_code  # Never dump exception or header content.
    except ssl.SSLError: record['failure_category'] = 'tls_protocol_failure'
    except (TimeoutError, socket.timeout): record['failure_category'] = 'transport_timeout'
    except (OSError, http.client.HTTPException): record['failure_category'] = 'transport_connection_failure'
    except ledger.Failure as error:
        record['failure_category'] = 'cohort_ledger'; record['ledger_failure_code'] = error.code
    finally:
        conn.close()
        if server is not None:
            server.shutdown(); worker.join(timeout=2); server.server_close()
        record['elapsed_ns'] = time.monotonic_ns()-start
        persist(); server_persist()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode', required=True, choices=['rehearsal', 'live'])
    for name in ('policy', 'contract', 'instruction', 'arguments', 'credential-file', 'ca', 'out', 'sources', 'permit',
                 'ledger', 'request', 'episode', 'task', 'draw', 'grant', 'commitment-nonce'):
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
