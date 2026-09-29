"""Pinned stdlib HTTPS handoff, driven here only by a local canned TLS peer.

The client function has no retry, redirect, proxy, repository or model tools.
The fixture changes the TCP destination and trust root explicitly; SNI and
hostname validation still use the intended provider host. This is not a test
of OpenAI's deployed endpoint, certificate chain, account or model.
"""
import argparse
import hashlib
import http.client
import http.server
import json
from pathlib import Path
import socket
import ssl
import threading
import time


def sha(data): return hashlib.sha256(data).hexdigest()
def encode(value): return (json.dumps(value, sort_keys=True, separators=(',', ':'))+'\n').encode()
def write(path, value): path.write_bytes(encode(value))


def read_credential(path):
    text=Path(path).read_bytes().decode('ascii')
    if not text.endswith('\n') or text.count('\n')!=1:
        raise ValueError('credential_format')
    text=text[:-1]
    if not text.startswith('Bearer ') or len(text)<=7 or any(ord(c)<32 or ord(c)>126 for c in text):
        raise ValueError('credential_format')
    return text


def client_context(ca_file):
    context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    context.verify_mode = ssl.CERT_REQUIRED
    context.check_hostname = True
    context.minimum_version = ssl.TLSVersion.TLSv1_2
    context.set_alpn_protocols(['http/1.1'])
    context.load_verify_locations(cafile=str(ca_file))
    return context


def connection(policy, context, *, fixture_port=None):
    endpoint = policy['endpoint']
    if endpoint != {'scheme':'https', 'host':'api.openai.com', 'port':443, 'path':'/v1/responses'}:
        raise ValueError('https_endpoint_policy')
    if context.verify_mode != ssl.CERT_REQUIRED or not context.check_hostname or context.minimum_version < ssl.TLSVersion.TLSv1_2:
        raise ValueError('tls_context_policy')
    conn = http.client.HTTPSConnection(endpoint['host'], endpoint['port'],
        timeout=policy['limits']['io_timeout_seconds'], context=context)
    if fixture_port is not None:
        # This one explicit test seam leaves HTTPSConnection.connect's wrapping,
        # SNI and hostname verification intact. No external connection is made.
        conn._create_connection = lambda address, timeout, source=None: socket.create_connection(('127.0.0.1', fixture_port), timeout)
    return conn


def handoff(conn, body, authorization, out, record, persist):
    """Capture the exact entity body at the call to HTTPSConnection.send."""
    record['connection_attempts'] += 1
    persist()
    conn.connect()  # Certificate/hostname validation MUST precede HTTP headers.
    peer = conn.sock.getpeercert(binary_form=True)
    record['tls'] = {'verified': True, 'peer_certificate_sha256': sha(peer),
        'version': conn.sock.version(), 'cipher': list(conn.sock.cipher()),
        'alpn': conn.sock.selected_alpn_protocol(), 'server_hostname': conn.sock.server_hostname}
    record['tls_verified_at_ns'] = time.monotonic_ns()
    persist()
    conn.putrequest('POST', '/v1/responses', skip_accept_encoding=True)
    conn.putheader('Content-Type', 'application/json')
    conn.putheader('Content-Length', str(len(body)))
    if authorization is not None: conn.putheader('Authorization', authorization)
    record['header_sends_started'] += 1
    record['header_send_at_ns'] = time.monotonic_ns()
    persist()
    conn.endheaders()
    record['header_sends_returned'] += 1
    (out/'outbound-body.json').write_bytes(body)
    record['body_sends_started'] += 1
    record['outbound_body_sha256'] = sha(body)
    persist()
    conn.send(body)
    record['body_sends_returned'] += 1
    persist()
    response = conn.getresponse()
    record['http_status'] = response.status
    # No header dumps. A redirected location is never dereferenced.
    record['response_headers'] = {k: response.getheader(k) for k in ('Content-Type', 'Content-Length', 'x-request-id')
                                  if response.getheader(k) is not None}
    raw = response.read(record['maximum_response_bytes']+1)
    (out/'provider-response.json').write_bytes(raw)
    record['response_sha256'], record['response_bytes'] = sha(raw), len(raw)
    declared=response.getheader('Content-Length')
    if len(raw) > record['maximum_response_bytes']: record['failure_category'] = 'provider_response_budget'
    elif declared is not None and (not declared.isdigit() or int(declared)!=len(raw)):
        record['failure_category']='transport_incomplete_response'
    persist()


def serialize(arguments, case):
    value = json.loads(json.dumps(arguments))
    if case == 'altered_prompt': value['input'][0]['content'] += 'Altered.'
    elif case == 'omitted_prompt': value['input'] = value['input'][1:]
    elif case == 'altered_prefix': value['input'][1]['content'] = 'X'+value['input'][1]['content'][1:]
    elif case == 'altered_body': value['input'][1]['content'] += ' '
    elif case == 'altered_options': value['max_output_tokens'] += 1
    return encode(value)


def execute(args):
    out = Path(args.out)
    policy = json.loads(Path(args.policy).read_bytes())
    fixture = json.loads(Path(args.fixture).read_bytes())
    arguments = json.loads(Path(args.arguments).read_bytes())
    # Never read a process environment credential, proxy or default CA path.
    authorization = read_credential(args.credential_file)
    if args.case == 'missing_credential': authorization = None
    elif args.case == 'wrong_credential': authorization = 'Bearer deliberately-wrong-canned-credential'
    body = serialize(arguments, args.case)
    if len(body) > policy['limits']['maximum_request_bytes']: raise ValueError('request_byte_budget')
    (out/'serialized-body.json').write_bytes(body)
    record = {'schema_version':'r6-https-observation-1', 'connection_attempts':0,
        'header_sends_started':0, 'header_sends_returned':0, 'body_sends_started':0, 'body_sends_returned':0,
        'tls':None, 'tls_verified_at_ns':None, 'header_send_at_ns':None,
        'request_sha256':sha(body), 'request_bytes':len(body), 'outbound_body_sha256':None,
        'response_sha256':None, 'response_bytes':None, 'http_status':None, 'response_headers':{},
        'failure_category':None, 'tls_verify_code':None, 'maximum_response_bytes':policy['limits']['maximum_response_bytes'],
        'endpoint':policy['endpoint'], 'transport_scope':'isolated_loopback_https_fixture',
        'openssl_version':ssl.OPENSSL_VERSION, 'ca_bundle_sha256':sha(Path(args.ca).read_bytes()),
        'retries':0, 'redirects_followed':0, 'verification_time_unix':int(time.time())}
    server_record = {'requests':[], 'server_names':[], 'scope':'local canned TLS receiver'}
    def persist(): write(out/'http.json', record)
    def server_persist(): write(out/'server.json', server_record)
    class Handler(http.server.BaseHTTPRequestHandler):
        def log_message(self, *unused): pass
        def do_POST(self):
            n = int(self.headers.get('Content-Length', '0'))
            if n < 1 or n > policy['limits']['maximum_request_bytes']:
                self.send_error(413); return
            received = self.rfile.read(n)
            (out/'received-body.json').write_bytes(received)
            header = self.headers.get('Authorization')
            server_record['requests'].append({'method':self.command, 'path':self.path,
                'host':self.headers.get('Host'), 'content_type':self.headers.get('Content-Type'),
                'declared_bytes':n, 'observed_bytes':len(received), 'body_sha256':sha(received),
                'authorization_present':header is not None,
                'authorization_sha256':sha(header.encode()) if header is not None else None})
            server_persist()
            response_body = fixture['body'].encode(); status = fixture['status']
            if args.case == 'reflected_canary':
                response_body = encode({'error': {'message': 'canned reflection: '+str(header)}}); status = 500
            self.send_response(status)
            self.send_header('Content-Type', 'application/json')
            self.send_header('Content-Length', str(len(response_body)+(1 if args.case=='truncated_response' else 0)))
            self.send_header('x-request-id', 'r6-local-canned-https')
            if status in (307, 308): self.send_header('Location', 'https://must-not-contact.invalid/')
            if status in (429, 503): self.send_header('Retry-After', '0')
            self.end_headers()
            self.wfile.write(response_body)
    server = http.server.HTTPServer(('127.0.0.1', 0), Handler)
    server_context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    server_context.minimum_version = ssl.TLSVersion.TLSv1_2
    server_context.set_alpn_protocols(['http/1.1'])
    server_context.load_cert_chain(args.server_cert, args.server_key)
    def sni(sock, name, context):
        server_record['server_names'].append(name); server_persist()
    server_context.set_servername_callback(sni)
    server.socket = server_context.wrap_socket(server.socket, server_side=True)
    worker = threading.Thread(target=server.serve_forever, kwargs={'poll_interval':0.02}, daemon=True)
    worker.start(); server_persist()
    record['fixture_tcp_port'] = server.server_port
    conn = connection(policy, client_context(args.ca), fixture_port=server.server_port)
    start = time.monotonic_ns(); persist()
    try:
        handoff(conn, body, authorization, out, record, persist)
    except ssl.SSLCertVerificationError as error:
        record['failure_category'] = 'tls_certificate_verification'
        record['tls_verify_code'] = error.verify_code  # Never dump exception/header content.
    except ssl.SSLError: record['failure_category'] = 'tls_protocol_failure'
    except (TimeoutError, socket.timeout): record['failure_category'] = 'transport_timeout'
    except (OSError, http.client.HTTPException): record['failure_category'] = 'transport_connection_failure'
    finally:
        conn.close(); server.shutdown(); worker.join(timeout=2); server.server_close()
        record['elapsed_ns'] = time.monotonic_ns()-start
        persist(); server_persist()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('policy','fixture','arguments','credential-file','ca','server-cert','server-key','out','case'):
        parser.add_argument('--'+name, required=True)
    execute(parser.parse_args())
