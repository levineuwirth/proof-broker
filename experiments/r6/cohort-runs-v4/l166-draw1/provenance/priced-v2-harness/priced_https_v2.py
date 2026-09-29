"""R6-006 actor: price admission before private-credential read or connection.

The R6-005 TLS/handoff primitives are loaded unchanged. Only the current gate
and these orchestration bytes can reach them through this canned entrypoint.
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
    spec=importlib.util.spec_from_file_location('r6_actor_'+name,Path(__file__).with_name(name+'.py'))
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


gate=load('pricing_gate_v2')
base=load('live_https')
sha,encode,write=base.sha,base.encode,base.write
read_credential,client_context,connection=base.read_credential,base.client_context,base.connection
handoff,serialize=base.handoff,base.serialize


def execute(args):
    out = Path(args.out)
    policy = json.loads(Path(args.policy).read_bytes())
    fixture = json.loads(Path(args.fixture).read_bytes())
    arguments = json.loads(Path(args.arguments).read_bytes())
    # Never read a process environment credential, proxy or default CA path.
    body = serialize(arguments, args.case)
    if len(body) > policy['limits']['maximum_request_bytes']: raise ValueError('request_byte_budget')
    (out/'serialized-body.json').write_bytes(body)
    record = {'schema_version':'r6-priced-https-observation-2', 'connection_attempts':0,
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
    record.update(pricing_failure_code=None, pricing_admitted_at_ns=None, connection_started_at_ns=None,
                  credential_read_at_ns=None)
    persist(); server_persist()
    evaluated=time.time()
    try:
        permit=gate.strict(Path(args.permit).read_bytes())
        check=gate.transport_admission(policy,args.sources,arguments,Path(args.request).read_bytes(),
                                       permit,Path(args.ledger).read_bytes(),args.episode,evaluated)
        # The same in-memory arguments/body proceed to handoff; no reread after admission.
        gate.require(check['current']['body_sha256']==sha(body),'pricing_serialized_body_binding')
    except (gate.Failure,ValueError,KeyError,TypeError,OSError,UnicodeError) as error:
        code=error.code if isinstance(error,gate.Failure) else 'pricing_input_malformed'
        write(out/'pricing-check.json',{'accepted':False,'failure_code':code,'evaluated_at_unix':evaluated})
        record.update(failure_category='pricing_admission',pricing_failure_code=code,
                      fixture_tcp_port=None,elapsed_ns=0)
        persist(); server_persist(); return
    check.update(evaluated_at_unix=evaluated, admitted_at_ns=time.monotonic_ns())
    write(out/'pricing-check.json',check)
    record['pricing_admitted_at_ns']=check['admitted_at_ns']
    record['credential_read_at_ns']=time.monotonic_ns()
    authorization = read_credential(args.credential_file)
    persist()
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
        record['connection_started_at_ns']=time.monotonic_ns(); persist()
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
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('policy','fixture','arguments','credential-file','ca','server-cert','server-key','out','case',
                 'request','sources','permit','ledger','episode'):
        parser.add_argument('--'+name,required=True)
    execute(parser.parse_args())
