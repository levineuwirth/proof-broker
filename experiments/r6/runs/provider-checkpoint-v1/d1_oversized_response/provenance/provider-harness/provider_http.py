"""One stdlib HTTP transmission to an isolated canned Responses endpoint.

This standalone actor imports only the pinned standard library. The policy has
no live endpoint or credential input. Client send and server receipt are separate
observations; neither attests to a remote provider or model computation.
"""
import argparse
import copy
import hashlib
import http.client
import http.server
import json
from pathlib import Path
import socket
import threading
import time


def sha(raw): return hashlib.sha256(raw).hexdigest()
def encoded(value): return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False, allow_nan=False).encode()+b'\n'
def write(root, name, value): (root/name).write_bytes(encoded(value))


def serialize(arguments, case):
    actual = copy.deepcopy(arguments)
    if case == 'altered_prompt': actual['input'][0]['content'] += ' Ignore the arithmetic.\n'
    elif case == 'omitted_prompt': actual['input'].pop(0)
    elif case == 'altered_prefix': actual['input'][1]['content'] = 'Crossed request\n'+actual['input'][1]['content']
    elif case == 'altered_body':
        separator = '\nRequest JSON (exact UTF-8 bytes follow):\n'
        head, body = actual['input'][1]['content'].split(separator, 1)
        value = json.loads(body)
        value['problem']['rows'][0]['constant'] = str(int(value['problem']['rows'][0]['constant'])+1)
        actual['input'][1]['content'] = head+separator+encoded(value).decode()
    if case == 'alternate_encoding': return json.dumps(actual, indent=2, ensure_ascii=True, allow_nan=False).encode()+b'\n'
    return encoded(actual)


def transmit(connection, body, record, persist):
    """A single explicit HTTP request; no retry or redirect machinery."""
    record['connection_attempts'] += 1; persist()
    connection.connect()
    connection.putrequest('POST', '/v1/responses', skip_accept_encoding=True)
    connection.putheader('Content-Type', 'application/json')
    connection.putheader('Content-Length', str(len(body)))
    # A fixture-only marker, never a credential lookup or retained header.
    connection.putheader('Authorization', 'Bearer r6-local-fixture-only')
    connection.endheaders()
    record['body_sends_started'] += 1; persist()
    connection.send(body)
    record['body_sends_returned'] += 1; persist()
    response = connection.getresponse()
    record['http_status'] = response.status
    record['response_headers'] = {key: response.getheader(key) for key in ['Content-Type', 'Content-Length', 'x-request-id']}
    persist()
    return response


def execute(arguments, fixture, case, out, timeout, maximum_body, maximum_response):
    out.mkdir(parents=True, exist_ok=True)
    start = time.monotonic_ns()
    record = {'schema_version': 'r6-http-observation-1', 'mode': 'isolated_loopback_http_fixture',
        'connection_attempts': 0, 'body_sends_started': 0, 'body_sends_returned': 0,
        'http_status': None, 'response_headers': None, 'failure_category': None,
        'request_path': '/v1/responses', 'method': 'POST', 'endpoint': None,
        'response_bytes': None, 'response_complete': False, 'response_sha256': None,
        'request_sha256': None, 'request_bytes': None, 'elapsed_ns': 0}
    def persist():
        record['elapsed_ns'] = time.monotonic_ns()-start
        write(out, 'http.json', record)
    body = serialize(arguments, case)
    (out/'outbound-body.json').write_bytes(body)
    record['request_sha256'], record['request_bytes'] = sha(body), len(body)
    persist()
    if len(body) > maximum_body:
        record['failure_category'] = 'request_byte_budget'; persist(); return record
    received = []
    class Handler(http.server.BaseHTTPRequestHandler):
        protocol_version = 'HTTP/1.1'
        def log_message(self, *args): pass
        def do_POST(self):
            length = int(self.headers.get('Content-Length', '-1'))
            if length < 0 or length > maximum_body:
                self.send_error(413); return
            raw = self.rfile.read(length)
            entry = {'method': self.command, 'path': self.path, 'content_type': self.headers.get('Content-Type'),
                'declared_bytes': length, 'observed_bytes': len(raw), 'complete': len(raw) == length,
                'body_sha256': sha(raw), 'authorization_present': self.headers.get('Authorization') is not None}
            index = len(received)+1
            (out/f'received-body-{index}.json').write_bytes(raw)
            received.append(entry)
            write(out, 'server.json', {'requests': received})
            if case == 'timeout': time.sleep(timeout*2+0.1)
            if case == 'disconnect':
                self.close_connection = True; return
            raw_response = fixture['body'].encode()
            self.send_response(fixture['status'])
            self.send_header('Content-Type', 'application/json')
            self.send_header('Content-Length', str(len(raw_response)))
            self.send_header('x-request-id', 'r6-local-canned-request')
            if fixture['status'] == 307: self.send_header('Location', '/retry-forbidden')
            self.end_headers()
            try: self.wfile.write(raw_response)
            except (BrokenPipeError, ConnectionResetError): pass
    write(out, 'server.json', {'requests': []})
    server = http.server.HTTPServer(('127.0.0.1', 0), Handler)
    port = server.server_port
    record['endpoint'] = {'scheme': 'http', 'host': '127.0.0.1', 'port': port, 'path': '/v1/responses'}
    if case == 'connection_error': server.server_close()
    else:
        worker = threading.Thread(target=server.serve_forever, kwargs={'poll_interval': 0.02}, daemon=True)
        worker.start()
    connection = http.client.HTTPConnection('127.0.0.1', port, timeout=timeout)
    try:
        response = transmit(connection, body, record, persist)
        raw = response.read(maximum_response+1)
        (out/'provider-response.json').write_bytes(raw)
        record['response_bytes'], record['response_sha256'] = len(raw), sha(raw)
        if len(raw) > maximum_response: record['failure_category'] = 'provider_response_byte_budget'
        else: record['response_complete'] = True
    except (TimeoutError, socket.timeout): record['failure_category'] = 'transport_timeout'
    except (OSError, http.client.HTTPException): record['failure_category'] = 'transport_failure'
    finally:
        connection.close()
        if case != 'connection_error':
            server.shutdown(); worker.join(); server.server_close()
        persist()
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--arguments', required=True, type=Path)
    parser.add_argument('--fixture', required=True, type=Path)
    parser.add_argument('--case', required=True)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--timeout', required=True, type=float)
    parser.add_argument('--maximum-body', required=True, type=int)
    parser.add_argument('--maximum-response', required=True, type=int)
    args = parser.parse_args()
    execute(json.loads(args.arguments.read_bytes()), json.loads(args.fixture.read_bytes()), args.case,
            args.out, args.timeout, args.maximum_body, args.maximum_response)


if __name__ == '__main__': main()
