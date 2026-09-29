"""Fresh synthetic CA and TLS keys, kept outside the publication tree."""
from contextlib import contextmanager
from pathlib import Path
import os
import shutil
import ssl
import subprocess
import tempfile

import run as r6


@contextmanager
def materialize(run, case):
    with tempfile.TemporaryDirectory(prefix='r6-005-tls-') as tmp:
        root = Path(tmp)
        commands = []
        def openssl(*argv):
            cmd = ['openssl', *argv]
            commands.append(cmd)
            subprocess.run(cmd, cwd=root, capture_output=True, check=True)
        for name in ('ca', 'other-ca', 'server'):
            openssl('genpkey', '-algorithm', 'EC', '-pkeyopt', 'ec_paramgen_curve:P-256', '-out', name+'.key')
            os.chmod(root/(name+'.key'), 0o600)
        for name in ('ca','other-ca'):
            openssl('req', '-new', '-x509', '-key', name+'.key', '-out', name+'.pem', '-days', '3',
                    '-subj', '/CN=R6 synthetic '+name, '-addext', 'basicConstraints=critical,CA:TRUE',
                    '-addext', 'keyUsage=critical,keyCertSign,cRLSign')
        openssl('req', '-new', '-key', 'server.key', '-out', 'server.csr', '-subj', '/CN=R6 canned endpoint')
        hostname = 'wrong.invalid' if case == 'wrong_hostname' else 'api.openai.com'
        (root/'extensions.cnf').write_text('basicConstraints=critical,CA:FALSE\nkeyUsage=critical,digitalSignature\nextendedKeyUsage=serverAuth\nsubjectAltName=DNS:'+hostname+'\n')
        dates = ['-not_before', '20000101000000Z', '-not_after', '20010101000000Z'] if case == 'expired_certificate' else ['-days', '2']
        openssl('x509', '-req', '-in', 'server.csr', '-CA', 'ca.pem', '-CAkey', 'ca.key', '-set_serial', '2',
                '-out', 'server.pem', '-extfile', 'extensions.cnf', *dates)
        destination = run/'tls-fixture'; destination.mkdir()
        for name in ('ca.pem','other-ca.pem','server.pem','extensions.cnf'):
            shutil.copyfile(root/name, destination/name)
        ca = root/('other-ca.pem' if case == 'untrusted_ca' else 'ca.pem')
        r6.write_json(destination/'provenance.json', {'openssl_binary':shutil.which('openssl'),
            'openssl_sha256':r6.sha(Path(shutil.which('openssl'))),
            'openssl_version':subprocess.check_output(['openssl','version']).decode().strip(),
            'commands':commands, 'hostname':hostname, 'trust_root_sha256':r6.sha(ca),
            'leaf_der_sha256':r6.hashlib.sha256(ssl.PEM_cert_to_DER_cert((root/'server.pem').read_text())).hexdigest(),
            'private_key_retained':False, 'private_directory':str(root),
            'scope':'fresh synthetic test PKI; not the deployed provider chain'})
        yield ca, root/'server.pem', root/'server.key'
