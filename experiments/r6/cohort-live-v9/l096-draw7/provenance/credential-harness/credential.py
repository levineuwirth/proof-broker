"""Synthetic credential canary: frozen derivation, private delivery, receipt.

The canary is a deliberately non-secret test value. Publication records retain
its nonce and this derivation so a reviewer can reconstruct it; they must never
retain the value itself. A real credential is not derivable from a published
nonce, so reconstructibility here is a review property, not a disclosure.

Delivery uses a private read-only file outside the artifact tree. The value
never enters argv, the environment, or generated source: Bubblewrap `--setenv`
arguments and the stage command record would both retain it.
"""
import contextlib
import hashlib
import os
from pathlib import Path
import re
import secrets
import shutil
import tempfile

DOMAIN = 'r6-004-synthetic-canary-v1'
TAG = 'R6CANARY'
SCHEME = 'Bearer'
NONCE = re.compile(r'[0-9a-f]{64}')
# A declared wrong value for the receipt-precondition control. It is a distinct
# constant, never a mutation of the canary, so a partial match cannot pass.
WRONG = SCHEME+' r6-not-the-canary-0000000000000000'


def nonce():
    return secrets.token_hex(32)


def derive(value):
    """The frozen generator. Reviewers recompute the canary from the nonce."""
    if not isinstance(value, str) or not NONCE.fullmatch(value):
        raise ValueError('Canary nonce must be 64 lowercase hex characters')
    return TAG+hashlib.sha256((DOMAIN+':'+value).encode()).hexdigest()


def header(canary):
    return SCHEME+' '+canary


def commitment(canary):
    """A synthetic-canary receipt commitment; not a scheme for real keys."""
    return hashlib.sha256(header(canary).encode()).hexdigest()


def record(value):
    return {'schema_version': 'r6-canary-1', 'nonce': value, 'derivation': DOMAIN, 'tag': TAG,
            'scheme': SCHEME, 'authorization_sha256': commitment(derive(value)),
            'delivery': 'private_read_only_file', 'value_retained': False,
            'scope': 'synthetic non-secret canary; reconstructible from this nonce by design, '
                     'unlike a real credential; receipt digest is a test commitment only'}


@contextlib.contextmanager
def delivery(value):
    """Materialize the header outside the run tree; remove it afterwards."""
    canary = derive(value)
    directory = Path(tempfile.mkdtemp(prefix='r6-credential-'))
    try:
        path = directory/'authorization'
        handle = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        try:
            os.write(handle, (header(canary)+'\n').encode())
        finally:
            os.close(handle)
        yield canary, path
    finally:
        shutil.rmtree(directory, ignore_errors=True)


def read(path):
    text = Path(path).read_text()
    if not text.endswith('\n') or text.count('\n') != 1:
        raise ValueError('Credential file must hold exactly one newline-terminated line')
    return text[:-1]
