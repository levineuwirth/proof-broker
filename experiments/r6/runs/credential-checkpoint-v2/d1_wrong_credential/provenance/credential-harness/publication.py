"""Disclosure scan over an independently derived publication inventory.

The inventory is walked here with explicit error handling, never taken from a
reported target list. A subtree that cannot be enumerated, a symlink, or any
non-regular entry prevents acceptance; nothing is silently skipped. Every
selected file is scanned as raw bytes; gzip members are additionally scanned
decompressed under an explicit limit.

Both credential representations are covered: the bare token and the complete
`Bearer <token>` Authorization value. Encoding the whole header changes the
alignment, so token-only patterns miss it. Overlapping matches are reported
separately per representation rather than de-duplicated.

Findings record where a value occurred, never the matching bytes. A path that
would itself re-emit the value is reported by digest instead of by name, and
counts as a disclosure in its own right.

Finalization order (see FINALIZATION): the scan runs after every other artifact
is written. Each later write is structurally restricted to an exact key set of
digests, counts and booleans, so nothing produced after the scan can carry the
value. That replaces a self-referential hash of the report inside itself.
"""
import base64
import binascii
import gzip
import hashlib
from pathlib import Path

import credential

VERSION = 'r6-publication-scan-2'
LIMIT = 64*1024**2
REPRESENTATIONS = ('token', 'authorization')
FORMS = ('utf-8', 'utf-8-lower', 'utf-8-upper', 'base64', 'hex', 'utf-16-le', 'utf-16-be')
FINALIZATION = ('artifacts', 'scan', 'scan_report', 'report_scan', 'terminal_event', 'seal')
# Declarative fields are excluded from the value restriction and pinned by name.
FINAL_KEYS = ('report_sha256', 'report_bytes', 'report_findings', 'report_clean', 'canary_nonce_sha256')
DECLARATIVE = ('schema_version', 'finalization_order')
TERMINAL_KEYS = ('accepted', 'proof_accepted', 'credential_receipt_accepted', 'publication_accepted',
                 'summary_sha256', 'publication_scan_sha256', 'publication_final_sha256')
SAFE = (bool, int, type(None))


def forms(value):
    raw = value.encode()
    return {'utf-8': raw, 'utf-8-lower': value.lower().encode(), 'utf-8-upper': value.upper().encode(),
            'base64': base64.b64encode(raw), 'hex': binascii.hexlify(raw),
            'utf-16-le': value.encode('utf-16-le'), 'utf-16-be': value.encode('utf-16-be')}


def patterns(canary):
    """Declared forms of both the token and the complete Authorization value."""
    result = {}
    for representation, value in (('token', canary), ('authorization', credential.header(canary))):
        for name, pattern in forms(value).items():
            if not pattern:
                raise ValueError('Refusing to scan for an empty pattern')
            result[representation+':'+name] = pattern
    if sorted(result) != sorted(r+':'+f for r in REPRESENTATIONS for f in FORMS):
        raise ValueError('Declared representation/form coverage changed')
    return result


def merge(*values):
    """Patterns for several canaries, so one scan covers a whole population."""
    result = {}
    for index, canary in enumerate(values):
        for name, pattern in patterns(canary).items():
            result[f'{index}:{name}'] = pattern
    return result


def occurrences(data, pats):
    found = []
    for name, pattern in pats.items():
        start = data.find(pattern)
        while start >= 0:
            representation, _, form = name.rpartition(':')
            found.append({'representation': representation, 'form': form, 'offset': start})
            start = data.find(pattern, start+1)
    return sorted(found, key=lambda hit: (hit['offset'], hit['representation'], hit['form']))


def identify(relative, pats):
    """Never re-emit a path that itself carries the value; report its digest."""
    raw = relative.encode()
    digest = hashlib.sha256(raw).hexdigest()
    hits = occurrences(raw, pats)
    return {'path': None if hits else relative, 'path_sha256': digest}, hits


def scan_data(data, pats, identity):
    entry = {**identity, 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data),
             'streams': ['raw'], 'scanned': True, 'error': None,
             'findings': [{'stream': 'raw', **hit} for hit in occurrences(data, pats)]}
    return entry


def scan_file(path, pats, root, limit=LIMIT):
    relative = str(Path(path).relative_to(root))
    identity, path_hits = identify(relative, pats)
    entry = {**identity, 'sha256': None, 'bytes': None, 'streams': [], 'scanned': False, 'error': None,
             'findings': [{'stream': 'path', **hit} for hit in path_hits]}
    try:
        data = Path(path).read_bytes()
    except OSError as error:
        entry['error'] = 'unreadable: '+type(error).__name__
        return entry
    entry.update(scan_data(data, pats, identity))
    entry['findings'] = [{'stream': 'path', **hit} for hit in path_hits]+entry['findings']
    if data[:2] == b'\x1f\x8b':
        try:
            with gzip.open(path, 'rb') as handle:
                plain = handle.read(limit+1)
        except (OSError, EOFError, gzip.BadGzipFile) as error:
            entry['scanned'] = False
            entry['error'] = 'undecompressible: '+type(error).__name__
            return entry
        if len(plain) > limit:
            entry['scanned'] = False
            entry['error'] = 'decompression_limit_exceeded'
            return entry
        entry['streams'].append('gzip')
        entry['findings'] += [{'stream': 'gzip', **hit} for hit in occurrences(plain, pats)]
    return entry


def inventory(roots):
    """Fail-closed traversal: report what could not be enumerated or classified."""
    files, unreadable, irregular = [], [], []
    for root in roots:
        root = Path(root)
        if not root.exists():
            raise ValueError('Publication inventory target is missing: '+str(root))
        if root.is_symlink() or (not root.is_dir() and not root.is_file()):
            irregular.append({'root': str(root), 'name': root.name, 'kind': 'symlink' if root.is_symlink() else 'non_regular'})
            continue
        if root.is_file():
            files.append((root, root.parent))
            continue
        stack = [root]
        while stack:
            directory = stack.pop()
            try:
                entries = sorted(directory.iterdir())
            except OSError as error:
                unreadable.append({'root': str(root), 'directory': str(directory.relative_to(root)) or '.',
                                   'error': type(error).__name__})
                continue
            for entry in entries:
                if entry.is_symlink():
                    irregular.append({'root': str(root), 'name': str(entry.relative_to(root)), 'kind': 'symlink'})
                elif entry.is_dir():
                    stack.append(entry)
                elif entry.is_file():
                    files.append((entry, root))
                else:
                    irregular.append({'root': str(root), 'name': str(entry.relative_to(root)), 'kind': 'non_regular'})
    return sorted(files, key=lambda item: str(item[0])), unreadable, irregular


def scan(roots, canary, nonce, *, limit=LIMIT, extra_canaries=()):
    pats = merge(canary, *extra_canaries) if extra_canaries else patterns(canary)
    files, unreadable, irregular = inventory(roots)
    entries = [scan_file(path, pats, root, limit) for path, root in files]
    incomplete = [{'path': e['path'], 'path_sha256': e['path_sha256'], 'error': e['error']}
                  for e in entries if not e['scanned']]
    disclosures = [{'path': e['path'], 'path_sha256': e['path_sha256'], **hit} for e in entries for hit in e['findings']]
    return {'schema_version': VERSION, 'canary_nonce': nonce, 'derivation_domain': credential.DOMAIN,
            'representations': list(REPRESENTATIONS), 'encoded_forms': list(FORMS),
            'extra_canary_count': len(extra_canaries), 'decompression_limit_bytes': limit,
            'roots': [str(Path(r)) for r in roots], 'files_scanned': len(entries),
            'gzip_streams_scanned': sum('gzip' in e['streams'] for e in entries),
            'unreadable_directories': unreadable, 'irregular_entries': irregular,
            'exempted_files': [], 'incompletely_scanned': incomplete, 'disclosures': disclosures,
            'accepted': not incomplete and not disclosures and not unreadable and not irregular,
            'inventory': entries,
            'scope': 'declared representations and encoded forms over the walked inventory; symlinks and '
                     'non-regular entries are rejected, not followed; not a proof of protection against '
                     'every transformation or partial disclosure'}


def safe_record(value, allowed):
    """Post-scan artifacts carry an exact key set of digests, counts and booleans."""
    if not isinstance(value, dict) or set(value) != set(allowed):
        return False
    for key, item in value.items():
        if isinstance(item, str):
            if not (len(item) == 64 and all(c in '0123456789abcdef' for c in item)):
                return False
        elif not isinstance(item, SAFE):
            return False
    return True


def final_record(report_path, canary, nonce):
    """Scan the report itself, then emit a record that cannot carry the value."""
    data = Path(report_path).read_bytes()
    hits = occurrences(data, patterns(canary))
    value = {'schema_version': 'r6-publication-final-1', 'report_sha256': hashlib.sha256(data).hexdigest(),
             'report_bytes': len(data), 'report_findings': len(hits), 'report_clean': not hits,
             'canary_nonce_sha256': hashlib.sha256(nonce.encode()).hexdigest(),
             'finalization_order': list(FINALIZATION)}
    if not safe_record({k: v for k, v in value.items() if k not in DECLARATIVE}, FINAL_KEYS):
        raise ValueError('Terminal publication record carries an unrestricted value')
    return value
