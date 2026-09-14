"""Disclosure scan over an independently derived publication inventory.

The inventory is walked here, never taken from a reported target list. Every
selected file is scanned as raw bytes; gzip members are additionally scanned
decompressed under an explicit limit. A file that cannot be read or cannot be
completely scanned prevents acceptance; it is never silently skipped.

Findings record where a value occurred, never the matching bytes, so a scan
report can be published without re-emitting what it detected.

Finalization order (see FINALIZATION): the scan runs after every other artifact
is written. Each later write is structurally restricted to digests, counts,
booleans and fixed strings, so nothing produced after the scan can carry the
value. That replaces a self-referential hash of the report inside itself.
"""
import base64
import binascii
import gzip
import hashlib
from pathlib import Path

VERSION = 'r6-publication-scan-1'
LIMIT = 64*1024**2
FINALIZATION = ('artifacts', 'scan', 'scan_report', 'report_scan', 'terminal_event', 'seal')
# Post-scan records may only carry these value shapes; see safe_record.
SAFE = (bool, int, type(None))


def forms(value):
    """The declared encoded forms covered by a scan."""
    raw = value.encode()
    covered = {'utf-8': raw, 'utf-8-lower': value.lower().encode(), 'utf-8-upper': value.upper().encode(),
               'base64': base64.b64encode(raw), 'hex': binascii.hexlify(raw),
               'utf-16-le': value.encode('utf-16-le'), 'utf-16-be': value.encode('utf-16-be')}
    if any(not pattern for pattern in covered.values()):
        raise ValueError('Refusing to scan for an empty pattern')
    return covered


def occurrences(data, patterns):
    found = []
    for name, pattern in patterns.items():
        start = data.find(pattern)
        while start >= 0:
            found.append({'form': name, 'offset': start})
            start = data.find(pattern, start+1)
    return found


def scan_file(path, patterns, root, limit=LIMIT):
    entry = {'path': str(Path(path).relative_to(root)), 'sha256': None, 'bytes': None,
             'streams': [], 'scanned': False, 'error': None, 'findings': []}
    try:
        data = Path(path).read_bytes()
    except OSError as error:
        entry['error'] = 'unreadable: '+type(error).__name__
        return entry
    entry['sha256'], entry['bytes'] = hashlib.sha256(data).hexdigest(), len(data)
    entry['streams'].append('raw')
    entry['findings'] += [{'stream': 'raw', **hit} for hit in occurrences(data, patterns)]
    if data[:2] == b'\x1f\x8b':
        try:
            with gzip.open(path, 'rb') as handle:
                plain = handle.read(limit+1)
        except (OSError, EOFError, gzip.BadGzipFile) as error:
            entry['error'] = 'undecompressible: '+type(error).__name__
            return entry
        if len(plain) > limit:
            entry['error'] = 'decompression_limit_exceeded'
            return entry
        entry['streams'].append('gzip')
        entry['findings'] += [{'stream': 'gzip', **hit} for hit in occurrences(plain, patterns)]
    entry['scanned'] = True
    return entry


def inventory(roots):
    """Walk the declared trees; a reported target list is never consulted."""
    files = []
    for root in roots:
        root = Path(root)
        if root.is_file():
            files.append((root, root.parent))
        elif root.is_dir():
            files += [(p, root) for p in root.rglob('*') if p.is_file()]
        else:
            raise ValueError('Publication inventory target is missing: '+str(root))
    return sorted(files, key=lambda item: str(item[0]))


def scan(roots, canary, nonce, *, limit=LIMIT, exemptions=()):
    patterns = forms(canary)
    exempt = {str(p) for p in exemptions}
    entries, skipped = [], []
    for path, root in inventory(roots):
        if str(path) in exempt:
            skipped.append({'path': str(path), 'sha256': hashlib.sha256(Path(path).read_bytes()).hexdigest()})
            continue
        entries.append(scan_file(path, patterns, root, limit))
    incomplete = [e['path'] for e in entries if not e['scanned']]
    disclosures = [{'path': e['path'], **hit} for e in entries for hit in e['findings']]
    return {'schema_version': VERSION, 'canary_nonce': nonce, 'derivation_domain': 'r6-004-synthetic-canary-v1',
            'encoded_forms': sorted(patterns), 'decompression_limit_bytes': limit,
            'roots': [str(Path(r)) for r in roots], 'files_scanned': len(entries),
            'gzip_streams_scanned': sum('gzip' in e['streams'] for e in entries),
            'exempted_files': skipped, 'incompletely_scanned': incomplete, 'disclosures': disclosures,
            'accepted': not incomplete and not disclosures, 'inventory': entries,
            'scope': 'declared value and encoded forms over the walked inventory; not a proof of '
                     'protection against every transformation or partial disclosure'}


def safe_record(value):
    """Post-scan artifacts may only carry digests, counts, booleans, fixed keys."""
    if isinstance(value, dict):
        return all(isinstance(k, str) and safe_record(v) for k, v in value.items())
    if isinstance(value, list):
        return all(safe_record(v) for v in value)
    if isinstance(value, str):
        return bool(len(value) == 64 and all(c in '0123456789abcdef' for c in value))
    return isinstance(value, SAFE)


def final_record(report_path, canary, nonce):
    """Scan the report itself, then emit a record that cannot carry the value."""
    patterns = forms(canary)
    data = Path(report_path).read_bytes()
    hits = occurrences(data, patterns)
    value = {'schema_version': 'r6-publication-final-1', 'report_sha256': hashlib.sha256(data).hexdigest(),
             'report_bytes': len(data), 'report_findings': len(hits), 'report_clean': not hits,
             'canary_nonce_sha256': hashlib.sha256(nonce.encode()).hexdigest(),
             'finalization_order': list(FINALIZATION)}
    checked = {k: v for k, v in value.items() if k not in {'schema_version', 'finalization_order'}}
    if not safe_record(checked):
        raise ValueError('Terminal publication record carries an unrestricted value')
    return value
