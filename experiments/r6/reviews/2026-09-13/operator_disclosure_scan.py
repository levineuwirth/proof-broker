"""Operator-run scan of publication roots for the *real* credential.

The pilot's live mode never mounts the synthetic canary, so its own
publication scan searched for a value that could not be present. This script
closes that gap without moving the secret: it reads the operator's credential
file itself, hands the token to the frozen scanner as the canary, and prints
only counts and digests. Run it as the operator, never as the agent.

With `--bind-runs`, it also binds the scanned value to what each campaign run
actually sent, as four separate verdicts per run: every file of the run is in
the scan inventory at its current digest (`covered_by_scan`); the run's seal
exists and every retained hash matches on disk (`sealed_and_intact`); the
`http.json` carrying the commitment is among the sealed files at its sealed
hash (`commitment_record_sealed`); and `credential_commitment_sha256 =
sha256(domain:nonce:header)` recomputes from the credential file and the run's
nonce (`commitment_bound`). Publication acceptance stays a separate predicate.
Receipts carry only digests, counts, booleans and scanner-labelled names.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

R6 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(R6))  # publication imports its sibling `credential` by name
COMMITMENT_DOMAIN = 'r6-campaign-credential-commitment-1'


def load(name):
    spec = importlib.util.spec_from_file_location('r6_'+name, R6/(name+'.py'))
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


def sha(data): return hashlib.sha256(data).hexdigest()


def scan_roots(publication, roots, token):
    """One frozen scan per root, so identical relative paths under different roots never collide. Entries carry a root *index*;
    the root names in the report are the scanner's own labels, and absolute paths live only in the in-memory lookup."""
    per_root = [publication.scan([root], token, 'operator-credential') for root in roots]
    union = []
    for index, r in enumerate(per_root):
        for e in r['inventory']: union.append({**e, 'root_index': index})
    report = {k: per_root[0][k] for k in ('schema_version', 'canary_nonce', 'derivation_domain', 'representations', 'encoded_forms',
                                           'extra_canary_count', 'decompression_limit_bytes', 'exempted_files', 'scope')}
    report.update(roots=[x for r in per_root for x in r['roots']], files_scanned=sum(r['files_scanned'] for r in per_root),
                  gzip_streams_scanned=sum(r['gzip_streams_scanned'] for r in per_root),
                  unreadable_directories=[x for r in per_root for x in r['unreadable_directories']],
                  irregular_entries=[x for r in per_root for x in r['irregular_entries']],
                  incompletely_scanned=[x for r in per_root for x in r['incompletely_scanned']],
                  disclosures=[x for r in per_root for x in r['disclosures']], accepted=all(r['accepted'] for r in per_root),
                  inventory=union, per_root_accepted=[r['accepted'] for r in per_root])
    return report


def bind_runs(runs, header, report, roots, publication, pats):
    """Per bound run, four separate verdicts: covered by the scan, sealed and intact, commitment record sealed, commitment bound."""
    inventory = {}
    for e in report['inventory']:
        if e['path'] is not None: inventory[str(roots[e['root_index']]/e['path'])] = e['sha256']
    def digest(path):
        try: return sha(path.read_bytes())
        except OSError: return None
    receipts = []
    for run in runs:
        try: files = sorted(p for p in run.rglob('*') if p.is_file())
        except OSError: files = []
        read_failures = sum(1 for p in files if digest(p) is None)
        covered = bool(files) and read_failures == 0 and any(run.is_relative_to(r) for r in roots) and all(inventory.get(str(p)) == digest(p) for p in files)
        seal_path = run/'seal.json'; sealed = commitment_sealed = False; retained = {}
        if seal_path.exists():
            try:
                seal = json.loads(seal_path.read_bytes()); retained = seal['retained_sha256']; ephemeral = seal['ephemeral_sha256']
                listed = set(retained) | set(ephemeral) | {'seal.json'}
                present = {str(p.relative_to(run)) for p in files}
                # every retained hash matches, and nothing is present that the seal does not list: later additions break intactness
                sealed = bool(retained) and all((run/k).is_file() and digest(run/k) == v for k, v in retained.items()) and present <= listed
            except (ValueError, KeyError, TypeError, OSError): sealed = False
        http = run/'stages/proposal-1/output/http.json'
        record = {}
        if http.exists():
            try: record = json.loads(http.read_bytes())
            except (ValueError, OSError): record = {}
            if not isinstance(record, dict): record = {}
            commitment_sealed = sealed and digest(http) is not None and retained.get('stages/proposal-1/output/http.json') == digest(http)
        nonce, recorded = record.get('commitment_nonce'), record.get('credential_commitment_sha256')
        expected = None if nonce is None else sha((COMMITMENT_DOMAIN+':'+nonce+':'+header).encode())
        nonce = nonce if isinstance(nonce, str) and len(nonce) == 64 and all(c in '0123456789abcdef' for c in nonce) else None
        recorded = recorded if isinstance(recorded, str) and len(recorded) == 64 and all(c in '0123456789abcdef' for c in recorded) else None
        receipts.append({'run': publication.label(run.name, pats), 'commitment_nonce': nonce, 'recorded_commitment_sha256': recorded,
                         'files': len(files), 'read_failures': read_failures, 'covered_by_scan': covered, 'sealed_and_intact': sealed,
                         'commitment_record_sealed': commitment_sealed,
                         'commitment_bound': recorded is not None and recorded == expected,
                         'seal_sha256': digest(seal_path) if seal_path.exists() else None,
                         'http_sha256': digest(http) if http.exists() else None})
    return receipts


def receipt_safe(receipt):
    """Digests, counts, booleans, None, or a scanner-labelled name; nothing else reaches the report."""
    for key, value in receipt.items():
        if key == 'run':
            if not (isinstance(value, dict) and set(value) == {'name', 'name_sha256'}): return False
        elif isinstance(value, str):
            if not (len(value) == 64 and all(c in '0123456789abcdef' for c in value)): return False
        elif not isinstance(value, (bool, int, type(None))): return False
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--credential-file', required=True)
    parser.add_argument('--report', default=str(Path(__file__).with_name('operator-disclosure-scan.json')))
    parser.add_argument('--bind-runs', nargs='*', default=[], help='campaign run directories whose credential commitments to check')
    parser.add_argument('--root', action='append', dest='roots', help='publication root to scan (repeatable; default experiments/r6)')
    args = parser.parse_args()
    args.roots = args.roots or [str(R6)]
    https, publication = load('live_https'), load('publication')
    header = https.read_credential(args.credential_file)
    token = header[len('Bearer '):]
    roots = [Path(r).resolve() for r in args.roots]
    pats = publication.patterns(token)
    report = scan_roots(publication, roots, token)
    receipts = bind_runs([Path(r).resolve() for r in args.bind_runs], header, report, roots, publication, pats)
    del token, header
    if not all(receipt_safe(r) for r in receipts): raise SystemExit('refusing to write a receipt with an unrestricted value')
    report['operator_scan'] = {'evaluated_at_unix': int(time.time()), 'credential_value_retained': False,
        'commitment_domain': COMMITMENT_DOMAIN, 'run_receipts': receipts,
        'scope': 'frozen publication.scan with the operator credential as canary; prints counts and digests only'}
    summary = {k: report[k] for k in ('files_scanned', 'gzip_streams_scanned', 'accepted')}
    summary.update(roots=[r['name'] or 'sha256:'+r['name_sha256'] for r in report['roots']],
                   unreadable=len(report['unreadable_directories']), irregular=len(report['irregular_entries']),
                   incomplete=len(report['incompletely_scanned']), disclosures=len(report['disclosures']),
                   disclosure_paths=sorted({d['path_sha256'] for d in report['disclosures']}),
                   run_receipts=receipts)
    bound = all(r['covered_by_scan'] and r['sealed_and_intact'] and r['commitment_record_sealed'] and r['commitment_bound'] for r in receipts)
    summary['bound_runs_accepted'] = bound
    # The assembled report and the printed summary are themselves scanned before anything leaves this process:
    # metadata added after the frozen scan (root labels, receipts, paths) is not exempt.
    assembled = (json.dumps(report, sort_keys=True, indent=1)+'\n').encode()
    printed = json.dumps(summary, indent=1).encode()
    if publication.occurrences(assembled, pats) or publication.occurrences(printed, pats):
        Path(args.report).write_bytes(b'{"accepted": false, "refused": "assembled report carried a credential form; nothing else written"}\n')
        print(json.dumps({'accepted': False, 'refused': 'assembled report carried a credential form', 'bound_runs_accepted': False}, indent=1))
        sys.exit(1)
    del pats
    Path(args.report).write_bytes(assembled)
    print(printed.decode())
    print(json.dumps({'bound_runs_accepted': bound}))
    sys.exit(0 if report['accepted'] and bound else 1)


def contained():
    """No exception text, and therefore no path, leaves this process: a failure is a sanitized refusal on stdout, exit 2."""
    try:
        main()
    except SystemExit:
        raise
    except BaseException as error:  # noqa: BLE001 — the whole point is containment
        sys.stderr = open(os.devnull, 'w')
        print(json.dumps({'accepted': False, 'refused': 'internal error: '+type(error).__name__, 'bound_runs_accepted': False}, indent=1))
        sys.exit(2)


if __name__ == '__main__':
    import os
    contained()
