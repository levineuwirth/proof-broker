#!/usr/bin/env python3
"""Re-derive checkpoint counts and on-host provenance after native execution.

This supplements the retained-only audit. Binary/source paths must exist on
this host; matching hashes are not compilation or inference attestations.
"""
import argparse
import hashlib
from pathlib import Path
import subprocess

import instrument
import proposal_instrument as overlay
import run as r6
import test_proposals


def verify(root):
    checkpoint = r6.read_json(root/'checkpoint.json')
    assert checkpoint['passed'] is True
    report = {'checkpoint_sha256': r6.sha(root/'checkpoint.json'), 'suites': {}, 'positive_episodes': {},
              'scope': 'Recomputed retained hashes and on-host source/binary provenance after native fixture execution; '
                       'no compilation or inference attestation'}
    for name, names in [('payload-admission.json', test_proposals.UNIT_CASES),
            ('native-fixtures.json', test_proposals.NATIVE_CASES), ('audit-regressions.json', test_proposals.AUDIT_CASES)]:
        suite = r6.read_json(root/name)
        test_proposals.assert_complete([c['name'] for c in suite['checks']], names)
        assert suite['passed'] is True and all(c['passed'] is True for c in suite['checks'])
        assert checkpoint['suites'][name]['sha256'] == r6.sha(root/name)
        report['suites'][name] = {'checks': len(names), 'passed': True, 'sha256': r6.sha(root/name)}
    for name in ['d1_valid', 'c8_valid']:
        p = root/name
        seal, verdict = r6.read_json(p/'seal.json'), r6.read_json(p/'verdict.json')
        assert all(r6.sha(p/k) == h for k, h in seal['retained_sha256'].items())
        binaries = r6.read_json(p/'provenance/binaries.json')
        assert all(r6.sha(Path(k)) == h for k, h in binaries.items())
        sources = r6.read_json(p/'provenance/sources.json')
        assert sources == overlay.source_record()[0]
        for source, record in sources.items():
            path = overlay.DEST/source if source.startswith('sdk/') else overlay.DEST/'bridge'/source.removeprefix('lean-bridge/')
            assert r6.sha(path) == record['instrumented_sha256']
        assert all(r6.sha(Path(k['host'])) == k['sha256'] for k in r6.read_json(p/'provenance/fixture-runtime.json'))
        assert all(r6.sha(p/'provenance/harness'/k) == h for k, h in overlay.source_lock().items())
        required = [str(p/k) for k in seal['retained_sha256']]+[str(p/'seal.json')]
        ignored = subprocess.run(['git', 'check-ignore', '--stdin'], input='\n'.join(required)+'\n', text=True, capture_output=True)
        assert ignored.returncode == 1, ignored.stdout
        report['positive_episodes'][name] = {'events': seal['event_count'], 'retained_files': len(seal['retained_sha256']),
            'verified_binaries': len(binaries), 'verified_base_overlay_sources': len(sources),
            'frozen_harness_sources': len(overlay.source_lock()), 'request_bytes': (p/'request.json').stat().st_size,
            'request_sha256': verdict['request_sha256'], 'solution_sha256': verdict['solution_sha256'],
            'declarations': {k: x['checked_declarations'] for k, x in verdict['final_validation'].items()},
            'axiom_delta': verdict['axiom_delta'], 'ignored_required_paths': []}
    old = r6.read_json(root/'prior-artifacts.sha256.json')
    assert all(r6.sha(instrument.REPO/p) == h for p, h in old.items())
    report['prior_artifacts'] = {'base_commit': r6.command(['git', 'rev-parse', '25c3b77']),
                               'checked_files': len(old), 'missing': 0, 'changed': 0}
    files = [str(p.relative_to(instrument.REPO)) for p in root.rglob('*') if p.is_file() and p.name != 'final-checks.json']
    ignored = subprocess.run(['git', 'check-ignore', '--stdin'], input='\n'.join(files)+'\n', text=True, capture_output=True)
    assert ignored.returncode in (0, 1)
    skip = set(ignored.stdout.splitlines())
    retained = [p for p in files if p not in skip]
    assert not any('__pycache__' in p or p.endswith('.pyc') for p in retained)
    blobs, total = {}, 0
    for p in retained:
        content = (instrument.REPO/p).read_bytes()
        total += len(content)
        blobs[hashlib.sha256(content).hexdigest()] = len(content)
    report['retention_excluding_this_report'] = {'files': len(retained), 'apparent_bytes': total,
        'unique_content_bytes': sum(blobs.values()), 'unique_blobs': len(blobs)}
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint', type=Path, required=True)
    args = parser.parse_args()
    root = args.checkpoint.resolve()
    result = verify(root)
    r6.write_json(root/'final-checks.json', result)
    print(__import__('json').dumps(result, indent=2))
