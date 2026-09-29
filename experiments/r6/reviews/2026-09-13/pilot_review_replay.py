#!/usr/bin/env python3
"""Replay only saved R6-007 evidence in network-isolated checker processes.

No actor, provider request, credential access, proof search, or Lean compilation.
Uses recorded binaries after digest checks, reconstructed frozen validation
policies, and newly unpacked challenge/proof exports. Writes new outputs only.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import episode
import pilot_contract
import run as r6


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    dest = args.output_dir.resolve(); dest.mkdir(parents=True, exist_ok=False)
    run = ROOT/'pilot-runs/live-2'
    task = r6.get_task('verinf-d1-70'); _, expected = r6.frozen_task(task)
    pilot_contract.verify_sources()
    inputs = dest/'inputs'; inputs.mkdir()
    challenge = gzip.decompress((task.path/'challenge.ndjson.gz').read_bytes())
    solution = gzip.decompress((run/'solution.ndjson.gz').read_bytes())
    assert hashlib.sha256(challenge).hexdigest() == expected['challenge_sha256']
    assert hashlib.sha256(solution).hexdigest() == r6.read_json(run/'verdict.json')['solution_sha256']
    (inputs/'challenge.ndjson').write_bytes(challenge)
    (inputs/'solution.ndjson').write_bytes(solution)
    roles = r6.read_json(run/'provenance/roles.json')
    binaries = r6.read_json(run/'provenance/binaries.json')
    checks = {}
    for stage in ('certificate-check', 'validation-local', 'validation-whole'):
        folder = dest/stage; folder.mkdir()
        output = folder/'output'; output.mkdir()
        binary = Path(roles['verifier' if stage == 'certificate-check' else 'checker'])
        assert r6.sha(binary) == binaries[str(binary)]
        replacements = {'/runner/bin/program': str(binary)}
        if stage == 'certificate-check':
            replacements['/evidence.json'] = str(run/'evidence.json')
        else:
            kind = stage.removeprefix('validation-')
            policy = episode.local_policy(task) if kind == 'local' else r6.policy([task.whole], True, task=task)
            assert policy == r6.read_json(run/'validation-input'/kind/'policy.json')
            r6.write_json(folder/'policy.json', policy)
            replacements.update({'/policy.json': str(folder/'policy.json'),
                '/challenge.ndjson': str(inputs/'challenge.ndjson'), '/solution.ndjson': str(inputs/'solution.ndjson')})
        command = list(r6.read_json(run/'stages'/stage/'command.json')['argv'])
        for i, value in enumerate(command):
            if value == '--ro-bind' and command[i+2] in replacements:
                command[i+1] = replacements[command[i+2]]
            elif value == '--bind':
                assert command[i+2] == '/out'
                command[i+1] = str(output)
        assert '--unshare-all' in command and '/credential' not in command
        r6.write_json(folder/'command.json', command)
        started = time.monotonic()
        p = subprocess.run(command, capture_output=True, timeout=150)
        (folder/'stdout').write_bytes(p.stdout); (folder/'stderr').write_bytes(p.stderr)
        assert p.returncode == 0, (stage, p.returncode, p.stderr.decode(errors='replace')[:1000])
        verdict = r6.read_json(output/'verdict.json')
        assert verdict['accepted'] is True
        if stage == 'certificate-check':
            old = r6.read_json(run/'certificate-verdict.json')
        else:
            old = json.loads(gzip.decompress((run/(stage+'.raw.json.gz')).read_bytes()))
        assert verdict == old, stage+' replay differs from saved verdict'
        checks[stage] = {'accepted': True, 'byte_identical_report': (output/'verdict.json').read_bytes() ==
                        (run/'certificate-verdict.json').read_bytes() if stage == 'certificate-check' else
                        (output/'verdict.json').read_bytes() == gzip.decompress((run/(stage+'.raw.json.gz')).read_bytes()),
                        'semantic_report_equality': True, 'binary_sha256': r6.sha(binary),
                        'report_sha256': r6.sha(output/'verdict.json'),
                        'checked_declarations': verdict.get('checked_declarations'),
                        'elapsed_seconds': time.monotonic()-started}
        print(stage+': accepted, saved verdict reproduced', flush=True)
    r6.write_json(dest/'result.json', {'passed': True, 'stages': checks,
        'program_sha256': r6.sha(Path(__file__)), 'solution_sha256': hashlib.sha256(solution).hexdigest(),
        'challenge_sha256': hashlib.sha256(challenge).hexdigest(), 'live_model_calls': 0, 'credential_reads': 0,
        'scope': 'fresh certificate verification and kernel replay of saved exports; no reconstruction, '
                 'compilation or inference attestation; recorded executables, current host shared libraries'})


if __name__ == '__main__': main()
