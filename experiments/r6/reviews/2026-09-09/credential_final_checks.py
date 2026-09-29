#!/usr/bin/env python3
"""Independent recount and publication gate for the R6-004 credential checkpoint.

Recomputes suite hashes/counts, event chains, seals and audits, and scans the
complete declared publication bundle — episode trees, process logs, suite and
checkpoint metadata, report, review files, frozen policies and locked sources —
against every episode's canary at once. The episode population must equal the
frozen native case set, and every process log must be present: an absent target
is an error, never a clean zero.

Disclosure counts are reported by population. The reflected control retains one
deliberate synthetic disclosure; that is research evidence, not a clean bundle,
and it is never folded into a blanket zero. It executes nothing.

Run with `python3 -B` so no bytecode is written into the scanned tree.
"""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

import credential                                   # noqa: E402
import credential_audit as auditor                  # noqa: E402
import credential_contract as contract              # noqa: E402
import credential_episode as harness                # noqa: E402
import events                                       # noqa: E402
import instrument                                   # noqa: E402
import publication                                  # noqa: E402
import run as r6                                    # noqa: E402
import task_spec                                    # noqa: E402
from test_credentials import GATES_FILE, GATE_CASES, NATIVE_CASES, NATIVE_CONTRACT, SUITE_CASES  # noqa: E402

BASE = 'ac0f50f'
# Must mirror `test_credentials.snapshot`; a divergence fails membership below.
SNAPSHOT_ROOTS = ('experiments/r6/tasks', 'experiments/r6/runs', 'experiments/r6/policies',
                  'experiments/r6/schema', 'experiments/r6/prompts', 'experiments/c1-cert-recovery')
DECLARATIONS = ('canary_derivation', 'publication_representations', 'publication_encoded_forms',
                'live_model_calls', 'scope')


def require(condition, message):
    if not condition: raise ValueError('R6-004 recount: '+message)


def bundle_roots(checkpoint):
    """The declared publication selection; a missing target fails the scan."""
    roots = [checkpoint, ROOT/'R6-004.md', Path(__file__).parent]
    roots += [contract.CONFIG, contract.LOCK]
    roots += [ROOT/name for name in contract.FILES]
    return roots


def check_declarations(index):
    """Bind the checkpoint's own declarations to their authoritative sources."""
    import test_credentials as harness_module
    require(index['policy_sha256'] == r6.sha(contract.CONFIG), 'checkpoint policy digest differs from the frozen policy')
    require(index['source_lock_sha256'] == r6.sha(contract.LOCK), 'checkpoint source-lock digest differs from the frozen lock')
    authoritative = {'canary_derivation': credential.DOMAIN,
                     'publication_representations': list(publication.REPRESENTATIONS),
                     'publication_encoded_forms': list(publication.FORMS),
                     'live_model_calls': 0}
    for field, value in authoritative.items():
        require(index[field] == value, 'checkpoint declaration differs from its authority: '+field)
    require(isinstance(index.get('scope'), str) and index['scope'], 'checkpoint scope statement is absent')
    return {field: index[field] for field in DECLARATIONS}


def verify_preservation(checkpoint):
    """Membership and values from the pinned commit, not from the supplied file.

    A count check alone would still admit a substituted inventory, so the exact
    path population comes from `git ls-tree` and every content digest from the
    committed blob.
    """
    records = r6.read_json(checkpoint/'prior-artifacts.sha256.json')
    listed = r6.command(['git', '-C', str(instrument.REPO), 'ls-tree', '-r', '--name-only',
                         BASE, *SNAPSHOT_ROOTS]).splitlines()
    require(sorted(records) == sorted(listed), 'preservation inventory differs from the pinned commit population')
    require(records, 'preservation inventory is empty')
    changed, mismatched = [], []
    for start in range(0, len(listed), 200):
        chunk = listed[start:start+200]
        proc = subprocess.run(['git', '-C', str(instrument.REPO), 'cat-file', '--batch'],
                              input='\n'.join(BASE+':'+path for path in chunk).encode(),
                              stdout=subprocess.PIPE, check=True)
        data, offset = proc.stdout, 0
        for path in chunk:
            end = data.index(b'\n', offset)
            _, kind, size = data[offset:end].decode().split()
            require(kind == 'blob', 'pinned object is not a blob: '+path)
            content = data[end+1:end+1+int(size)]
            offset = end+1+int(size)+1
            if hashlib.sha256(content).hexdigest() != records[path]:
                mismatched.append(path)
            local = instrument.REPO/path
            if not local.is_file() or r6.sha(local) != records[path]:
                changed.append(path)
    require(not mismatched, 'preservation inventory disagrees with the pinned commit content')
    require(not changed, 'a pre-existing artifact changed')
    return {'files': len(records), 'membership_source': 'git ls-tree at '+BASE,
            'values_source': 'git cat-file at '+BASE, 'changed_or_missing': 0}


def case_contract(checkpoint, index, episodes):
    """The complete-checkpoint gate: frozen case sets and per-case agreement.

    Case sets come from the frozen module, never from a suite's own declared
    `expected_cases`, and every native case is bound to its task, policy case,
    predicates and seal.
    """
    require(set(index['suites']) == set(SUITE_CASES), 'checkpoint suite inventory differs from the frozen module')
    declarations = check_declarations(index)
    suites, total = {}, 0
    for name, frozen_cases in SUITE_CASES.items():
        raw = (checkpoint/name).read_bytes()
        value = json.loads(raw)
        digest = hashlib.sha256(raw).hexdigest()
        require(digest == index['suites'][name]['sha256'], 'suite hash differs: '+name)
        require(len(value['checks']) == index['suites'][name]['count'] == value['check_count'], 'suite count differs: '+name)
        names = [c['name'] for c in value['checks']]
        require(sorted(names) == sorted(set(names)), 'duplicate suite case: '+name)
        require(names == list(frozen_cases), 'suite case set differs from the frozen module: '+name)
        require(value['expected_cases'] == list(frozen_cases), 'declared case set differs from the frozen module: '+name)
        require(value['passed'] is True and all(c['passed'] for c in value['checks']), 'suite did not pass: '+name)
        suites[name] = {'sha256': digest, 'count': len(names), 'frozen_case_set': True, 'duplicates': 0}
        total += len(names)

    records = {c['name']: c['detail'] for c in json.loads((checkpoint/'credential-native.json').read_bytes())['checks']}
    for name, spec in NATIVE_CONTRACT.items():
        directory = checkpoint/name
        policy = r6.read_json(directory/'search-policy.json')
        summary = r6.read_json(directory/'credential-summary.json')
        seal = r6.read_json(directory/'seal.json')
        observed = episodes[name]
        require(policy['case'] == spec['case'], 'episode directory holds a different canned case: '+name)
        require(summary['task_id'] == spec['task_id'] and policy['task_id'] == spec['task_id'],
                'episode directory holds a different task: '+name)
        require(seal['accepted'] is spec['accepted'], 'retained seal disagrees with the frozen contract: '+name)
        record = records[name]
        for field in ('accepted', 'credential_receipt_accepted', 'publication_accepted', 'failure_category'):
            require(observed[field] == spec[field], f're-audited {field} differs from the frozen contract: {name}')
            require(record[field] == spec[field], f'native suite record differs from the frozen contract: {name}')
        require(record['seal_sha256'] == r6.sha(directory/'seal.json'),
                'native suite record seal digest differs from the episode: '+name)
        require(record['files_scanned'] == observed['scan_coverage']['files_scanned'],
                'native suite record scan count differs from the episode: '+name)
        require(record['disclosures'] == observed['recorded_disclosures'],
                'native suite record disclosure count differs from the episode: '+name)
        require(record['outer_log_clean'] is observed['outer_log_clean'],
                'native suite record log result differs from recomputation: '+name)
        # Both sides audit the original tree, so coverage is comparable here; a
        # retained-only re-audit keeps its own `recorded_not_recomputed` figure.
        require(record['coverage'] == observed['scan_coverage'],
                'native suite record coverage differs from the re-audited episode: '+name)
    return suites, total, declarations


def publication_gate(checkpoint):
    """The population and disclosure gate; usable against a partial run."""
    sealed = sorted(p.name for p in checkpoint.iterdir() if (p/'seal.json').exists())
    require(sealed == sorted(NATIVE_CASES), 'episode population differs from the frozen native case set')
    for name in NATIVE_CASES:
        require((checkpoint/(name+'.log')).is_file(), 'missing episode process log: '+name)

    episodes, canaries, event_hashes, sealed_entries = {}, {}, 0, 0
    for name in NATIVE_CASES:
        directory = checkpoint/name
        seal = r6.read_json(directory/'seal.json')
        rows = events.read(directory/'events.ndjson')
        require(len(rows) == seal['event_count'] and rows[-1]['event_hash'] == seal['last_event_hash'], 'seal/receipt mismatch')
        event_hashes += len(rows)
        sealed_entries += len(seal['retained_sha256'])
        require(all(r6.sha(directory/n) == h for n, h in seal['retained_sha256'].items()), 'sealed artifact changed')
        record = r6.read_json(directory/'credential-canary.json')
        canary = credential.derive(record['nonce'])
        require(canary not in json.dumps(record), 'canary record retains the value')
        canaries[name] = canary
        task = task_spec.get(r6.read_json(directory/'credential-summary.json')['task_id'])
        result = auditor.audit(directory, task)
        recorded = r6.read_json(directory/'publication-scan.json')
        log = publication.scan([checkpoint/(name+'.log')], canary, record['nonce'])
        episodes[name] = {'accepted': result['accepted'], 'proof_accepted': result['proof_accepted'],
            'outer_log_clean': log['accepted'],
            'credential_receipt_accepted': result['credential_receipt_accepted'],
            'publication_accepted': result['publication_accepted'],
            'failure_category': result['failure_category'],
            'recorded_disclosures': len(recorded['disclosures']), 'events': len(rows),
            'sealed_files': len(seal['retained_sha256']), 'seal_sha256': r6.sha(directory/'seal.json'),
            'scan_coverage': result['coverage'], 'canary_reconstructed_from_nonce': True}

    order = list(NATIVE_CASES)
    bundle = publication.scan(bundle_roots(checkpoint), canaries[order[0]],
                              r6.read_json(checkpoint/order[0]/'credential-canary.json')['nonce'],
                              extra_canaries=[canaries[n] for n in order[1:]])
    require(not bundle['unreadable_directories'] and not bundle['irregular_entries'],
            'the publication bundle could not be fully enumerated')
    require(not bundle['incompletely_scanned'], 'a publication artifact could not be completely scanned')
    expected, unexpected, in_accepted = [], [], []
    for hit in bundle['disclosures']:
        location = hit['path'] or ''
        owner = next((n for n in NATIVE_CASES if location.startswith(checkpoint.name+'/'+n+'/')
                      or location.startswith(n+'/')), None)
        if owner is None:
            unexpected.append(hit)
        elif episodes[owner]['publication_accepted']:
            in_accepted.append(hit)
        elif episodes[owner]['recorded_disclosures']:
            expected.append({**hit, 'episode': owner})
        else:
            unexpected.append(hit)
    require(not unexpected, 'unexpected canary disclosure in the publication bundle')
    require(not in_accepted, 'a publication-accepted episode discloses a canary')
    require(len(expected) == sum(e['recorded_disclosures'] for e in episodes.values()),
            'bundle disclosures disagree with the recorded per-episode counts')

    return {'episodes': episodes, 'canaries': canaries, 'population': sealed,
            'event_hashes': event_hashes, 'sealed_entries': sealed_entries, 'bundle': bundle,
            'expected': expected, 'unexpected': unexpected, 'in_accepted': in_accepted}


def recount(checkpoint):
    index = r6.read_json(checkpoint/'checkpoint.json')
    require(index.get('passed') is True, 'checkpoint is not marked complete')
    gate = publication_gate(checkpoint)
    suites, total, declarations = case_contract(checkpoint, index, gate['episodes'])
    preservation = verify_preservation(checkpoint)
    audit_records = {c['name']: c['detail'] for c in
                     json.loads((checkpoint/'credential-audits.json').read_bytes())['checks']}
    claimed = audit_records['prior_artifacts_preserved']
    require(claimed['git_base'] == BASE and claimed['checked_files'] == preservation['files']
            and claimed['changed'] == 0 and claimed['missing'] == 0,
            'preservation suite record differs from the verified population')
    episodes, bundle = gate['episodes'], gate['bundle']
    expected, unexpected, in_accepted = gate['expected'], gate['unexpected'], gate['in_accepted']
    event_hashes, sealed_entries, sealed, canaries = (gate['event_hashes'], gate['sealed_entries'],
                                                      gate['population'], gate['canaries'])
    compiled = subprocess.run([sys.executable, '-m', 'py_compile',
                               *[str(ROOT/n) for n in contract.FILES if n.endswith('.py')]], capture_output=True)
    return {'passed': True, 'scope': 'artifact recomputation and a complete publication-bundle scan after the '
            'native suite; no additional execution, credential experiment, TLS, remote receipt, compilation or '
            'inference attestation',
        'recount_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'base_commit': BASE,
        'suites': suites, 'total_checks': total, 'episodes': episodes, 'episode_population': sealed,
        'episode_population_matches_frozen_cases': True, 'process_logs_present': len(NATIVE_CASES),
        'event_hashes_recomputed': event_hashes, 'sealed_entries_checked': sealed_entries,
        'canary_derivation': credential.DOMAIN, 'canaries_scanned': len(canaries),
        'bundle_roots': bundle['roots'], 'bundle_files_scanned': bundle['files_scanned'],
        'bundle_gzip_streams_scanned': bundle['gzip_streams_scanned'],
        'disclosures_expected_synthetic': len(expected),
        'disclosures_expected_detail': expected,
        'disclosures_unexpected': len(unexpected),
        'disclosures_in_publication_accepted_episodes': len(in_accepted),
        'disclosure_population_note': 'the reflected control deliberately retains its synthetic canary as research '
            'evidence; the bundle is not clean, and no blanket zero is claimed for it',
        'publication_representations': list(publication.REPRESENTATIONS),
        'publication_encoded_forms': list(publication.FORMS),
        'publication_decompression_limit_bytes': publication.LIMIT,
        'finalization_order': list(publication.FINALIZATION),
        'prior_files_checked': preservation['files'], 'prior_changed_or_missing': [],
        'preservation': preservation, 'checkpoint_declarations': declarations,
        'policy_sha256': r6.sha(contract.CONFIG), 'source_lock_sha256': r6.sha(contract.LOCK),
        'runtime_lock_sha256': r6.sha(contract.RUNTIME), 'prompt_sha256': r6.sha(contract.PROMPT),
        'declared_cases': list(harness.CASES), 'python_compile_exit': compiled.returncode,
        'live_model_calls': 0, 'live_model_cost_usd': 0, 'real_credentials_used': 0}


def gate_suite(checkpoint):
    """Validate the gate probes' own suite.

    This cannot live inside `recount`: those probes call `recount` against a
    checkpoint that necessarily predates their own results. It runs at
    publication instead, so the record is still bound and the function under
    test is unchanged.
    """
    index = r6.read_json(checkpoint/'checkpoint.json')
    record = index.get('gates')
    require(isinstance(record, dict), 'checkpoint declares no gate-suite record')
    raw = (checkpoint/GATES_FILE).read_bytes()
    value = json.loads(raw)
    names = [c['name'] for c in value['checks']]
    require(hashlib.sha256(raw).hexdigest() == record['sha256'], 'gate suite hash differs')
    require(len(value['checks']) == record['count'] == value['check_count'], 'gate suite count differs')
    require(names == list(GATE_CASES) and value['expected_cases'] == list(GATE_CASES),
            'gate suite case set differs from the frozen module')
    require(value['passed'] is True and all(c['passed'] for c in value['checks']), 'gate suite did not pass')
    require(all(c['detail'].get('unmutated_copy_passes') is True for c in value['checks']),
            'a gate probe did not first confirm its unmutated copy passes')
    return {'sha256': record['sha256'], 'count': len(names), 'frozen_case_set': True,
            'scope': 'validated at publication; the probes call recount against a checkpoint '
                     'that predates their own results, so recount cannot validate this suite'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint', type=Path, default=ROOT/'runs/credential-checkpoint-v3')
    parser.add_argument('--development-policy-dir', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.development_policy_dir: contract.development(args.development_policy_dir)
    checkpoint = args.checkpoint.resolve()
    result = recount(checkpoint)
    result['gate_suite'] = gate_suite(checkpoint)
    result['total_checks'] += result['gate_suite']['count']
    require(not result['prior_changed_or_missing'], 'a pre-existing artifact changed')
    require(result['python_compile_exit'] == 0, 'policy sources do not compile')
    destination = args.output or (args.checkpoint/'final-checks.json')
    r6.write_json(destination, result)
    print(json.dumps({k: v for k, v in result.items() if not isinstance(v, (dict, list))}, indent=1))


if __name__ == '__main__':
    main()
