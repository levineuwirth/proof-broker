#!/usr/bin/env python3
"""Read-only evidence and arithmetic for the proposed R6-009 design.

Reads selected public artifacts pinned to 4b8a7d9. Does not import the harness,
read a credential, launch search, or issue a network request. Output is new.
"""
import argparse
from fractions import Fraction
import gzip
import hashlib
import json
from math import comb, gcd, lcm, log, ceil
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[4]
R6 = ROOT/'experiments/r6'
BASE = '4b8a7d9'
INPUTS = {}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    raw = path.read_bytes()
    relative = str(path.relative_to(ROOT))
    committed = subprocess.check_output(['git', 'show', BASE+':'+relative], cwd=ROOT)
    assert raw == committed, relative
    INPUTS[relative] = {'sha256': sha(raw), 'bytes': len(raw)}
    return raw


def load(path):
    return json.loads(read(path))


def differences(a, b, path=''):
    if type(a) is not type(b):
        return [path]
    if isinstance(a, dict):
        return sorted([path+'/'+k for k in a.keys() ^ b.keys()] +
                      [p for k in a.keys() & b.keys()
                       for p in differences(a[k], b[k], path+'/'+k)])
    if isinstance(a, list):
        if len(a) != len(b):
            return [path+'/length']
        return [p for i, (x, y) in enumerate(zip(a, b))
                for p in differences(x, y, path+'/'+str(i))]
    return [] if a == b else [path]


def primitive(witness):
    weights = {}
    for entry in witness['coefficients']:
        name = entry['hypothesis']
        assert name not in weights
        weights[name] = Fraction(entry['coefficient'])
    weights = {k: v for k, v in weights.items() if v}
    assert weights
    denominator = lcm(*(v.denominator for v in weights.values()))
    integers = {k: int(v*denominator) for k, v in weights.items()}
    divisor = gcd(*integers.values())
    return {k: integers[k]//divisor for k in sorted(integers)}


def arithmetic(problem, witness):
    rows = {r['name']: r for r in problem['rows']}
    total, variables = 0, {}
    for entry in witness['coefficients']:
        row = rows[entry['hypothesis']]
        weight = int(entry['coefficient'])
        assert row['relation'] in ('le', 'eq')
        assert row['relation'] == 'eq' or weight >= 0
        total += weight*int(row['constant'])
        for term in row['terms']:
            key = term['variable']
            variables[key] = variables.get(key, 0)+weight*int(term['coefficient'])
    variables = {k: v for k, v in variables.items() if v}
    assert not variables and total > 0
    return {'residual_terms': variables, 'positive_constant': str(total)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    assert not args.output.exists(), 'Refusing overwrite'
    paths = [R6/'pilot-runs/live-2', R6/'campaign-runs-v7/live-1']
    requests = [load(p/'live-request.json') for p in paths]
    arguments = [load(p/'live-arguments.json') for p in paths]
    prompts = [read(p/'prompt.txt') for p in paths]
    deltas = differences(*requests)
    assert deltas == ['/policy_sha256', '/schema_version']
    assert prompts[0] == prompts[1]
    opts = [{k: v for k, v in a.items() if k != 'input'} for a in arguments]
    assert opts[0] == opts[1]
    assert arguments[0]['input'][0] == arguments[1]['input'][0]
    assert arguments[0]['input'][1] != arguments[1]['input'][1]
    observations = {}
    for p, request in zip(paths, requests):
        raw_request = read(p/'live-request.json')
        response = load(p/'validated-response.json')
        assert response['request_sha256'] == sha(raw_request)
        witness = response['witness']
        verdict = load(p/'verdict.json')
        proof = sha(gzip.decompress(read(p/'solution.ndjson.gz')))
        assert proof == verdict['solution_sha256']
        observations[str(p.relative_to(R6))] = {
            'request_sha256': sha(raw_request), 'witness': witness,
            'primitive_witness': primitive(witness),
            'arithmetic': arithmetic(request['problem'], witness),
            'proof_export_sha256': proof}
        rescaled = {'coefficients': [{**e, 'coefficient': str(2*int(e['coefficient']))}
                                    for e in witness['coefficients']]}
        assert primitive(rescaled) == primitive(witness)
        arithmetic(request['problem'], rescaled)
    assert len({json.dumps(x['primitive_witness'], sort_keys=True) for x in observations.values()}) == 2

    manifest = load(R6/'tasks/verinf-d1-70/manifest.json')
    pristine = read(R6/'tasks/verinf-d1-70/Pristine.lean')
    assert sha(pristine) == manifest['upstream']['pristine_sha256']
    sites = [i for i, line in enumerate(pristine.decode().splitlines(), 1) if 'omega' in line]
    assert sites == [69, 70, 71, 78, 96, 98, 99, 101, 158, 166, 170, 175, 178, 180, 204]

    policy = load(R6/'policies/responses-campaign-v7.json')
    limits, rates = policy['limits'], policy['pricing']['nano_usd_per_token']
    nanos = limits['input_tokens_reserved']*max(rates[k] for k in ('input', 'cached_input', 'cache_write')) + limits['output_tokens']*rates['output']
    reservation = (nanos+999)//1000
    assert reservation == 102400
    planning = []
    for n in (4, 8, 16):
        planning.append({'draws_per_task': n,
            'one_sided_95_lower_bound_if_all_succeed_iid': 0.05**(1/n),
            'one_sided_95_upper_bound_if_all_fail_iid': 1-0.05**(1/n),
            'detect_at_least_one_success_if_p_is_0_2_iid': 1-0.8**n,
            'fourteen_tasks_transmissions': 14*n,
            'fourteen_tasks_reserved_micro_usd': 14*n*reservation,
            'fifteen_tasks_transmissions': 15*n,
            'fifteen_tasks_reserved_micro_usd': 15*n*reservation})

    # Check the stated subset averages directly for every possible c, n=8.
    # These exact finite-pool identities do not establish IID provider draws.
    from itertools import combinations
    for c in range(9):
        pool = [1]*c+[0]*(8-c)
        for k in (1, 2, 4, 8):
            subsets = list(combinations(pool, k))
            at_least_one = Fraction(sum(any(s) for s in subsets), len(subsets))
            all_success = Fraction(sum(all(s) for s in subsets), len(subsets))
            assert at_least_one == 1-Fraction(comb(8-c, k), comb(8, k))
            assert all_success == Fraction(comb(c, k), comb(8, k))
    for p in ('campaign_contract.py', 'campaign_budget.py', 'campaign_ledger.py'):
        read(R6/p)
    read(ROOT/'sdk/lib/farkas_search.ml')
    result = {
        'status': 'design evidence; no frozen cohort or spending authorization',
        'git_base': subprocess.check_output(['git', 'rev-parse', BASE], cwd=ROOT, text=True).strip(),
        'observations': observations,
        'historical_input_comparison': {
            'system_prompt_sha256': sha(prompts[0]), 'same_system_prompt_bytes': True,
            'same_problem_and_binding_objects': True, 'same_request_options': True,
            'request_options': opts[0], 'model_visible_request_differences': deltas,
            'same_complete_model_input': False, 'isolates_sampling_randomness': False,
            'different_valid_observed_witnesses': True, 'estimates_failure_rate': False},
        'source_census': {'upstream': manifest['upstream'], 'textual_omega_lines': sites,
                          'textual_sites': len(sites), 'extraction_performed': False,
                          'admitted_task_count': None},
        'planning_arithmetic': planning,
        'required_all_successes_for_one_sided_95_lower_bound_at_least_0_9_iid': ceil(log(0.05)/log(0.9)),
        'recommended_draws_per_primary_task': 8,
        'sample_size_is_power_calculation': False,
        'per_draw_reservation_micro_usd_from_retained_v7_basis': reservation,
        'current_pricing_refetched': False, 'billing_guarantee': False,
        'subset_identity_checks': 36, 'positive_rescaling_controls': 2,
        'inputs': INPUTS, 'program_sha256': sha(Path(__file__).read_bytes()),
        'new_model_calls': 0, 'credential_reads': 0, 'new_native_episodes': 0,
        'policy_changes': 0, 'authorization_changes': 0,
        'scope': 'historical byte comparison, integer witness arithmetic and prospective planning formulas; no new kernel check'}
    with args.output.open('x') as f:
        json.dump(result, f, indent=2, sort_keys=True); f.write('\n')
    print(json.dumps({'completed': True, 'inputs_bound': len(INPUTS),
                      'model_visible_differences': deltas, 'planning': planning}, indent=1))


if __name__ == '__main__':
    main()
