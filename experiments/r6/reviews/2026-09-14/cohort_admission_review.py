#!/usr/bin/env python3
"""Focused contract-type probes at production admission; no transport or credential."""
import argparse
import copy
from pathlib import Path
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import cohort_contract as contract
import cohort_budget as budget
import pricing_gate_v3 as gate
import run as r6

CASES = ('baseline', 'integer_option_as_float', 'boolean_option_as_integer')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', required=True, type=Path)
    args = p.parse_args(); assert not args.output.exists()
    policy = contract.config(); scientific = contract.contract()
    request = budget.request(r6.get_task('verinf-d1-70'), r6.read_json(ROOT/'runs/provider-checkpoint-v1/d1_valid/prepared.json'))
    original = budget.arguments(request); results = {}
    for name, field, value in [('baseline', None, None), ('integer_option_as_float', 'max_output_tokens', 4096.0), ('boolean_option_as_integer', 'store', 0)]:
        arguments = copy.deepcopy(original)
        if field is not None:
            assert type(value) is not type(arguments[field]) and value == arguments[field]
            arguments[field] = value
            assert gate.entity_body(arguments) != gate.entity_body(original)
        admission = gate.admission(policy, scientific, contract.PROMPT.read_text(), ROOT/policy['pricing_sources'], arguments, request, time.time())
        results[name] = {'admission_accepted': admission['accepted'], 'changed_field': field,
                         'expected_type': type(original[field]).__name__ if field else None,
                         'observed_type': type(value).__name__ if field else None,
                         'expected_entity_sha256': gate.sha(gate.entity_body(original)),
                         'actual_entity_sha256': gate.sha(gate.entity_body(arguments)),
                         'entity_bytes_equal': gate.entity_body(arguments) == gate.entity_body(original)}
    assert set(results) == set(CASES)
    record = {'complete': True, 'scope': 'production shared admission predicate only; no actor or provider transmission',
              'results': results, 'program_sha256': r6.sha(Path(__file__)), 'live_model_calls': 0, 'real_credentials_read': 0}
    r6.write_json(args.output, record)
    print({k: (v['admission_accepted'], v['entity_bytes_equal']) for k, v in results.items()})


if __name__ == '__main__': main()
