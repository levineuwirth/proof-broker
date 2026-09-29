"""R6-009 admission: the scientific contract, then pricing. Standard library only.

The contract pins everything the model can see or that shapes its answer:
the exact instruction bytes, the rendering of a request into messages, the
request schema and row semantics, the response schema, the model identity, the
generation options — including the options that must stay omitted — and the
scientific resource limits. A request binds to the contract's digest; a policy
binds to the same digest and may not disagree with the contract's generation
settings. Admission recomputes the whole envelope from the request and the
contract and compares it to what the sender is about to serialize; three
matching reported hashes are not enough. Pricing evidence is the v2 rule set,
carried unchanged, over the policy's own retained sources.
"""
import hashlib
import json
import re

import pricing_gate_v2 as v2

Failure, require, canonical, sha, strict, entity_body = v2.Failure, v2.require, v2.canonical, v2.sha, v2.strict, v2.entity_body
cost_micro, MODEL, STANDARD_ENDPOINT = v2.cost_micro, v2.MODEL, v2.STANDARD_ENDPOINT
CONTRACT_SCHEMA = 'r6-farkas-proposal-contract-1'
REQUEST_SCHEMA = 'r6-farkas-request-9'


HEX64 = re.compile(r'^[a-f0-9]{64}$')
INTEGER = re.compile(r'^-?(0|[1-9][0-9]*)$')
TASKS = ('verinf-d1-70', 'c1-c8-2p18')
BINDING_KEYS = ('task_id', 'manifest_sha256', 'challenge_sha256', 'input_ir_sha256', 'final_ir_sha256', 'prompt_sha256')


def contract_digest(contract):
    return sha(canonical(contract)+b'\n')


def same_json(a, b):
    """Byte-and-type identity of two JSON values: 4096.0 is not 4096, 0 is not false, and key sets must match exactly."""
    if type(a) is not type(b): return False
    if isinstance(a, dict): return set(a) == set(b) and all(same_json(a[k], b[k]) for k in a)
    if isinstance(a, list): return len(a) == len(b) and all(same_json(x, y) for x, y in zip(a, b))
    return a == b


def check_request_grammar(request):
    """The frozen cohort-request schema, enforced here without a schema library: exact keys, required bindings, row shape,
    integer-string grammar, nonempty populations. Parity with the schema is a host-side control."""
    require(isinstance(request, dict) and set(request) == {'schema_version', 'contract_sha256', 'binding', 'problem'}, 'contract_request_keys')
    require(request['schema_version'] == REQUEST_SCHEMA, 'contract_request_schema_version')
    require(isinstance(request['contract_sha256'], str) and HEX64.match(request['contract_sha256']), 'contract_request_digest_form')
    binding = request['binding']
    require(isinstance(binding, dict) and set(binding) == set(BINDING_KEYS), 'contract_request_binding_keys')
    require(binding['task_id'] in TASKS, 'contract_request_task')
    require(all(isinstance(binding[k], str) and HEX64.match(binding[k]) for k in BINDING_KEYS if k != 'task_id'), 'contract_request_binding_form')
    problem = request['problem']
    require(isinstance(problem, dict) and set(problem) == {'fragment', 'rows'} and problem['fragment'] == 'LIA', 'contract_request_problem_keys')
    rows = problem['rows']
    require(isinstance(rows, list) and len(rows) >= 1, 'contract_request_rows_empty')
    names = []
    for row in rows:
        require(isinstance(row, dict) and set(row) == {'name', 'relation', 'constant', 'terms'}, 'contract_request_row_keys')
        require(isinstance(row['name'], str) and row['name'] != '' and row['relation'] in ('le', 'eq'), 'contract_request_row_form')
        require(isinstance(row['constant'], str) and len(row['constant']) <= 128 and INTEGER.match(row['constant']), 'contract_request_constant_grammar')
        require(isinstance(row['terms'], list), 'contract_request_terms')
        for term in row['terms']:
            require(isinstance(term, dict) and set(term) == {'variable', 'coefficient'} and isinstance(term['variable'], str) and term['variable'] != ''
                    and isinstance(term['coefficient'], str) and len(term['coefficient']) <= 128 and INTEGER.match(term['coefficient']), 'contract_request_term_grammar')
        names.append(row['name'])
    require(len(names) == len(set(names)), 'contract_request_duplicate_row')
    return request


def check_task_join(request, task_id, manifest_sha256, challenge_sha256):
    """The request's own identity must be the funded task's: name, manifest and challenge. A matching digest is not a substitute."""
    binding = request['binding']
    require(binding['task_id'] == task_id, 'cohort_request_task_mismatch')
    require(binding['manifest_sha256'] == manifest_sha256 and binding['challenge_sha256'] == challenge_sha256, 'cohort_request_task_identity')


def check_contract(contract):
    """Structural well-formedness of a contract object; a frozen file is canonical bytes of exactly this."""
    require(contract.get('schema_version') == CONTRACT_SCHEMA, 'contract_schema')
    for key in ('name', 'instruction', 'rendering', 'request_schema', 'response_schema', 'model', 'generation', 'limits', 'scope'):
        require(key in contract, 'contract_incomplete_'+key)
    require(contract['request_schema']['schema_version'] == REQUEST_SCHEMA, 'contract_request_schema')
    gen = contract['generation']
    require(gen['options']['model'] == contract['model']['requested_id'] == v2.MODEL, 'contract_model')
    require(set(gen['options']) & set(gen['omitted']) == set() and 'input' not in gen['options'], 'contract_generation_options')
    require(gen['options']['max_output_tokens'] == contract['limits']['output_tokens'], 'contract_output_limit')
    return contract_digest(contract)


def render_arguments(contract, instruction_text, request_bytes):
    """The one rendering rule: generation options, then the two messages."""
    r = contract['rendering']
    arguments = dict(contract['generation']['options'])
    arguments['input'] = [{'role': r['system_role'], 'content': instruction_text},
                          {'role': r['user_role'], 'content': r['prefix']+sha(request_bytes)+r['separator']+request_bytes.decode()}]
    return arguments


def check_envelope(contract, instruction_text, arguments, request_bytes):
    """The actual arguments the sender will serialize equal the rendering of this request under this contract."""
    require(sha(instruction_text.encode()) == contract['instruction']['sha256'] and len(instruction_text.encode()) == contract['instruction']['bytes'],
            'contract_instruction_bytes')
    expected = render_arguments(contract, instruction_text, request_bytes)
    require(isinstance(arguments, dict) and set(arguments) == set(expected), 'contract_envelope_keys')
    for key in expected:
        if key != 'input': require(same_json(arguments[key], expected[key]), 'contract_generation_'+key)
    require(same_json(arguments['input'], expected['input']), 'contract_envelope_messages')
    require(not any(k in arguments for k in contract['generation']['omitted']), 'contract_omitted_option_present')
    require(canonical(arguments) == canonical(expected), 'contract_envelope_bytes')  # the whole envelope, byte for byte
    request = check_request_grammar(strict(request_bytes))
    require(request['contract_sha256'] == contract_digest(contract), 'contract_request_binding')
    require(request_bytes == canonical(request)+b'\n', 'contract_request_noncanonical')
    require(all(row['relation'] in contract['request_schema']['row_relations'] for row in request['problem']['rows']), 'contract_row_relation')
    limits = contract['limits']
    size = sum(len(m['content'].encode()) for m in arguments['input'])
    require(size <= limits['message_utf8_bytes'] and len(entity_body(arguments)) <= limits['maximum_request_bytes'], 'contract_input_budget')
    return {'contract_sha256': contract_digest(contract), 'request_sha256': sha(request_bytes), 'arguments_sha256': sha(canonical(arguments)),
            'body_sha256': sha(entity_body(arguments)), 'message_utf8_bytes': size}


def check_policy(policy, contract):
    """A policy serves exactly one contract and may not disagree with its generation settings or scientific limits."""
    require(policy['contract_sha256'] == contract_digest(contract), 'policy_contract_binding')
    require(same_json(policy['request'], contract['generation']['options']), 'policy_generation_conflict')
    for key, value in contract['limits'].items():
        require(key in policy['limits'] and same_json(policy['limits'][key], value), 'policy_limit_conflict_'+key)
    require(policy['model']['requested_id'] == contract['model']['requested_id'] and policy['model']['allowed_response_ids'] == contract['model']['allowed_response_ids'],
            'policy_model_conflict')


def admission(policy, contract, instruction_text, source_dir, arguments, request_bytes, now):
    """Contract first, then the v2 pricing relationships over the policy's retained sources."""
    check_contract(contract); check_policy(policy, contract)
    envelope = check_envelope(contract, instruction_text, arguments, request_bytes)
    evidence = v2.source_evidence(source_dir)
    require(type(now) in (int, float) and now > 0, 'pricing_clock')
    approved = policy['pricing_admission']
    for role, value in evidence.items():
        pin = approved['sources'][role]
        require(value['extract_sha256'] == pin['extract_sha256'], 'pricing_semantic_drift_'+role)
        require(value['raw_sha256'] == pin['raw_sha256'], 'pricing_raw_drift_'+role)
        age = now-value['finished_unix']
        require(age >= -approved['future_clock_tolerance_seconds'], 'pricing_capture_in_future')
        require(age <= approved['maximum_source_age_seconds'], 'pricing_capture_stale')
    rates = v2.rates_from(evidence)
    require(rates == policy['pricing']['nano_usd_per_token'], 'pricing_policy_rates')
    applicability = v2.check_applicability(policy, evidence, arguments)
    limits = policy['limits']
    return {'schema_version': 'r6-pricing-admission-3', 'accepted': True, 'policy_sha256': sha(canonical(policy)+b'\n'), **envelope,
            'sources': {k: {f: v[f] for f in ('raw_sha256', 'extract_sha256', 'receipt_sha256')} for k, v in evidence.items()},
            'nano_usd_per_token': rates, 'reserved_micro_usd': v2.cost_micro(limits['input_tokens_reserved'], limits['output_tokens'], rates),
            'applicability': applicability, 'evaluated_at_unix': now, 'billing_guarantee': False,
            'evidence_scope': 'envelope recomputed from the request under the contract; local retained-source, clock and request consistency; '
                              'no remote pricing or inference attestation'}
