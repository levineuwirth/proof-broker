"""R6-006 source, request and price admission. Standard library only.

Source capture dates and host clocks are observations, not remote attestations.
The caller supplies already-retained bytes; no content from a page is executed.
"""
from datetime import datetime, timezone
from decimal import Decimal
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re

MODEL = 'gpt-5.4-2026-03-05'
STANDARD_ENDPOINT = {'scheme':'https','host':'api.openai.com','port':443,'path':'/v1/responses'}
URLS = {
    'model': 'https://developers.openai.com/api/docs/models/gpt-5.4',
    'caching': 'https://developers.openai.com/api/docs/guides/prompt-caching',
}


class Failure(ValueError):
    def __init__(self, code):
        super().__init__(code)
        self.code = code


def require(ok, code):
    if not ok:
        raise Failure(code)


def canonical(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(',', ':')).encode()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def entity_body(arguments):
    # The frozen HTTPS encoder escapes non-ASCII characters. Canonical data
    # hashing above deliberately keeps UTF-8; those are distinct byte domains.
    return (json.dumps(arguments,sort_keys=True,separators=(',',':'))+'\n').encode()


def strict(raw):
    def pairs(rows):
        result = {}
        for key, value in rows:
            require(key not in result, 'duplicate_json_key')
            result[key] = value
        return result
    return json.loads(raw, object_pairs_hook=pairs, parse_constant=lambda _: (_ for _ in ()).throw(Failure('nonfinite_json')))


class Text(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.hidden = 0
        self.parts = []

    def handle_starttag(self, tag, attrs):
        if tag in ('script', 'style'):
            self.hidden += 1

    def handle_endtag(self, tag):
        if tag in ('script', 'style'):
            self.hidden -= 1

    def handle_data(self, value):
        if self.hidden == 0:
            self.parts.append(value)


def price_conditions(pricing):
    long = re.findall(r'prompts with >(\d+)K input tokens are priced at (\d+(?:\.\d+)?)x input and '
        r'(\d+(?:\.\d+)?)x output for the full session for standard, batch, and flex\.', pricing)
    regional = re.findall(r'Regional processing \(data residency\) endpoints are charged a (\d+)% uplift '
        r'for GPT-5\.4 and GPT-5\.4 Pro\.', pricing)
    require(len(long)==1, 'pricing_long_context_source_clause')
    require(len(regional)==1, 'pricing_regional_source_clause')
    threshold,input_multiplier,output_multiplier=long[0]
    return {'long_context':{'input_tokens_threshold':int(threshold)*1000,'comparison':'greater_than',
                'input_multiplier':input_multiplier,'output_multiplier':output_multiplier,
                'scope':'full_session','service_tiers':['standard','batch','flex']},
            'regional_processing':{'uplift_percent':int(regional[0]),'scope':'regional_processing_endpoints'}}


def applicability_policy(conditions):
    return {'long_context':{'source_condition':conditions['long_context'],
                'input_tokens_upper_bound_exclusive':conditions['long_context']['input_tokens_threshold']},
            'regional_processing':{'source_condition':conditions['regional_processing'],
                'allowed_endpoints':[dict(STANDARD_ENDPOINT)]},
            'session_scope':'one_stateless_request'}


def check_applicability(policy, evidence, arguments):
    # Re-derive source facts. A declared non-applicable flag is not evidence.
    conditions=evidence['model']['extract']['price_conditions']
    expected=applicability_policy(conditions)
    declared=policy['pricing_admission'].get('applicability')
    require(isinstance(declared,dict) and set(declared)==set(expected),'pricing_applicability_policy')
    for kind in ('long_context','regional_processing'):
        require(canonical(declared[kind])==canonical(expected[kind]),'pricing_'+kind+'_policy')
    require(declared['session_scope']==expected['session_scope'],'pricing_session_policy')
    tokens=policy['limits']['input_tokens_reserved']
    bound=expected['long_context']['input_tokens_upper_bound_exclusive']
    require(type(tokens) is int and 0 <= tokens < bound,'pricing_long_context_out_of_scope')
    require(canonical(policy['endpoint'])==canonical(STANDARD_ENDPOINT),'pricing_regional_endpoint_out_of_scope')
    # The documented multiplier applies to the full session. No hidden previous
    # response, conversation, compaction, or tool history enters this policy.
    require(not {'previous_response_id','conversation','context_management'} & set(arguments),
            'pricing_session_out_of_scope')
    return {'source_conditions':conditions,'input_tokens_reserved':tokens,
            'input_tokens_upper_bound_exclusive':bound,'endpoint':policy['endpoint'],
            'long_context_surcharge_applicable':False,'regional_surcharge_applicable':False,
            'session_scope':'one_stateless_request',
            'scope':'local policy/input applicability under the existing token-bound assumption; not billing attestation'}


def extract(raw, role):
    parser = Text()
    parser.feed(raw.decode('utf-8')); parser.close()
    require(parser.hidden == 0, 'source_html_unbalanced')
    text = ' '.join(' '.join(parser.parts).split())
    if role == 'model':
        require(text.count('Text tokens') == 1, 'model_pricing_section')
        tail = text.split('Text tokens', 1)[1]
        require('Modalities' in tail, 'model_pricing_section')
        pricing = 'Text tokens'+tail.split('Modalities', 1)[0].rstrip()
        matches = re.findall(r'Input \$(\d+\.\d+) Cached input \$(\d+\.\d+) Output \$(\d+\.\d+)', pricing.split('Quick comparison', 1)[0])
        require(len(matches) == 1, 'model_pricing_table')
        require(text.count('Snapshots Snapshots let you') == 1, 'model_snapshot_section')
        snapshots = text.split('Snapshots Snapshots let you', 1)[1].split('Rate limits', 1)[0].strip()
        ids = sorted(set(re.findall(r'\bgpt-[a-z0-9]+(?:[.-][a-z0-9]+)*\b', snapshots)))
        require(MODEL in ids, 'dated_model_not_listed')
        return {'role': role, 'pricing_section': pricing, 'snapshot_section': snapshots,
                'listed_ids': ids, 'input': matches[0][0], 'cached_input': matches[0][1], 'output': matches[0][2],
                'price_conditions':price_conditions(pricing)}
    require(role == 'caching', 'unknown_source_role')
    # Keep the entire comparison, not just the favorable cell.
    start = 'Behavior GPT-5.6 and later GPT-5.5 and GPT-5.5 Pro Other earlier models'
    require(text.count(start) == 1, 'caching_comparison_section')
    tail = text.split(start, 1)[1]
    require('How to optimize prompt caching' in tail, 'caching_comparison_section')
    comparison = start+tail.split('How to optimize prompt caching', 1)[0].rstrip()
    expected = 'Cache write charge 1.25× the uncached input-token rate No additional cache-write charge No additional cache-write charge'
    require(expected in comparison and 'gpt-5.4' in comparison, 'earlier_model_cache_write_rule')
    return {'role': role, 'comparison_section': comparison, 'model_class': 'Other earlier models',
            'additional_cache_write_charge': '0', 'total_write_rate_rule': 'ordinary input rate'}


def source_evidence(directory):
    directory = Path(directory)
    require(directory.is_dir() and not directory.is_symlink(), 'pricing_sources_missing')
    names = {role+suffix for role in URLS for suffix in ('.html', '.extract.json', '.receipt.json')}
    require({p.name for p in directory.iterdir()} == names, 'pricing_source_population')
    result = {}
    for role, url in URLS.items():
        paths = [directory/(role+suffix) for suffix in ('.html', '.extract.json', '.receipt.json')]
        require(all(p.is_file() and not p.is_symlink() for p in paths), 'pricing_source_type')
        require(all(p.stat().st_size <= 4*1024**2 for p in paths), 'pricing_source_size')
        raw, derived_raw, receipt_raw = [p.read_bytes() for p in paths]
        receipt = strict(receipt_raw)
        require(receipt['requested_url'] == receipt['transfer']['url_effective'] == url
            and receipt['transfer']['http_code'] == 200 and receipt['transfer']['ssl_verify_result'] == 0
            and receipt['transfer']['redirects'] == 0 and receipt['transfer']['content_type'] in ('text/html','text/html; charset=utf-8'), 'pricing_source_retrieval')
        require(receipt['raw_sha256'] == sha(raw) and receipt['raw_bytes'] == len(raw)
            and receipt['transfer']['download_bytes'] == len(raw), 'pricing_raw_binding')
        derived = extract(raw, role)
        require(strict(derived_raw) == derived and receipt['extract_sha256'] == sha(derived_raw), 'pricing_extract_binding')
        require(receipt['extractor_sha256'] == sha(Path(__file__).read_bytes()), 'pricing_extractor_binding')
        finish = datetime.fromisoformat(receipt['finished_at_utc'])
        start = datetime.fromisoformat(receipt['started_at_utc'])
        require(start.utcoffset() is not None and finish.utcoffset() is not None and start <= finish,
                'pricing_capture_time')
        result[role] = {'raw_sha256': sha(raw), 'extract_sha256': sha(canonical(derived)),
                        'receipt_sha256': sha(receipt_raw), 'finished_unix': finish.timestamp(), 'extract': derived}
    return result


def rates_from(evidence):
    model = evidence['model']['extract']
    require(evidence['caching']['extract']['additional_cache_write_charge'] == '0', 'pricing_write_rate_unknown')
    # Nano-USD/token avoids floats for a 2.50 USD/million-token input rate.
    rates = {k: Decimal(model[k])*1000 for k in ('input', 'cached_input', 'output')}
    require(all(x >= 0 and x == x.to_integral_value() for x in rates.values()), 'pricing_rate_precision')
    rates = {k: int(v) for k, v in rates.items()}
    rates['cache_write'] = rates['input']
    return rates


def cost_micro(input_tokens, output_tokens, rates):
    require(type(input_tokens) is int and input_tokens >= 0 and type(output_tokens) is int and output_tokens >= 0,
            'pricing_token_count')
    nanos = input_tokens*max(rates[k] for k in ('input', 'cached_input', 'cache_write')) + output_tokens*rates['output']
    return (nanos+999)//1000


def admission(policy, source_dir, arguments, request, now):
    evidence = source_evidence(source_dir)
    require(type(now) in (int, float) and now > 0, 'pricing_clock')
    approved = policy['pricing_admission']
    for role, value in evidence.items():
        pin = approved['sources'][role]
        # Report semantic drift before a raw-only change; neither permits send.
        require(value['extract_sha256'] == pin['extract_sha256'], 'pricing_semantic_drift_'+role)
        require(value['raw_sha256'] == pin['raw_sha256'], 'pricing_raw_drift_'+role)
        age = now-value['finished_unix']
        require(age >= -approved['future_clock_tolerance_seconds'], 'pricing_capture_in_future')
        require(age <= approved['maximum_source_age_seconds'], 'pricing_capture_stale')
    rates = rates_from(evidence)
    require(rates == policy['pricing']['nano_usd_per_token'], 'pricing_policy_rates')
    applicability = check_applicability(policy,evidence,arguments)
    require(policy['model']['requested_id'] == MODEL and policy['request']['model'] == MODEL, 'pricing_model')
    opts = {k:v for k,v in arguments.items() if k != 'input'}
    require(opts == policy['request'], 'pricing_request_options')
    messages = arguments['input']
    require(isinstance(messages, list) and len(messages) == 2 and all(isinstance(m, dict)
            and set(m) == {'role','content'} and isinstance(m['content'], str) for m in messages), 'pricing_message_shape')
    require([m['role'] for m in messages] == ['system','user'], 'pricing_message_roles')
    require(sha(messages[0]['content'].encode()) == policy['prompt_sha256'], 'pricing_prompt_binding')
    expected_user = 'Request SHA-256: '+sha(request)+'\nRequest JSON (exact UTF-8 bytes follow):\n'+request.decode()
    require(messages[1]['content'] == expected_user, 'pricing_request_body_binding')
    size = sum(len(m['content'].encode()) for m in messages)
    limits = policy['limits']
    require(size <= limits['message_utf8_bytes'] and len(entity_body(arguments)) <= limits['maximum_request_bytes'], 'pricing_input_budget')
    request_value = strict(request)
    require(request_value['policy_sha256'] == sha(canonical(policy)+b'\n'), 'pricing_inner_policy_binding')
    return {'schema_version':'r6-pricing-admission-2', 'accepted':True,
        'policy_sha256':sha(canonical(policy)+b'\n'), 'request_sha256':sha(request),
        'arguments_sha256':sha(canonical(arguments)), 'body_sha256':sha(entity_body(arguments)),
        'sources':{k:{f:v[f] for f in ('raw_sha256','extract_sha256','receipt_sha256')} for k,v in evidence.items()},
        'nano_usd_per_token':rates, 'reserved_micro_usd':cost_micro(limits['input_tokens_reserved'],limits['output_tokens'],rates),
        'applicability':applicability,
        'message_utf8_bytes':size, 'evaluated_at_unix':now,
        'billing_guarantee':False, 'evidence_scope':'local retained-source, clock and request consistency; no remote pricing or inference attestation'}


def transport_admission(policy, sources, arguments, request, permit, ledger_raw, episode_id, now):
    require(isinstance(permit,dict),'pricing_permit_missing')
    current=admission(policy,sources,arguments,request,now)
    host_time=permit['pricing_admission']['evaluated_at_unix']
    require(0 <= now-host_time <= policy['pricing_admission']['maximum_permit_age_seconds'],'pricing_permit_stale')
    host=admission(policy,sources,arguments,request,host_time)
    require(permit['pricing_admission']==host,'pricing_permit_binding')
    require(ledger_raw.endswith(b'\n'),'pricing_ledger_truncated')
    rows=[strict(line) for line in ledger_raw.splitlines()]
    require(0 < len(rows) <= policy['limits']['campaign_attempts'],'pricing_ledger_population')
    require(rows[-1]==permit,'pricing_ledger_permit_binding')
    spent=0; attempts=0
    for index,row in enumerate(rows):
        require(row['sequence']==index and row['policy_sha256']==current['policy_sha256'],'pricing_ledger_identity')
        previous='0'*64 if index==0 else sha(canonical(rows[index-1]))
        require(row['previous_hash']==previous,'pricing_ledger_chain')
        require(type(row['reservation']['reserved_micro_usd']) is int
            and row['reservation']['reserved_micro_usd']==current['reserved_micro_usd'],'pricing_reservation_amount')
        if index<len(rows)-1:
            spent+=row['reservation']['reserved_micro_usd']
            attempts+=row['episode_id']==episode_id
    limits=policy['limits']
    require(attempts<limits['attempts_per_episode'] and spent+current['reserved_micro_usd']<=limits['total_micro_usd'],'pricing_campaign_budget')
    reservation={'attempt':attempts+1,'reserved_micro_usd':current['reserved_micro_usd'],
        'spent_plus_reserved_micro_usd':spent+current['reserved_micro_usd'],'message_utf8_bytes':current['message_utf8_bytes'],
        'input_tokens_reserved':limits['input_tokens_reserved'],'output_tokens_reserved':limits['output_tokens'],
        'input_token_bound_status':'byte_ceiling_plus_framing_assumption','billing_guarantee':False}
    require(permit['reservation']==reservation,'pricing_reservation_binding')
    require(permit['episode_id']==episode_id and permit['request_sha256']==current['request_sha256']
        and permit['arguments_sha256']==current['arguments_sha256'],'pricing_permit_request_binding')
    return {'accepted':True,'current':current,'permit_sha256':sha(canonical(permit)),
            'ledger_sha256':sha(ledger_raw),'episode_id':episode_id}
