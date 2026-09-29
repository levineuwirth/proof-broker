#!/usr/bin/env python3
"""Offline provenance and comparison of the two R6-005 documentation captures.

This is a review utility, not a live admission gate or a general pricing parser.
The raw HTTPS entity is retained; the extractor accepts the inspected page
layout and fails on missing or ambiguous sections. It makes no network calls.
"""
import argparse
from decimal import Decimal
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re

MODELS = ('gpt-5.6-sol', 'gpt-5.4')
BASE = 'https://developers.openai.com/api/docs/models/'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(',', ':')).encode()


def write(path, value):
    with path.open('x') as f:
        json.dump(value, f, indent=2, sort_keys=True, ensure_ascii=False)
        f.write('\n')


class VisibleText(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.parts = []
        self.hidden = 0

    def handle_starttag(self, tag, attrs):
        if tag in ('script', 'style'):
            self.hidden += 1

    def handle_endtag(self, tag):
        if tag in ('script', 'style'):
            self.hidden -= 1

    def handle_data(self, value):
        if not self.hidden:
            self.parts.append(value)


def extract(raw, model):
    require(model in MODELS, 'unsupported model source')
    parser = VisibleText()
    parser.feed(raw.decode('utf-8'))
    parser.close()
    require(parser.hidden == 0, 'unbalanced hidden page content')
    text = ' '.join(' '.join(parser.parts).split())

    def section(start, end):
        require(text.count(start) == 1, 'missing or ambiguous '+start+' section')
        tail = text.split(start, 1)[1]
        require(end in tail, 'missing '+end+' boundary')
        return start + tail.split(end, 1)[0].rstrip()

    pricing = section('Text tokens', 'Modalities')
    # Anchor the selected table before comparison cards and pricing conditions.
    table = pricing.split('Quick comparison', 1)[0]
    matches = re.findall(r'Input \$(\d+\.\d+) Cached input \$(\d+\.\d+) Output \$(\d+\.\d+)', table)
    require(len(matches) == 1, 'missing or ambiguous token pricing table')
    rates = dict(zip(('input', 'cached_input', 'output'), matches[0]))
    writes = re.findall(r'Cache writes are billed at (\d+(?:\.\d+)?)x the uncached input token rate\.', pricing)
    require(len(writes) <= 1, 'ambiguous cache-write rate')
    multiplier = writes[0] if writes else None
    rates['cache_write'] = format(Decimal(rates['input'])*Decimal(multiplier), '.2f') if multiplier else None
    snapshots = section('Snapshots Snapshots let you', 'Rate limits')
    ids = sorted(set(re.findall(r'\bgpt-[a-z0-9]+(?:[.-][a-z0-9]+)*\b', snapshots)))
    require(model in ids, 'snapshot section belongs to a different model')
    return {
        'schema_version': 'r6-pricing-extract-1', 'model_page': model,
        'currency': 'USD', 'unit': 'per_million_tokens',
        'per_million_tokens': rates, 'cache_write_multiplier': multiplier,
        'cache_write_scope': 'derived from the stated multiplier' if multiplier else 'not established by this page',
        'pricing_section': pricing, 'snapshot_section': snapshots,
        'listed_ids': ids,
        'listed_dated_ids': [x for x in ids if re.search(r'-\d{4}-\d{2}-\d{2}$', x)],
    }


def verify(bundle, model):
    raw_path = bundle/(model+'.html')
    extract_path = bundle/(model+'.extract.json')
    receipt_path = bundle/(model+'.receipt.json')
    receipt = json.loads(receipt_path.read_bytes())
    require(receipt['schema_version'] == 'r6-pricing-capture-1', 'capture schema differs')
    require(receipt['model_page'] == model and receipt['requested_url'] == BASE+model,
            'capture model/source differs')
    transfer = receipt['transfer']
    require(transfer['http_code'] == 200 and transfer['url_effective'] == BASE+model
            and transfer['redirects'] == 0 and transfer['ssl_verify_result'] == 0
            and transfer['content_type'] == 'text/html', 'capture retrieval declaration differs')
    raw = raw_path.read_bytes()
    derived_bytes = extract_path.read_bytes()
    require(receipt['raw'] == {'file': raw_path.name, 'sha256': sha(raw), 'bytes': len(raw)}
            and transfer['download_bytes'] == len(raw), 'raw source binding differs')
    require(receipt['extractor_sha256'] == sha(Path(__file__).read_bytes()), 'extractor source binding differs')
    actual = extract(raw, model)
    require(json.loads(derived_bytes) == actual, 'pricing extraction differs from retained page')
    require(receipt['extract'] == {'file': extract_path.name, 'sha256': sha(derived_bytes),
            'bytes': len(derived_bytes), 'canonical_sha256': sha(canonical(actual))},
            'extracted source binding differs')
    return actual, receipt


def policy_check(bundle, policy_path):
    model = 'gpt-5.6-sol'
    data, receipt = verify(bundle, model)
    policy = json.loads(policy_path.read_bytes())
    require(policy['model']['requested_id'] == model and policy['pricing']['source'] == BASE+model,
            'policy model/source differs')
    require(data['per_million_tokens'] == policy['pricing']['per_million_tokens'], 'policy rates differ from source')
    rates = data['per_million_tokens']
    require(rates['cache_write'] is not None, 'worst input rate is not established')
    worst_input = max(Decimal(rates[k]) for k in ('input', 'cached_input', 'cache_write'))
    output = Decimal(rates['output'])
    reserve_rates = policy['pricing']['reservation_micro_usd_per_token']
    require(Decimal(str(reserve_rates['input'])) == worst_input
            and Decimal(str(reserve_rates['output'])) == output, 'reservation rates differ from source')
    limits = policy['limits']
    reserve = worst_input*limits['input_tokens_reserved'] + output*limits['output_tokens']
    require(reserve == reserve.to_integral_value(), 'fractional micro-USD reservation requires a rounding rule')
    return {'policy_sha256': sha(policy_path.read_bytes()), 'source_receipt_sha256': sha((bundle/(model+'.receipt.json')).read_bytes()),
            'source_raw_sha256': receipt['raw']['sha256'], 'source_extract_sha256': receipt['extract']['canonical_sha256'],
            'reservation_micro_usd': int(reserve), 'rates_match': True,
            'billing_guarantee': False, 'live_admission_implemented': False}


def compare(old, new, model):
    a, ar = verify(old, model)
    b, br = verify(new, model)
    changed = [k for k in sorted(a) if a[k] != b[k]]
    return {'model_page': model, 'old_raw_sha256': ar['raw']['sha256'], 'new_raw_sha256': br['raw']['sha256'],
            'raw_changed': ar['raw']['sha256'] != br['raw']['sha256'],
            'extract_changed': a != b, 'changed_fields': changed,
            'rates_changed': a['per_million_tokens'] != b['per_million_tokens'],
            'pricing_text_changed': a['pricing_section'] != b['pricing_section'],
            'snapshot_ids_changed': a['listed_ids'] != b['listed_ids'],
            'automatic_live_authorization': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    audit = sub.add_parser('audit')
    audit.add_argument('--bundle', type=Path, required=True)
    audit.add_argument('--policy', type=Path, required=True)
    diff = sub.add_parser('compare')
    diff.add_argument('--old', type=Path, required=True)
    diff.add_argument('--new', type=Path, required=True)
    diff.add_argument('--model', choices=MODELS, required=True)
    args = parser.parse_args()
    if args.command == 'audit':
        for model in MODELS:
            verify(args.bundle, model)
        result = policy_check(args.bundle, args.policy)
    else:
        result = compare(args.old, args.new, args.model)
    print(json.dumps(result, indent=2, sort_keys=True))
