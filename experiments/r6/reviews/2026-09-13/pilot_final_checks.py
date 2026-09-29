#!/usr/bin/env python3
"""R6-007 independent recount over the six pilot runs.

Re-derives the live-2 witness arithmetic, provider fields, TLS ordering, seal,
event chain, ledger and policy bindings from retained bytes; builds a post-hoc
manifest for the unsealed live-1; recounts the rehearsal outcomes. No native
episode, TLS handshake, Lean build or provider request is executed here.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import pilot_contract as contract
import run as r6

CHECKS = []


def require(ok, message):
    CHECKS.append({'check': message, 'passed': bool(ok)})
    if not ok: raise AssertionError(message)


def digest(data): return hashlib.sha256(data).hexdigest()
def canonical(value): return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode()
def load(path): return json.loads(Path(path).read_bytes())


def chain(path):
    """events.read re-derived: sequence, previous_hash and digest per row."""
    previous, rows = '0'*64, []
    for line in Path(path).read_bytes().splitlines():
        row = json.loads(line); recorded = row.pop('event_hash')
        require(row['sequence'] == len(rows) and row['previous_hash'] == previous and digest(canonical(row)) == recorded,
                f'{path.parent.name}: event {len(rows)} chained and digested')
        row['event_hash'] = recorded; rows.append(row); previous = recorded
    return rows


def farkas(problem, witness):
    rows = {row['name']: row for row in problem['rows']}
    terms, constant = {}, 0
    for entry in witness['coefficients']:
        row, m = rows[entry['hypothesis']], int(entry['coefficient'])
        require(row['relation'] == 'eq' or m >= 0, f"multiplier on le row {entry['hypothesis']} is nonnegative")
        constant += m*int(row['constant'])
        for term in row['terms']:
            terms[term['variable']] = terms.get(term['variable'], 0)+m*int(term['coefficient'])
    residual = {v: c for v, c in terms.items() if c}
    return residual, constant


def live2(run):
    request = load(run/'live-request.json'); response = load(run/'response.json')
    validated = load(run/'validated-response.json')
    require(response == validated, 'live-2: response.json equals validated-response.json')
    require(response['request_sha256'] == r6.sha(run/'live-request.json') == digest(Path(run/'live-request.json').read_bytes()),
            'live-2: model echoed the request digest')
    residual, constant = farkas(request['problem'], response['witness'])
    require(residual == {} and constant > 0, f'live-2: witness cancels every variable and leaves {constant} > 0')
    support = sorted(e['hypothesis'] for e in response['witness']['coefficients'])
    require(support == ['hwidth', 'neg_goal'], 'live-2: witness support is exactly {hwidth, neg_goal}')
    require('hZ' not in support, 'live-2: witness does not use hZ, the row every earlier fixture and D-search witness used')
    cert = load(run/'certificate-verdict.json')
    require(cert['accepted'] is True and cert['reason']['kind'] == 'verified_farkas', 'live-2: SDK certificate verdict is verified_farkas')
    raw = load(run/'stages/proposal-1/output/provider-response.json')
    require(raw['model'] == contract.MODEL == 'gpt-5.4-2026-03-05' and raw['status'] == 'completed', 'live-2: provider reports the pinned dated model, completed')
    usage = raw['usage']
    require((usage['input_tokens'], usage['output_tokens'], usage['total_tokens']) == (1523, 573, 2096), 'live-2: usage 1523/573/2096')
    require(usage['input_tokens_details']['cached_tokens'] == 0 and usage['input_tokens_details']['cache_write_tokens'] == 0,
            'live-2: no cached or cache-write tokens')
    text = [c['text'] for item in raw['output'] if item.get('type') == 'message' for c in item['content'] if c.get('type') == 'output_text']
    require(len(text) == 1 and json.loads(text[0]) == response, 'live-2: the single assistant text is exactly the retained witness JSON')
    meta = load(run/'provider-metadata.json')
    require(meta['response_id'] == raw['id'] and meta['reported_model'] == raw['model'], 'live-2: provider-metadata binds response id and model')
    policy = load(contract.CONFIG); rates = policy['pricing']['nano_usd_per_token']
    ceiling = -(-(usage['input_tokens']*rates['input']+usage['output_tokens']*rates['output'])//1000)
    acct = load(run/'accounting.json')
    require(acct['priced_usage_ceiling_micro_usd'] == ceiling == 12403, 'live-2: priced ceiling recomputed as 12,403 µUSD')
    require(acct['live_model_calls'] == 1 and acct['connection_attempts'] == acct['bodies_returned'] == 1, 'live-2: one connection, one body returned, one live call')
    http = load(run/'stages/proposal-1/output/http.json')
    require(http['tls']['verified'] and http['tls']['version'] == 'TLSv1.3' and http['tls']['server_hostname'] == 'api.openai.com',
            'live-2: TLS 1.3 verified against api.openai.com')
    require(http['tls_verified_at_ns'] < http['header_send_at_ns'], 'live-2: certificate verification precedes header send')
    require(http['ca_bundle_sha256'] == policy['tls']['public_ca_bundle']['sha256'], 'live-2: actor used the pinned public CA bundle')
    require(http['http_status'] == 200 and http['redirects_followed'] == 0 and http['retries'] == 0, 'live-2: HTTP 200, no redirects, no retries')
    require(http['request_sha256'] == r6.sha(run/'stages/proposal-1/output/serialized-body.json'), 'live-2: outbound body digest matches the serialized body')
    receipt = load(run/'credential-receipt.json')
    require(receipt['exact_receipt'] is True and receipt['http_status'] == 200, 'live-2: credential receipt is the non-401 provider status')
    ledger = Path(run/'reservation-ledger.ndjson').read_bytes().splitlines()
    require(len(ledger) == 1, 'live-2: exactly one ledger row')
    reservation = load(run/'reservation.json')
    require(reservation['policy_sha256'] == r6.sha(contract.CONFIG) == policy_digest(), 'live-2: reservation bound to the signed policy digest')
    require(reservation['request_sha256'] == response['request_sha256'], 'live-2: reservation bound to the request the model answered')
    verdict = load(run/'verdict.json')
    require(verdict['local_obligation_closed'] is True, 'live-2: local obligation closed')
    require(all(d == {'added': [], 'removed': []} for d in verdict['axiom_delta'].values()) and len(verdict['axiom_delta']) == 2,
            'live-2: axiom deltas empty for both targets')
    rows = chain(run/'events.ndjson')
    kernel = [r for r in rows if r['event'] == 'kernel_verdict']
    require([k['payload']['checked_declarations'] for k in kernel] == [3700, 3719] and all(k['payload']['accepted'] for k in kernel),
            'live-2: kernel replays 3700 and 3719 declarations, both accepted')
    proof = [r for r in rows if r['event'] == 'proof_validated'][-1]['payload']
    require(proof['proof_accepted'] and proof['solution_sha256'] == '862f16b9d9efc5de246fc8aa8aa2278bfff5590fbc70dd6b8d42ab993ab25c27',
            'live-2: proof export 862f16b9…')
    require(not proof['solution_sha256'].startswith('cd6081daac2fc64d'), 'live-2: proof export differs from the deterministic cd6081da… export')
    seal = load(run/'seal.json')
    require(seal['accepted'] and seal['event_count'] == len(rows) == 52 and seal['last_event_hash'] == rows[-1]['event_hash'],
            'live-2: seal binds the 52-event chain')
    retained = seal['retained_sha256']
    mismatched = [k for k, v in retained.items() if r6.sha(run/k) != v]
    require(len(retained) == 263 and not mismatched, 'live-2: all 263 sealed retained files match on disk')
    final = load(run/'publication-final.json')
    require(final['report_findings'] == 0 and final['report_sha256'] == r6.sha(run/'publication-scan.json'), 'live-2: synthetic-canary scan report bound and clean')
    return {'witness': response['witness'], 'residual_terms': residual, 'positive_constant': str(constant),
            'proof_export_sha256': proof['solution_sha256'], 'certificate_hash': cert['certificate_hash'],
            'response_id': raw['id'], 'x_request_id': http['response_headers'].get('x-request-id'),
            'usage': usage, 'priced_ceiling_micro_usd': ceiling, 'seal_sha256': r6.sha(run/'seal.json'),
            'tls_order_margin_ns': http['header_send_at_ns']-http['tls_verified_at_ns'],
            'synthetic_scan_scope': 'live mode never mounts the synthetic canary; this scan is vacuous for the real credential'}


def policy_digest():
    return digest(Path(contract.CONFIG).read_bytes())


def live1(run):
    """Unsealed by a harness defect; manifest built here, evidence recounted."""
    rows = chain(run/'events.ndjson')
    require(rows[-1]['event'] == 'stage_finished' and not any(r['event'] in ('episode_finished', 'episode_rejected') for r in rows),
            'live-1: event chain ends at stage_finished with no terminal event')
    http = load(run/'stages/proposal-1/output/http.json')
    require(http['connection_attempts'] == 0 and http['header_sends_started'] == 0 and http['failure_category'] is None,
            'live-1: zero connections and an unclassified http record')
    stderr = Path(run/'stages/proposal-1/proposal-1.stderr').read_text()
    require(stderr.rstrip().endswith('ValueError: credential_format') and 'Bearer' not in stderr, 'live-1: stderr names credential_format and carries no header text')
    process = load(run/'stages/proposal-1/proposal-1.process.json')
    require(process['exit_code'] == 1, 'live-1: actor exited 1')
    require(len(Path(run/'reservation-ledger.ndjson').read_bytes().splitlines()) == 1, 'live-1: one reservation row consumed')
    files = sorted(p for p in run.rglob('*') if p.is_file())
    manifest = {str(p.relative_to(run)): r6.sha(p) for p in files}
    return {'post_hoc_manifest_files': len(manifest), 'post_hoc_manifest_sha256': digest(canonical(manifest)),
            'events': len(rows), 'last_event_hash': rows[-1]['event_hash'],
            'scope': 'not sealed by the harness; StageFailure propagated before finalize'}


def rehearsals(root):
    expected = {'rehearsal-1': ('host', 'pricing_capture_stale'), 'rehearsal-2': ('actor', 'pricing_reservation_binding'),
                'rehearsal-3': ('actor', 'tls_protocol_failure'), 'rehearsal-4': ('pass', None)}
    out = {}
    for name, (where, code) in expected.items():
        run = root/name; rows = chain(run/'events.ndjson'); seal = load(run/'seal.json')
        require(seal['event_count'] == len(rows) and seal['last_event_hash'] == rows[-1]['event_hash'], f'{name}: sealed over its event chain')
        require(seal['accepted'] is (where == 'pass') and rows[-1]['event'] == ('episode_finished' if where == 'pass' else 'episode_rejected'),
                f'{name}: seal records the episode outcome and the chain ends with a terminal event')
        acct = load(run/'accounting.json')
        require(acct['live_model_calls'] == 0, f'{name}: zero live calls')
        if where == 'host':
            require(load(run/'host-pricing-admission.json')['failure_code'] == code, f'{name}: host admission rejected with {code}')
        elif where == 'actor':
            require(load(run/'stages/proposal-1/output/http.json')['failure_category'] in (code, 'pricing_admission'), f'{name}: actor failed with {code}')
            if code != 'tls_protocol_failure':
                require(load(run/'stages/proposal-1/output/pricing-check.json')['failure_code'] == code, f'{name}: actor pricing check names {code}')
        else:
            proof = [r for r in rows if r['event'] == 'proof_validated'][-1]['payload']
            require(proof['proof_accepted'] and proof['solution_sha256'].startswith('cd6081daac2fc64d'), f'{name}: canned witness reproduces the deterministic export cd6081da…')
        out[name] = {'events': len(rows), 'seal_sha256': r6.sha(run/'seal.json'), 'outcome': code or 'proof_accepted'}
    return out


def locks():
    lock = load(contract.LOCK)
    require(sorted(lock) == sorted(contract.FILES), 'pilot-harness-v1 lock names exactly the six pilot files')
    drift = [f for f in contract.FILES if r6.sha(ROOT/f) != lock[f]]
    require(not drift, 'pilot-harness-v1 lock matches the working tree')
    policy = load(contract.CONFIG)
    require(Path(contract.CONFIG).read_bytes() == canonical(policy)+b'\n', 'pilot policy is stored in canonical form')
    require(policy['authorization']['approved_by'] == 'Levi Neuwirth' and policy['authorization']['maximum_attempts'] == 1
            and policy['limits']['campaign_attempts'] == 1 and policy['live_enabled'] is True, 'policy: author-signed, one attempt, live enabled')
    require(policy['runtime_divergence']['libraries_changed'] == ['/usr/lib/liblzma.so.5'] and policy['runtime_divergence']['python_unchanged'],
            'policy records the liblzma divergence from provider-runtime-v1')
    sp = load(ROOT/'pilot-runs/live-2/search-policy.json')
    require(sp['config_sha256'] == policy_digest() and sp['source_lock_sha256'] == r6.sha(contract.LOCK), 'live-2 search policy binds this policy and lock')
    return {'policy_sha256': policy_digest(), 'lock_sha256': r6.sha(contract.LOCK)}


def operator_scan():
    summary = load(Path(__file__).with_name('operator-disclosure-scan.summary.json'))
    require(summary['accepted'] and summary['disclosures'] == [] and summary['files_scanned'] == 43108, 'operator scan: 43,108 files, zero disclosures')
    require(summary['files_by_top_level']['pilot-runs'] == 1329, 'operator scan covered all 1,329 pilot-run files')
    full = Path(__file__).with_name('operator-disclosure-scan.json')
    if full.exists():
        require(r6.sha(full) == summary['full_report_sha256'], 'operator scan: local full report matches the committed summary digest')
    return {k: summary[k] for k in ('files_scanned', 'gzip_streams_scanned', 'full_report_sha256', 'inventory_sha256')}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runs', type=Path, default=ROOT/'pilot-runs')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('R6-007-CHECKS.json'))
    args = parser.parse_args()
    result = {'locks': locks(), 'live-2': live2(args.runs/'live-2'), 'live-1': live1(args.runs/'live-1'),
              'rehearsals': rehearsals(args.runs), 'operator_scan': operator_scan()}
    result.update(passed=all(c['passed'] for c in CHECKS), total_checks=len(CHECKS), checks=CHECKS,
                  live_model_calls=0, live_model_cost_usd=0, program_sha256=r6.sha(Path(__file__)),
                  scope='independent recount over retained bytes; no new native execution or inference')
    r6.write_json(args.output, result)
    print(json.dumps({k: result[k] for k in ('passed', 'total_checks')}, indent=1))
    print(json.dumps({k: result['live-2'][k] for k in ('witness', 'residual_terms', 'positive_constant', 'priced_ceiling_micro_usd', 'tls_order_margin_ns')}, indent=1))
    print(json.dumps({'live-1': result['live-1'], 'rehearsals': {k: v['outcome'] for k, v in result['rehearsals'].items()}}, indent=1))


if __name__ == '__main__':
    main()
