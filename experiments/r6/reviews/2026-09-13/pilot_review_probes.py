#!/usr/bin/env python3
"""Independent R6-007 review probes. Never connects or reads an operator key.

Mutations affect temporary copies only. A reproduced gap is an observation,
not an approval of the checkpoint. The original recount is called in the same
order as its public CLI; its --runs-independent lock/scan roots are preserved.
"""
import argparse
from collections import Counter
import copy
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import credential
import credential_episode as finalizer
import envelope_proof_audit
import events
import pilot_budget as budget
import pilot_contract as contract
import pilot_https as actor
import pricing_gate_v2 as gate
import run as r6

spec = importlib.util.spec_from_file_location('reviewed_pilot_recount',
    Path(__file__).with_name('pilot_final_checks.py'))
recount = importlib.util.module_from_spec(spec)
spec.loader.exec_module(recount)
RUNS = ROOT/'pilot-runs'
NAMES = ('live-1', 'live-2', 'rehearsal-1', 'rehearsal-2', 'rehearsal-3', 'rehearsal-4')
MUTATIONS = ('wrong_target', 'wrong_type', 'forbidden_axiom', 'invalid_proof_export',
             'wrong_reconstruction_context', 'substituted_certificate_witness',
             'false_host_admission', 'broken_reservation_ledger', 'altered_outbound_body',
             'rehearsal_file_drift', 'unsealed_file_drift', 'extra_live_episode')


def sha(raw): return hashlib.sha256(raw).hexdigest()
def load(p): return json.loads(p.read_bytes())
def write(p, value): p.write_bytes(events.canonical(value)+b'\n')


def public_recount(root):
    recount.CHECKS.clear()
    try:
        recount.locks()
        recount.live2(root/'live-2')
        recount.live1(root/'live-1')
        recount.rehearsals(root)
        recount.operator_scan()
    except Exception as error:
        return {'accepted': False, 'error': str(error), 'checks': len(recount.CHECKS)}
    return {'accepted': True, 'checks': len(recount.CHECKS)}


def shared_proof(run):
    task = r6.get_task('verinf-d1-70')
    rows = events.read(run/'events.ndjson')
    def receipt(stage, event):
        hits = [r['payload'] for r in rows if r['source'] == 'supervisor'
                and r['stage'] == stage and r['event'] == event]
        assert len(hits) == 1
        return hits[0]
    read = lambda name: load(run/name)
    assert read('stages/reconstruct/output/context.json') == read('stages/preparation/output/context.json') \
        == load(task.path/'context/local-context.json'), 'reconstruction context differs'
    assert read('verdict.json')['task_id'] == task.id, 'target identity differs'
    assert read('evidence.json')['certificate']['payload']['witness_data'] \
        == read('validated-response.json')['witness'], 'certificate witness differs from response'
    envelope_proof_audit.audit(task, read('evidence.json'), read('verdict.json'), rows,
                               lambda name: run/name, read, receipt)


def rechain(run, rows):
    previous = '0'*64
    for i, row in enumerate(rows):
        row.update(sequence=i, previous_hash=previous)
        row.pop('event_hash', None)
        row['event_hash'] = events.digest(row)
        previous = row['event_hash']
    (run/'events.ndjson').write_bytes(b''.join(events.canonical(r)+b'\n' for r in rows))


def refinalize(run, change):
    """Normal synthetic scan -> report scan -> terminal -> seal on our copy."""
    rows = events.read(run/'events.ndjson')
    assert rows[-1]['event'] == 'episode_finished'
    rows.pop()
    change(run, rows)
    rechain(run, rows)
    for name in ('publication-scan.json', 'publication-final.json', 'seal.json'):
        (run/name).unlink()
    nonce = load(run/'credential-canary.json')['nonce']
    accepted, scan, final = finalizer.finalize(run, credential.derive(nonce), nonce,
                                               load(run/'credential-summary.json'))
    assert accepted and scan['accepted'] and final['report_clean']
    seal = load(run/'seal.json')
    assert len(seal['retained_sha256']) == 263
    assert all(r6.sha(run/p) == h for p, h in seal['retained_sha256'].items())
    assert len(events.read(run/'events.ndjson')) == 52


def alter(run, rows, name):
    def change_json(file, fn):
        obj = load(run/file); fn(obj); write(run/file, obj)
    if name == 'wrong_target':
        change_json('verdict.json', lambda v: v.update(task_id='c1-c8-coefficient-bound'))
    elif name in ('wrong_type', 'forbidden_axiom'):
        raw_path = run/'validation-local.raw.json.gz'
        obj = json.loads(gzip.decompress(raw_path.read_bytes()))
        target = obj['targets'][0]
        if name == 'wrong_type':
            assert target['type_repr'] != 'False'
            target['type_repr'] = 'False'
        else:
            assert 'sorryAx' not in target['axioms']
            target['axioms'].append('sorryAx')
        raw_path.write_bytes(gzip.compress(events.canonical(obj)+b'\n', mtime=0))
        normalized = copy.deepcopy(obj)
        t = normalized['targets'][0]
        t['type_sha256'] = sha(t.pop('type_repr').encode())
        t['type_hash_format'] = 'Lean-4.32.2-reprStr-Expr-UTF8'
        change_json('verdict.json', lambda v: v['final_validation'].update(local=normalized))
        hits = [r for r in rows if r['stage'] == 'validation-local' and r['event'] == 'kernel_verdict']
        assert len(hits) == 1
        hits[0]['payload'] = normalized
    elif name == 'invalid_proof_export':
        p = run/'solution.ndjson.gz'
        original = gzip.decompress(p.read_bytes())
        assert original and original != b'invalid proof export\n'
        p.write_bytes(gzip.compress(b'invalid proof export\n', mtime=0))
    elif name == 'wrong_reconstruction_context':
        p = run/'stages/reconstruct/output/context.json'
        obj = load(p); assert obj['target'] != 'False'
        obj['target'] = 'False'; write(p, obj)
        hits = [r for r in rows if r['event'] == 'context_validated']
        assert len(hits) == 1
        hits[0]['payload']['captured_context_sha256'] = r6.sha(p)
    elif name == 'substituted_certificate_witness':
        p = run/'evidence.json'; obj = load(p)
        c = obj['certificate']['payload']['witness_data']['coefficients'][0]
        assert c['coefficient'] == '1'
        c['coefficient'] = '999999'
        write(p, obj); write(run/'stages/assembly/output/evidence.json', obj)
    elif name == 'false_host_admission':
        change_json('host-pricing-admission.json', lambda o: o.update(accepted=False))
    elif name == 'broken_reservation_ledger':
        assert len((run/'reservation-ledger.ndjson').read_bytes().splitlines()) == 1
        (run/'reservation-ledger.ndjson').write_bytes(b'{}\n')
    elif name == 'altered_outbound_body':
        p = run/'stages/proposal-1/output/outbound-body.json'
        original = p.read_bytes(); assert original == (p.parent/'serialized-body.json').read_bytes()
        p.write_bytes(original+b' ')
        change_json('stages/proposal-1/output/http.json', lambda h: h.update(outbound_body_sha256=r6.sha(p)))
    else:
        raise AssertionError(name)
    for row in rows:
        if row['event'] == 'proof_validated':
            row['payload']['verdict_sha256'] = r6.sha(run/'verdict.json')


def mutation_probes():
    result = {}
    for name in MUTATIONS:
        with tempfile.TemporaryDirectory(prefix='r6-007-mutation-') as temp:
            root = Path(temp)/'pilot-runs'; shutil.copytree(RUNS, root)
            baseline = public_recount(root)
            assert baseline == {'accepted': True, 'checks': 230}, baseline
            shared_proof(root/'live-2')
            kind = 'scan_report_terminal_and_seal_recomputed'
            if name == 'rehearsal_file_drift':
                p = root/'rehearsal-4/solution.ndjson.gz'
                p.write_bytes(b'not gzip')
                kind = 'original_seal_intentionally_stale_to_test_rehearsal_hash_verification'
            elif name == 'unsealed_file_drift':
                p = root/'live-1/prepared.json'
                v = load(p); v['fragment'] = 'wrong_fragment'; write(p, v)
                kind = 'post_hoc_inventory_is_recomputed_not_compared_to_reviewed_baseline'
            elif name == 'extra_live_episode':
                shutil.copytree(root/'live-2', root/'live-3')
                kind = 'extra_directory_is_not_examined'
            else:
                refinalize(root/'live-2', lambda run, rows: alter(run, rows, name))
            observed = public_recount(root)
            assert observed['accepted'] and observed['checks'] == 230, (name, observed)
            item = {'unmutated_copy': baseline, 'mutation': name, 'recount': observed,
                    'scope': kind, 'gap_reproduced': True}
            if name in MUTATIONS[:6]:
                try: shared_proof(root/'live-2')
                except (ValueError, AssertionError) as error: item['independent_detection'] = str(error)
                else: raise AssertionError('Proof probe did not reach its intended boundary: '+name)
            if name == 'altered_outbound_body':
                _, _, _, validation, error = budget.interpret(root/'live-2/stages/proposal-1/output',
                    (root/'live-2/live-request.json').read_bytes(), True)
                assert error is None and validation['body_consistency']['accepted'] is None
                item['production_interpret_error'] = None
                item['production_body_consistency'] = validation['body_consistency']
            result[name] = item
    assert tuple(result) == MUTATIONS
    return result


def ledger_probe():
    root = RUNS/'live-2'; c = contract.config()
    arguments = load(root/'live-arguments.json'); request = (root/'live-request.json').read_bytes()
    now = load(root/'host-pricing-admission.json')['evaluated_at_unix']
    with tempfile.TemporaryDirectory(prefix='r6-007-ledger-') as temp, patch.object(budget.time, 'time', return_value=now):
        rows = []
        for name in ('new-live-a', 'new-live-b'):
            folder = Path(temp)/name; folder.mkdir()
            row = budget.reserve(folder/'reservation-ledger.ndjson', name, arguments, request, root/'pricing-sources')
            admitted = gate.transport_admission(c, root/'pricing-sources', arguments, request, row,
                (folder/'reservation-ledger.ndjson').read_bytes(), name, now)
            assert admitted['accepted']
            rows.append(row)
        try:
            budget.reserve(Path(temp)/'new-live-b/reservation-ledger.ndjson', 'new-live-b', arguments, request, root/'pricing-sources')
        except gate.Failure as error: rejected = error.code
        else: raise AssertionError('Same-ledger positive rejection control failed')
        assert rejected == 'campaign_request_budget'
    return {'same_policy': r6.sha(contract.CONFIG), 'new_ledgers_admitted_by_host_and_actor': len(rows),
            'combined_reserved_micro_usd': sum(r['reservation']['reserved_micro_usd'] for r in rows),
            'declared_campaign_micro_usd': c['limits']['total_micro_usd'], 'same_ledger_second_attempt_rejected': rejected,
            'clock': 'recorded host admission time; no freshness claim about now', 'connections': 0,
            'gap_reproduced': True}


def authorization_probe():
    c = contract.config()
    results = {}
    for name, key, value in [('zero_monetary_authorization', 'maximum_micro_usd', 0),
                             ('missing_operator_identity', 'approved_by', '')]:
        mutant = copy.deepcopy(c); mutant['authorization'][key] = value
        try: contract.authorization(mutant)
        except ValueError as error: host_error = str(error)
        else: raise AssertionError('Host precondition did not reject')
        actor_record = actor.live_authorization(mutant)
        assert actor_record[key] == value
        results[name] = {'host_rejected': host_error, 'actor_authorization_accepted': True}
    return results


def inventory_review():
    p = Path(__file__).with_name('operator-disclosure-scan.json')
    full = load(p); summary = load(p.with_name('operator-disclosure-scan.summary.json'))
    assert sha(p.read_bytes()) == summary['full_report_sha256']
    items = full['inventory']; assert len(items) == len({e['path_sha256'] for e in items}) == 43108
    changed = []
    for e in items:
        target = ROOT/e['path']
        if not target.is_file() or r6.sha(target) != e['sha256']: changed.append(e['path'])
    assert sum(e['path'].startswith('pilot-runs/') for e in items) == 1329
    return {'recorded_files': len(items), 'recorded_files_changed_now': changed,
            'pilot_files_all_in_scan': True, 'full_report_sha256': r6.sha(p),
            'operator_key_read_by_review': False,
            'scope': 'digest/inventory check of operator report, not a repeat of secret-dependent scanning'}


def original_evidence():
    contract.verify_sources()
    root = RUNS/'live-2'; shared_proof(root)
    task = r6.get_task('verinf-d1-70'); request = (root/'live-request.json').read_bytes()
    assert request == budget.request(task, load(root/'prepared.json'))
    assert load(root/'live-arguments.json') == budget.arguments(request)
    host = load(root/'host-pricing-admission.json')
    assert host == gate.admission(contract.config(), root/'pricing-sources', load(root/'live-arguments.json'), request,
                                   host['evaluated_at_unix'])
    record = load(root/'stages/proposal-1/output/pricing-check.json')
    observed = gate.transport_admission(load(root/'transport-policy.json'), root/'transport-pricing-sources',
        load(root/'transport-arguments.json'), (root/'transport-request.json').read_bytes(),
        load(root/'pricing-permit.json'), (root/'transport-ledger.ndjson').read_bytes(), 'live-2', record['evaluated_at_unix'])
    assert observed == {k:v for k,v in record.items() if k not in ('admitted_at_ns', 'evaluated_at_unix')}
    seals = {}; event_count = 0
    for name in NAMES:
        run = RUNS/name; rows = events.read(run/'events.ndjson'); event_count += len(rows)
        p = run/'seal.json'
        if p.exists():
            seal = load(p)
            assert all(r6.sha(run/n) == h for n,h in seal['retained_sha256'].items())
            assert seal['event_count'] == len(rows) and seal['last_event_hash'] == rows[-1]['event_hash']
            seals[name] = len(seal['retained_sha256'])
    rows = events.read(root/'events.ndjson')
    duplicate_keys = Counter((r['source'],r['stage'],r['event']) for r in rows)
    duplicates = [{'key':list(k), 'count':v} for k,v in duplicate_keys.items() if v>1]
    attribution = {r['event']: r['payload'] for r in rows if r['event'] in
                   ('recovery_started', 'certificate_assembled', 'recovery_finished')}
    ledgers = {name: load(RUNS/name/'reservation.json')['reserved_micro_usd'] for name in ('live-1', 'live-2')}
    return {'shared_proof_checker': True, 'context_equality': True, 'request_projection': True,
            'host_and_actor_pricing_rederived': True, 'all_sealed_files_match': True,
            'seals': seals, 'sealed_entries': sum(seals.values()), 'event_count': event_count,
            'duplicate_receipt_keys': duplicates, 'attribution': attribution,
            'observed_live_reservations_micro_usd': ledgers,
            'source_lock_verified': True, 'scope': 'retained observations checked; no new Lean or verifier execution'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite output')
    evidence = original_evidence()
    baseline = public_recount(RUNS); assert baseline == {'accepted': True, 'checks': 230}
    results = {'baseline': baseline, 'original_evidence': evidence,
               'mutations': mutation_probes(), 'ledger': ledger_probe(),
               'authorization': authorization_probe(), 'operator_scan_inventory': inventory_review()}
    results.update(review_probes_completed=True, checkpoint_approved=False,
                   program_sha256=r6.sha(Path(__file__)), source_lock_sha256=r6.sha(contract.LOCK),
                   policy_sha256=r6.sha(contract.CONFIG), live_model_calls=0, credentials_read=0,
                   scope='offline probes on temporary copies; no live/native episode or inference executed')
    write(args.output, results)
    print(json.dumps({'review_probes_completed':True, 'checkpoint_approved':False,
                      'accepted_mutations':len(results['mutations']), 'output':str(args.output)}, indent=1))


if __name__ == '__main__': main()
