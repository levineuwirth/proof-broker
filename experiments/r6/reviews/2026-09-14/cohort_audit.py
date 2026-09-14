#!/usr/bin/env python3
"""R6-009 checkpoint auditor: identical model input across policy revisions, distinct receipts, continuous campaign accounting.

Non-locked; read-only over retained bytes. Every run binds to its own retained policy revision, the one frozen contract and the
one campaign; requests are regenerated and the envelope recomputed under the contract; the entity bodies of all runs of the same
task must be byte-identical whatever revision they ran under; reservation, grant and commitment identities must be distinct;
and the shared campaign ledger must chain every revision and every slot outcome across them.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import cohort_budget as budget
import cohort_contract as contract
import cohort_ledger as ledger
import credential
import envelope_proof_audit
import events
import payload
import priced_payload_v2 as v2
import pricing_gate_v3 as gate
import pricing_gate_v2 as gate2
import run as r6


class Rejection(AssertionError):
    def __init__(self, case, detail=''):
        super().__init__(case+(': '+detail if detail else '')); self.case = case


class Audit:
    def __init__(self): self.cases = {}
    def require(self, ok, case, detail=''):
        if case in self.cases: raise Rejection(case, 'duplicate case name')
        self.cases[case] = bool(ok)
        if not ok: raise Rejection(case, detail)


def sha(data): return hashlib.sha256(data).hexdigest()
def load(p): return json.loads(Path(p).read_bytes())
def canonical(v): return events.canonical(v)


def run_cases(name, kind):
    names = [f'{name}:versions:policy_revision_contract_campaign_bound', f'{name}:chain:valid', f'{name}:request:regenerated_under_contract',
             f'{name}:envelope:recomputed_from_contract', f'{name}:pricing:host_and_actor_rederived', f'{name}:ledger:permit_and_reconciliation_bound',
             f'{name}:slot:identity_in_receipts_not_in_model_bytes', f'{name}:seal:retained_hashes_and_outcome']
    if kind == 'proof': names += [f'{name}:proof:shared_checker', f'{name}:grant:ordered_before_first_header_byte']
    return names


def audit(root, ledgers, expected):
    """`expected`: run name -> (kind, task, draw, revision index) for the checkpoint population."""
    a = Audit(); result = {'runs': {}}
    names = sorted(expected); present = sorted(p.name for p in root.iterdir() if p.is_dir())
    a.require(present == names, 'population:exactly_expected_runs', str(present))
    contract_value = contract.contract(); contract_digest = contract.contract_sha256()
    task_cache = {}; bodies = {}; identities = {}; campaign_ids = set(); revisions = {}
    for name in names:
        kind, task_id, draw, revision = expected[name]; run = root/name
        sp = load(run/'search-policy.json'); ph = run/'provenance/cohort-harness'
        policy_path = next(ph.glob('policies/farkas-cohort-v*.json')); policy = load(policy_path); lock = load(next(ph.glob('policies/cohort-harness-v*.sha256.json')))
        retained_contract = load(ph/'contracts/farkas-proposal-contract-v1.json')
        a.require(sp['config_sha256'] == sha(policy_path.read_bytes()) and policy['revision'] == revision and sp['revision'] == revision
                  and sp['contract_sha256'] == contract_digest == policy['contract_sha256'] == sha(canonical(retained_contract)+b'\n')
                  and retained_contract == contract_value and sp['campaign_id'] == policy['campaign']['id'] and sp['task_id'] == task_id and sp['draw'] == draw
                  and policy['source_lock_sha256'] == sha(next(ph.glob('policies/cohort-harness-v*.sha256.json')).read_bytes())
                  and all(sha((ph/f).read_bytes()) == h for f, h in lock.items()) and policy['live_enabled'] is False
                  and (kind == 'refused' or ((run/'transport-policy.json').read_bytes() == policy_path.read_bytes()
                                             and (run/'transport-contract.json').read_bytes() == contract.CONTRACT.read_bytes()))
                  and gate.check_policy(policy, contract_value) is None,
                  f'{name}:versions:policy_revision_contract_campaign_bound')
        campaign_ids.add(sp['campaign_id']); revisions[revision] = sp['config_sha256']
        try: rows = events.read(run/'events.ndjson')
        except ValueError as error: a.require(False, f'{name}:chain:valid', str(error))
        a.require(all(r['task_id'] == task_id for r in rows), f'{name}:chain:valid')
        task = task_cache.setdefault(task_id, r6.get_task(task_id))
        value = payload.strict_json(v2.request(task, load(run/'prepared.json'))); value.pop('policy_sha256')
        value['schema_version'] = gate.REQUEST_SCHEMA; value['contract_sha256'] = contract_digest
        request_bytes = (run/'live-request.json').read_bytes()
        a.require(canonical(value)+b'\n' == request_bytes and 'policy_sha256' not in json.loads(request_bytes)
                  and (kind == 'refused' or (run/'transport-request.json').read_bytes() == request_bytes), f'{name}:request:regenerated_under_contract')
        instruction = (run/'transport-instruction.txt').read_text() if (run/'transport-instruction.txt').exists() else contract.PROMPT.read_text()
        expected_args = gate.render_arguments(contract_value, instruction, request_bytes)
        a.require(load(run/'live-arguments.json') == expected_args and (kind == 'refused' or load(run/'transport-arguments.json') == expected_args)
                  and sha(instruction.encode()) == contract_value['instruction']['sha256']
                  and gate.check_envelope(contract_value, instruction, expected_args, request_bytes)['body_sha256'] == sha(gate2.entity_body(expected_args)),
                  f'{name}:envelope:recomputed_from_contract')
        bodies.setdefault(task_id, {})[name] = gate2.entity_body(expected_args)
        admission = load(run/'host-pricing-admission.json')
        derived = None if kind == 'refused' else gate.admission(policy, contract_value, instruction, run/'pricing-sources', expected_args, request_bytes, admission['evaluated_at_unix'])
        out = run/'stages/proposal-1/output'; check = load(out/'pricing-check.json') if (out/'pricing-check.json').exists() else None
        actor_ok = (kind == 'refused') or (check is not None and check['accepted'] is True and {k: v for k, v in check.items() if k != 'admitted_at_ns'}
                                            == gate.admission(policy, contract_value, instruction, run/'transport-pricing-sources', expected_args, request_bytes, check['evaluated_at_unix']))
        a.require(admission == derived and actor_ok if kind != 'refused' else admission['accepted'] is False, f'{name}:pricing:host_and_actor_rederived')
        if kind == 'refused':
            a.require(admission['failure_code'] == 'cohort_slot_consumed' and not (run/'campaign-permit.json').exists(), f'{name}:ledger:permit_and_reconciliation_bound')
            a.require(not (out/'http.json').exists(), f'{name}:slot:identity_in_receipts_not_in_model_bytes')
        else:
            permit = load(run/'campaign-permit.json'); rec = load(run/'campaign-reconciliation.json')
            before = ledger.parse((run/'transport-ledger.ndjson').read_bytes()); after = ledger.parse((run/'ledger-after.ndjson').read_bytes())
            a.require(before[-1] == permit and after[-1] == rec and after[:len(before)] == before and permit['task_id'] == task_id and permit['draw'] == draw
                      and permit['policy_sha256'] == sp['config_sha256'] and permit['contract_sha256'] == contract_digest and rec['reservation_id'] == permit['reservation_id']
                      and rec['task_id'] == task_id and rec['draw'] == draw and rec['kind'] == {'proof': 'send_grant', 'release': 'release'}[kind]
                      and permit['request_sha256'] == sha(request_bytes) and ledger.state(after, sp['campaign_id'])['open_reservations'] == [],
                      f'{name}:ledger:permit_and_reconciliation_bound')
            http = load(out/'http.json'); text = gate2.entity_body(expected_args).decode()
            identities[name] = {'reservation_id': permit['reservation_id'], 'grant_id': http.get('grant_id'), 'commitment': http['credential_commitment_sha256'], 'nonce': http['commitment_nonce']}
            a.require(http['slot'] == f'{task_id}/{draw}' and http['task_id'] == task_id and http['draw'] == draw and http['reservation_id'] == permit['reservation_id']
                      and not any(needle in text for needle in (permit['reservation_id'], sp['campaign_id'], sp['config_sha256'], 'draw', 'slot')),
                      f'{name}:slot:identity_in_receipts_not_in_model_bytes')
        seal = load(run/'seal.json')
        mismatched = [k for k, v in seal['retained_sha256'].items() if sha((run/k).read_bytes()) != v]
        a.require(not mismatched and seal['event_count'] == len(rows) and seal['last_event_hash'] == rows[-1]['event_hash']
                  and seal['accepted'] is (kind == 'proof') and rows[-1]['event'] == ('episode_finished' if kind == 'proof' else 'episode_rejected'),
                  f'{name}:seal:retained_hashes_and_outcome')
        if kind == 'proof':
            verdict = load(run/'verdict.json'); evidence = load(run/'evidence.json')
            def receipt(stage, event):
                hits = [r['payload'] for r in rows if r['source'] == 'supervisor' and r['stage'] == stage and r['event'] == event]
                if len(hits) != 1: raise ValueError(f'{stage}/{event}: {len(hits)}')
                return hits[0]
            try:
                if verdict['task_id'] != task.id or evidence['certificate']['payload']['witness_data'] != load(run/'validated-response.json')['witness']: raise ValueError('identity')
                envelope_proof_audit.audit(task, evidence, verdict, rows, lambda n: run/n, lambda n: load(run/n), receipt)
            except (ValueError, AssertionError, KeyError, OSError) as error: a.require(False, f'{name}:proof:shared_checker', str(error))
            a.require(True, f'{name}:proof:shared_checker')
            g = ledger.read_grant(ledgers/sp['campaign_id']/'rehearsal'/'slots'/task_id/str(draw)/permit['reservation_id'], permit)
            a.require(g is not None and http['tls_verified_at_ns'] < http['grant_created_at_ns'] < http['grant_durable_at_ns'] < http['header_send_at_ns'] and http['grant_id'] == g['grant_id'],
                      f'{name}:grant:ordered_before_first_header_byte')
        result['runs'][name] = {'kind': kind, 'task': task_id, 'draw': draw, 'revision': revision, 'policy_sha256': sp['config_sha256']}
    # cross-run relationships
    a.require(len(campaign_ids) == 1, 'campaign:single_identity', str(campaign_ids))
    for task_id, group in bodies.items():
        distinct = {sha(b) for b in group.values()}
        a.require(len(distinct) == 1, f'input:identical_model_bytes:{task_id}', f'{len(distinct)} distinct entity bodies across {sorted(group)}')
    revs = sorted(set(r for (_, _, _, r) in expected.values()))
    a.require(len(revs) >= 2 and len(set(revisions.values())) == len(revs), 'revisions:at_least_two_distinct_policies', str(revisions))
    ids = [v['reservation_id'] for v in identities.values()]; grants = [v['grant_id'] for v in identities.values() if v['grant_id']]; nonces = [v['nonce'] for v in identities.values()]
    a.require(len(set(ids)) == len(ids) and len(set(grants)) == len(grants) and len(set(nonces)) == len(nonces), 'receipts:distinct_across_runs')
    book = ledger.Ledger(ledgers/next(iter(campaign_ids))/'rehearsal', next(iter(campaign_ids)))
    raw, s = book.snapshot(); rows_l = ledger.parse(raw); hashes = {r['row_hash'] for r in rows_l}
    permits = [load(root/n/'campaign-permit.json') for n, (k, *_) in expected.items() if k != 'refused']
    recs = [load(root/n/'campaign-reconciliation.json') for n, (k, *_) in expected.items() if k != 'refused']
    a.require(all(p['row_hash'] in hashes for p in permits) and all(r['row_hash'] in hashes for r in recs) and s['open_reservations'] == []
              and [r['policy_sha256'] for r in rows_l if r['kind'] in ('activation', 'authorization_revision')] == [revisions[i] for i in sorted(revisions)]
              and s['contract_sha256'] == contract_digest, 'ledger:continuous_across_revisions', str([r['kind'] for r in rows_l]))
    consumed = {n for n, (k, *_) in expected.items() if k == 'proof'}
    slots = {f"{t}/{d}" for n, (k, t, d, _) in expected.items() if k == 'proof'}
    a.require(all(s['slots'][k]['consumed'] for k in slots) and s['transmissions_consumed'] == len(slots), 'ledger:consumed_slots_persist', str(s['slots']))
    result.update(accepted=all(a.cases.values()), cases=a.cases, case_count=len(a.cases), campaign_id=next(iter(campaign_ids)), contract_sha256=contract_digest,
                  revisions=revisions, entity_body_sha256={t: sha(next(iter(g.values()))) for t, g in bodies.items()}, identities=identities,
                  ledger_state={k: s[k] for k in ('revision', 'revisions', 'transmissions_consumed', 'slots', 'committed_micro_usd')},
                  program_sha256=sha(Path(__file__).read_bytes()), live_model_calls=0, credentials_read=0)
    return result


EXPECTED = {'r1-d1-draw1': ('proof', 'verinf-d1-70', 1, 1), 'r1-d1-draw2-format': ('release', 'verinf-d1-70', 2, 1),
            'r2-d1-draw1-refused': ('refused', 'verinf-d1-70', 1, 2), 'r2-d1-draw2': ('proof', 'verinf-d1-70', 2, 2), 'r2-d1-draw3': ('proof', 'verinf-d1-70', 3, 2)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runs', type=Path, default=ROOT/'cohort-runs')
    parser.add_argument('--ledgers', type=Path, default=ROOT/'ledgers/campaigns')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output and args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    try: result = audit(args.runs.resolve(), args.ledgers.resolve(), EXPECTED)
    except Rejection as rejection:
        print(json.dumps({'accepted': False, 'rejected_case': rejection.case, 'detail': str(rejection)}, indent=1)); sys.exit(1)
    if args.output: r6.write_json(args.output, result)
    print(json.dumps({k: result[k] for k in ('accepted', 'case_count', 'revisions', 'entity_body_sha256', 'ledger_state')}, indent=1))
    sys.exit(0 if result['accepted'] else 1)


if __name__ == '__main__':
    main()
