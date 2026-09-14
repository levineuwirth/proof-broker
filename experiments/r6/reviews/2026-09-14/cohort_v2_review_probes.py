#!/usr/bin/env python3
"""Independent review of eb8bf13: copied-artifact joins and failed directory-creation recovery.

No provider, credential, native Lean, real campaign mutation, or signing path.
Accepted mutations are findings, not passing conformance tests.
"""
import argparse
import copy
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
import cohort_contract as contract
import cohort_https as actor
import cohort_ledger as ledger
import events
import run as r6

spec = importlib.util.spec_from_file_location('cohort_v2_review_controls', Path(__file__).with_name('cohort_audit_controls.py'))
helper = importlib.util.module_from_spec(spec); spec.loader.exec_module(helper)
J = lambda p: json.loads(Path(p).read_bytes())
W = lambda p, value: Path(p).write_bytes(events.canonical(value)+b'\n')
LAST = 'r2-c8-draw2'
AUDIT_CASES = ('mounted_adapter_foreign', 'credential_hash_pair_false', 'pricing_admitted_receipt_wrong',
               'request_reserved_receipt_wrong', 'reservation_reconciled_receipt_wrong', 'https_observed_receipt_wrong',
               'transport_validated_receipt_false', 'resource_limit_receipt_wrong', 'nonzero_sender_exit_coherent',
               'zero_reservation_coherent')


def event(rows, name, stage=None):
    matches = [r for r in rows if r['event'] == name and (stage is None or r['stage'] == stage)]
    assert len(matches) == 1, (name, len(matches))
    return matches[0]['payload']


def same_basename(run, rows):
    command = J(run/'stages/proposal-1/command.json'); argv = command['argv']
    matches = [i for i, x in enumerate(argv) if x == '/adapter.py' and i >= 2 and argv[i-2] == '--ro-bind']
    assert len(matches) == 1
    i = matches[0]-1; old = argv[i]
    argv[i] = '/tmp/r6-009-v2-review-unapproved/cohort_https.py'
    assert argv[i] != old and Path(argv[i]).name == Path(old).name
    W(run/'stages/proposal-1/command.json', command)


def coherent_exit(root, book, campaign):
    run = root/LAST; p = run/'stages/proposal-1/proposal-1.process.json'
    process = J(p); assert process['exit_code'] == 0
    process['exit_code'] = 7; W(p, process)
    rec = J(run/'campaign-reconciliation.json')
    rec['evidence']['process_sha256'] = r6.sha(p); rec['evidence']['process_exit_code'] = 7
    rows = ledger.parse((book/'ledger.ndjson').read_bytes())
    assert rows[-1]['reservation_id'] == rec['reservation_id'] and rows[-1]['kind'] == 'send_grant'
    rows[-1] = rec; helper.rewrite_ledger(book, campaign, rows); rec = rows[-1]
    W(run/'campaign-reconciliation.json', rec)
    shutil.copyfile(book/'ledger.ndjson', run/'ledger-after.ndjson')
    def change(run, rows):
        finish = event(rows, 'stage_finished', 'proposal-1'); finish.clear(); finish.update(process)
        event(rows, 'reservation_reconciled').update(row_hash=rec['row_hash'], ledger_sha256=r6.sha(run/'ledger-after.ndjson'))
    helper.refinalize(run, change)
    return {'recorded_exit_code': 7, 'termination_established': rec['termination_established'], 'ledger_kind': rec['kind']}


def coherent_zero(root, book, campaign):
    run = root/LAST; rows = ledger.parse((book/'ledger.ndjson').read_bytes())
    permit, rec = rows[-2], rows[-1]
    assert permit == J(run/'campaign-permit.json') and rec == J(run/'campaign-reconciliation.json')
    assert permit['reserved_micro_usd'] == permit['reservation']['reserved_micro_usd'] == 102400
    def actor_pricing_check():
        return actor.pricing_check(J(run/'transport-policy.json'), J(run/'transport-contract.json'),
                                   (run/'transport-instruction.txt').read_text(), run/'transport-pricing-sources',
                                   J(run/'transport-arguments.json'), (run/'transport-request.json').read_bytes(), permit,
                                   J(run/'stages/proposal-1/output/pricing-check.json')['evaluated_at_unix'])
    assert actor_pricing_check()['accepted'] is True
    # One false reservation amount, consistently carried through every mirror.
    # The independently rederived pricing admission remains 102400.
    permit['reserved_micro_usd'] = 0; permit['reservation']['reserved_micro_usd'] = 0
    try: actor_pricing_check()
    except actor.gate.Failure as caught: actor_rejection = caught.code
    else: raise AssertionError('executing actor price predicate accepted zero reservation')
    assert actor_rejection == 'pricing_reservation_amount'
    helper.rewrite_ledger(book, campaign, rows)
    W(run/'campaign-permit.json', permit); W(run/'campaign-reconciliation.json', rec)
    before = b''.join(events.canonical(r)+b'\n' for r in rows[:-1])
    (run/'transport-ledger.ndjson').write_bytes(before)
    shutil.copyfile(book/'ledger.ndjson', run/'ledger-after.ndjson')
    reservation = J(run/'reservation.json')
    reservation.update(reserved_micro_usd=0, ledger_row_hash=permit['row_hash'], ledger_sha256=r6.sha(run/'transport-ledger.ndjson'))
    W(run/'reservation.json', reservation)
    accounting = J(run/'accounting.json'); accounting['reservation'] = copy.deepcopy(reservation); W(run/'accounting.json', accounting)
    summary = J(run/'credential-summary.json'); summary['accounting'] = copy.deepcopy(accounting); W(run/'credential-summary.json', summary)
    def change(run, rows):
        reserve_event = event(rows, 'request_reserved'); reserve_event.clear(); reserve_event.update(reservation)
        event(rows, 'reservation_reconciled').update(row_hash=rec['row_hash'], ledger_sha256=r6.sha(run/'ledger-after.ndjson'))
    helper.refinalize(run, change)
    state = ledger.state(rows, campaign)
    return {'permit_reserved_micro_usd': permit['reserved_micro_usd'],
            'host_price_reservation_micro_usd': J(run/'host-pricing-admission.json')['reserved_micro_usd'],
            'actor_price_reservation_micro_usd': J(run/'stages/proposal-1/output/pricing-check.json')['reserved_micro_usd'],
            'committed_micro_usd': state['committed_micro_usd'], 'executing_actor_predicate_baseline_accepted': True,
            'executing_actor_predicate_rejects_mutation': actor_rejection,
            'actor_predicate_scope': 'shared executing price predicate only; no actor process or connection'}


def mutate(name, root, ledgers):
    run = root/LAST; campaign = J(run/'search-policy.json')['campaign_id']; book = ledgers/campaign/'rehearsal'
    if name == 'nonzero_sender_exit_coherent': return coherent_exit(root, book, campaign)
    if name == 'zero_reservation_coherent': return coherent_zero(root, book, campaign)
    def change(run, rows):
        if name == 'mounted_adapter_foreign': same_basename(run, rows)
        elif name == 'credential_hash_pair_false':
            receipt = J(run/'credential-receipt.json')
            assert receipt['expected_authorization_sha256'] != '0'*64
            receipt['expected_authorization_sha256'] = receipt['observed_authorization_sha256'] = '0'*64
            W(run/'credential-receipt.json', receipt)
            mirror = event(rows, 'credential_receipt_checked'); mirror.clear(); mirror.update(receipt)
        elif name == 'pricing_admitted_receipt_wrong':
            p = event(rows, 'pricing_admitted'); assert p['admission_sha256'] != '0'*64; p['admission_sha256'] = '0'*64
        elif name == 'request_reserved_receipt_wrong':
            p = event(rows, 'request_reserved'); assert p['reserved_micro_usd'] == 102400; p['reserved_micro_usd'] = 0
        elif name == 'reservation_reconciled_receipt_wrong':
            p = event(rows, 'reservation_reconciled'); assert p['row_hash'] != '0'*64; p['row_hash'] = '0'*64
        elif name == 'https_observed_receipt_wrong':
            p = event(rows, 'https_observed'); assert p['http_sha256'] != '0'*64; p['http_sha256'] = '0'*64
        elif name == 'transport_validated_receipt_false':
            p = event(rows, 'transport_validated'); assert p['outbound_envelope']['accepted'] is True; p['outbound_envelope']['accepted'] = False
        elif name == 'resource_limit_receipt_wrong':
            p = event(rows, 'stage_started', 'proposal-1'); assert p['wall_limit_seconds'] == 60; p['wall_limit_seconds'] = 0
        else: raise AssertionError(name)
    helper.refinalize(run, change)
    return {}


def audit_probes(scratch, save):
    results = {}
    for name in AUDIT_CASES:
        with tempfile.TemporaryDirectory(prefix='audit-copy-', dir=scratch) as temp:
            d = Path(temp); root = d/'runs'; ledgers = d/'ledgers'
            shutil.copytree(ROOT/'cohort-runs-v2', root); shutil.copytree(ROOT/'ledgers/campaigns', ledgers)
            baseline = helper.run_audit(root, ledgers); assert baseline['accepted'] is True, baseline
            detail = mutate(name, root, ledgers)
            observed = helper.run_audit(root, ledgers)
            results[name] = {'unmutated_copy': baseline, 'mutated_copy': observed, 'detail': detail}
            save(results, False); print(name, observed, detail, flush=True)
    assert tuple(results) == AUDIT_CASES
    return results


def fault_case(directory, where):
    book = ledger.Ledger(directory/'ledger', contract.config()['campaign']['id']); policy = contract.config()
    book.activate(policy, False); task = 'verinf-d1-70'; draw = 1
    task_dir, draw_dir = book.slots/task, book.slots/task/'1'
    assert not task_dir.exists() and not draw_dir.exists()
    original = ledger.fsync_directory; attempted = []; completed = []; failed = []
    def sync(path):
        path = Path(path); attempted.append(str(path.relative_to(directory)))
        if ((where == 'task' and path == task_dir) or (where == 'slots' and path == book.slots)) and not failed:
            failed.append(str(path.relative_to(directory))); raise OSError('review injected directory fsync failure')
        original(path); completed.append(str(path.relative_to(directory)))
    def reserve(label):
        return book.reserve(label, policy, task, draw, {'reserved_micro_usd': 102400},
                            {'contract_sha256': policy['contract_sha256'], 'request_sha256': 'a'*64}, {'accepted': True})
    with patch.object(ledger, 'fsync_directory', sync):
        try: reserve('interrupted')
        except OSError: pass
        else: raise AssertionError('fault did not trigger')
    assert len(failed) == 1 and len(ledger.parse(book.path.read_bytes())) == 1
    assert task_dir.exists() and draw_dir.exists()
    first = {'attempted': list(attempted), 'completed': list(completed), 'failed': list(failed)}
    attempted.clear(); completed.clear()
    with patch.object(ledger, 'fsync_directory', sync):
        permit, _ = reserve('retry')
    missing = [str(p.relative_to(directory)) for p in (book.slots, task_dir) if str(p.relative_to(directory)) not in completed]
    result = {'first': first, 'retry': {'attempted': attempted, 'completed': completed, 'missing_ancestor_fsyncs': missing},
              'ledger_rows_after_retry': len(ledger.parse(book.path.read_bytes())), 'retry_reserved_micro_usd': permit['reserved_micro_usd'],
              'scope': 'one injected fsync exception followed by a successful production reserve; no simulated power loss or sender'}
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('mode', choices=['audit', 'fault'])
    p.add_argument('--scratch', type=Path, required=True); p.add_argument('--output', type=Path, required=True)
    args = p.parse_args(); assert not args.output.exists()
    args.scratch.mkdir(parents=True, exist_ok=False)
    def save(results, complete):
        W(args.output, {'complete': complete, 'reviewed_commit': 'eb8bf13', 'mode': args.mode, 'results': results,
                        'program_sha256': r6.sha(Path(__file__)), 'live_model_calls': 0, 'real_credentials_read': 0})
    save({}, False)
    if args.mode == 'audit': results = audit_probes(args.scratch, save)
    else:
        results = {}
        for label in ('task', 'slots'):
            d = args.scratch/label; d.mkdir(); results[label] = fault_case(d, label)
            print(label, results[label], flush=True)
        assert set(results) == {'task', 'slots'}
    save(results, True)


if __name__ == '__main__': main()
