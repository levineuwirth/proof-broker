#!/usr/bin/env python3
"""Controls for the R6-009 checkpoint auditor: one relationship per mutation on copies of the runs and the campaign ledger.

Every mutation is applied to a fresh copy that first passes the unmutated audit; the mutated copy must be rejected at
exactly the named case. Where a mutation touches a record that later records commit to by digest, the production
finalizer (scan, terminal event, seal) or a coherent ledger rebind is applied so that the rejection is the intended
relationship and not an incidental hash mismatch. The set of controls is a fixed population: the record is refused unless
exactly these names were exercised. Carried forward: the R6-009 v1 controls; the fourteen corrupted-copy probes and the
missing-case probe of the independent review; the reviewer's type-substitution probe at audit level; a second-task control
(D1 bytes in a C8 run); a refusal control; the grant-ordering control driven through the production auditor on a
coherently rebound transport record; and, after the v2 review, its ten further corrupted copies: a coherent zero reservation
against a 102,400 µUSD admission, a foreign adapter mount with the approved basename, a coherently rebound non-zero sender
exit, a false credential-hash pair, and five false receipt payloads (admission, reservation, reconciliation, HTTP observation,
transport validation) plus a false resource-limit receipt; and, after the v3 review, its five: a foreign stdlib source with its
role, a foreign interpreter source with its role, an extra read-only repository mount, and non-zero exits of the assembly and
whole-declaration validation stages with matching finish receipts.
"""
import argparse
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
import cohort_episode as driver
import credential
import events
import run as r6

spec = importlib.util.spec_from_file_location('r6_review_cohort_audit', Path(__file__).with_name('cohort_audit.py'))
audit = importlib.util.module_from_spec(spec); spec.loader.exec_module(audit)
J = lambda p: json.loads(Path(p).read_bytes()); W = lambda p, v: Path(p).write_bytes(events.canonical(v)+b'\n')
D1, C8 = audit.D1, audit.C8
LAST, LAST_D1, FIRST = 'r2-c8-draw2', 'r2-d1-draw2', 'r1-d1-draw1'
EXPECTED = {
    # R6-009 v1 controls, carried forward
    'instruction_altered_in_one_run': f'{LAST_D1}:versions:policy_lock_contract_campaign_bound',
    'policy_digest_in_request': f'{LAST_D1}:request:regenerated_under_contract',
    'arguments_option_altered': f'{LAST_D1}:envelope:recomputed_from_contract',
    'revision_row_removed': 'ledger:continuous_across_revisions',
    'slot_marker_removed': 'ledger:continuous_across_revisions',
    'retained_contract_altered': f'{FIRST}:versions:policy_lock_contract_campaign_bound',
    'run_added': 'population:exactly_expected_runs',
    # the independent review's corrupted-copy probes (R6-009-REVIEW-AUDIT-PROBES.json), each previously accepted
    'serialized_body_altered': f'{LAST_D1}:transport:bodies_are_the_contract_rendering',
    'outbound_body_altered': f'{LAST_D1}:transport:bodies_are_the_contract_rendering',
    'received_body_altered': f'{LAST_D1}:transport:bodies_are_the_contract_rendering',
    'raw_provider_response_altered': f'{LAST_D1}:transport:local_send_and_remote_receipt',
    'reconstruction_context_false': f'{LAST_D1}:proof:shared_checker',
    'summary_wrong_task': f'{LAST_D1}:summary:bound_to_audited_records',
    'summary_nested_allowance_zero': f'{LAST_D1}:summary:bound_to_audited_records',
    'accounting_allowance_zero': f'{LAST_D1}:summary:bound_to_audited_records',
    'credential_receipt_false': f'{LAST_D1}:credential_receipt:recorded',
    'proposer_attribution_altered': f'{LAST_D1}:proof:attribution_passed_through',
    'authoritative_ledger_mount_changed': f'{LAST_D1}:mounts:authority_bound',
    'retained_imported_module_changed': 'modules:bound_to_retained_copies',
    'unlisted_file_after_seal': f'{LAST_D1}:seal:retained_hashes',
    'publication_report_rejected': f'{LAST_D1}:publication:recomputed',
    'audit_case_removed': 'cases:population',
    # new for revision 2
    'arguments_option_type_altered': f'{LAST_D1}:envelope:recomputed_from_contract',
    'accounting_and_summary_allowance_zero': f'{LAST_D1}:accounting:recomputed',
    'd1_bytes_in_c8_run': f'{LAST}:transport:bodies_are_the_contract_rendering',
    'refusal_code_altered': 'r2-d1-draw1-refused:pricing:host_admission_rederived',
    'permit_task_join_altered': f'{LAST}:ledger:permit_and_reconciliation_bound',
    'grant_reordered_coherent': f'{LAST}:grant:ordered_before_first_header_byte',
    # the v2 review's corrupted copies (R6-009-V2-REVIEW-PROBES.json), each previously accepted
    'zero_reservation_coherent': f'{LAST}:ledger:reservation_priced_from_contract_limits',
    'mounted_adapter_foreign': f'{LAST}:mounts:authority_bound',
    'nonzero_sender_exit_coherent': f'{LAST}:receipts:stage_returned_within_frozen_limits',
    'credential_hash_pair_false': f'{LAST}:credential_receipt:recorded',
    'pricing_admitted_receipt_wrong': f'{LAST}:receipts:payloads_bound_to_records',
    'request_reserved_receipt_wrong': f'{LAST}:receipts:payloads_bound_to_records',
    'reservation_reconciled_receipt_wrong': f'{LAST}:receipts:payloads_bound_to_records',
    'https_observed_receipt_wrong': f'{LAST}:receipts:payloads_bound_to_records',
    'transport_validated_receipt_false': f'{LAST}:receipts:payloads_bound_to_records',
    'resource_limit_receipt_wrong': f'{LAST}:receipts:stage_returned_within_frozen_limits',
    # the v3 review's corrupted copies (R6-009-V3-REVIEW-PROBES.json), each previously accepted
    'runtime_source_and_role_foreign': f'{LAST}:command:reconstructed_from_pinned_runtime_and_layout',
    'interpreter_source_and_role_foreign': f'{LAST}:command:reconstructed_from_pinned_runtime_and_layout',
    'extra_readonly_host_mount': f'{LAST}:command:reconstructed_from_pinned_runtime_and_layout',
    'nonzero_assembly_exit_coherent': f'{LAST}:stages:every_stage_on_the_path_returned',
    'nonzero_whole_validation_exit_coherent': f'{LAST}:stages:every_stage_on_the_path_returned',
}
RUNS = audit.POPULATIONS[audit.contract.NAME]['runs']
CONTROLS = ('baseline', *EXPECTED)


def run_audit(root, ledgers):
    try: result = audit.audit(root, ledgers, audit.contract.NAME)
    except audit.Rejection as rejection: return {'accepted': False, 'rejected_case': rejection.case, 'detail': str(rejection)}
    return {'accepted': result['accepted'], 'case_count': result['case_count']}


def rechain(run, rows):
    previous = '0'*64
    for i, row in enumerate(rows):
        row.update(sequence=i, previous_hash=previous); row.pop('event_hash', None); row['event_hash'] = events.digest(row); previous = row['event_hash']
    (run/'events.ndjson').write_bytes(b''.join(events.canonical(r)+b'\n' for r in rows))


def refinalize(run, change):
    """Apply `change` to the run's artifacts and pre-terminal events, then finalize with the production driver: scan, terminal event, seal."""
    rows = events.read(run/'events.ndjson'); rows.pop(); change(run, rows); rechain(run, rows)
    for n in ('publication-scan.json', 'publication-final.json', 'seal.json'): (run/n).unlink()
    nonce = J(run/'credential-canary.json')['nonce']
    driver.finalize(run, credential.derive(nonce), nonce, J(run/'credential-summary.json'), False)


def change_json(run, relative, change):
    p = run/relative; value = J(p); old = events.canonical(value)
    change(value); assert events.canonical(value) != old, 'vacuous mutation'
    W(p, value)


def rewrite_ledger(book, campaign, rows):
    previous = '0'*64
    for i, r in enumerate(rows):
        r.update(sequence=i, previous_hash=previous); r.pop('row_hash', None); r['row_hash'] = audit.ledger.digest(r); previous = r['row_hash']
    (book/'ledger.ndjson').write_bytes(b''.join(events.canonical(r)+b'\n' for r in rows))
    W(book/'head.json', {'campaign_id': campaign, 'rows': len(rows), 'last_hash': rows[-1]['row_hash']})


def event(rows, name, stage=None):
    matches = [r for r in rows if r['event'] == name and (stage is None or r['stage'] == stage)]
    assert len(matches) == 1, (name, len(matches))
    return matches[0]['payload']


def rebind_terminal_row(root, book, campaign, name, rec, change_events):
    """Rewrite the last run's reconciliation row and everything that commits to it: the authoritative ledger and head, the run's ledger
    snapshot, the supervisor receipts, then the scan, terminal event and seal."""
    run = root/name; rows = [json.loads(l) for l in (book/'ledger.ndjson').read_bytes().splitlines()]
    index = next(i for i, r in enumerate(rows) if r['kind'] in audit.ledger.TERMINAL and r['reservation_id'] == rec['reservation_id'])
    assert index == len(rows)-1, 'the control rebinds only a terminal row that is the last row'
    rows[index] = dict(rec); rewrite_ledger(book, campaign, rows)
    rec = rows[index]; W(run/'campaign-reconciliation.json', rec); shutil.copyfile(book/'ledger.ndjson', run/'ledger-after.ndjson')
    def change(run, rows):
        event(rows, 'reservation_reconciled').update(row_hash=rec['row_hash'], ledger_sha256=r6.sha(run/'ledger-after.ndjson'))
        change_events(run, rows)
    refinalize(run, change)
    return rec


def rebind_http(root, book, campaign, name, change):
    """Mutate the last run's transport record and rebind every digest that commits to it."""
    run = root/name; http_path = run/'stages/proposal-1/output/http.json'
    change_json(run, 'stages/proposal-1/output/http.json', change)
    rec = J(run/'campaign-reconciliation.json'); rec['evidence']['http_sha256'] = r6.sha(http_path)
    rebind_terminal_row(root, book, campaign, name, rec, lambda run, rows: event(rows, 'https_observed').__setitem__('http_sha256', r6.sha(http_path)))


def coherent_exit(root, book, campaign, name):
    """The sender's process record says exit 7; the finish receipt, reconciliation evidence, ledger, snapshot and receipts all agree with it."""
    run = root/name; p = run/'stages/proposal-1/proposal-1.process.json'
    process = J(p); assert process['exit_code'] == 0; process['exit_code'] = 7; W(p, process)
    rec = J(run/'campaign-reconciliation.json'); rec['evidence']['process_sha256'] = r6.sha(p); rec['evidence']['process_exit_code'] = 7
    def change(run, rows):
        finish = event(rows, 'stage_finished', 'proposal-1'); finish.clear(); finish.update(process)
    rebind_terminal_row(root, book, campaign, name, rec, change)


def coherent_zero(root, book, campaign, name):
    """One false reservation amount carried through every mirror: permit, ledger rows, snapshots, reservation, accounting, summary, receipts.
    The host and actor pricing records still say 102,400."""
    run = root/name; rows = [json.loads(l) for l in (book/'ledger.ndjson').read_bytes().splitlines()]
    permit, rec = rows[-2], rows[-1]
    assert permit['reservation_id'] == rec['reservation_id'] and permit['kind'] == 'reservation' and permit['reserved_micro_usd'] == 102400
    permit['reserved_micro_usd'] = 0; permit['reservation']['reserved_micro_usd'] = 0
    rewrite_ledger(book, campaign, rows); permit, rec = rows[-2], rows[-1]
    W(run/'campaign-permit.json', permit); W(run/'campaign-reconciliation.json', rec)
    (run/'transport-ledger.ndjson').write_bytes(b''.join(events.canonical(r)+b'\n' for r in rows[:-1]))
    shutil.copyfile(book/'ledger.ndjson', run/'ledger-after.ndjson')
    reservation = J(run/'reservation.json')
    reservation.update(reserved_micro_usd=0, ledger_row_hash=permit['row_hash'], ledger_sha256=r6.sha(run/'transport-ledger.ndjson')); W(run/'reservation.json', reservation)
    accounting = J(run/'accounting.json'); accounting['reservation'] = dict(reservation); W(run/'accounting.json', accounting)
    summary = J(run/'credential-summary.json'); summary['accounting'] = dict(accounting); W(run/'credential-summary.json', summary)
    def change(run, rows):
        reserved = event(rows, 'request_reserved'); reserved.clear(); reserved.update(reservation)
        event(rows, 'reservation_reconciled').update(row_hash=rec['row_hash'], ledger_sha256=r6.sha(run/'ledger-after.ndjson'))
    refinalize(run, change)


def mutate(name, root, ledgers):
    campaign = J(root/LAST/'search-policy.json')['campaign_id']; book = ledgers/campaign/'rehearsal'
    out = 'stages/proposal-1/output/'; last_d1 = root/LAST_D1
    if name == 'instruction_altered_in_one_run':
        refinalize(last_d1, lambda run, rows: (run/'transport-instruction.txt').write_text((run/'transport-instruction.txt').read_text()+' '))
    elif name == 'policy_digest_in_request':
        refinalize(last_d1, lambda run, rows: change_json(run, 'live-request.json', lambda v: v.__setitem__('policy_sha256', J(run/'search-policy.json')['config_sha256'])))
    elif name == 'arguments_option_altered':
        refinalize(last_d1, lambda run, rows: change_json(run, 'live-arguments.json', lambda v: v.__setitem__('max_output_tokens', 4097)))
    elif name == 'arguments_option_type_altered':  # same Python value, different JSON type and bytes
        refinalize(last_d1, lambda run, rows: change_json(run, 'live-arguments.json', lambda v: v.__setitem__('max_output_tokens', 4096.0)))
    elif name == 'revision_row_removed':
        rows = [json.loads(l) for l in (book/'ledger.ndjson').read_bytes().splitlines()]
        rewrite_ledger(book, campaign, [r for r in rows if r['kind'] != 'authorization_revision'])
    elif name == 'slot_marker_removed':
        rows = [json.loads(l) for l in (book/'ledger.ndjson').read_bytes().splitlines()]; rid = J(root/FIRST/'campaign-permit.json')['reservation_id']
        rewrite_ledger(book, campaign, [r for r in rows if not (r['kind'] == 'send_grant' and r['reservation_id'] == rid)])
    elif name == 'retained_contract_altered':
        refinalize(root/FIRST, lambda run, rows: change_json(run, 'provenance/cohort-harness/contracts/farkas-proposal-contract-v1.json', lambda v: v.__setitem__('scope', 'altered')))
    elif name == 'run_added': shutil.copytree(root/LAST, root/'r2-c8-draw3')
    elif name in ('serialized_body_altered', 'outbound_body_altered', 'received_body_altered'):
        base = name.removesuffix('_altered').replace('_', '-')+'.json'
        refinalize(last_d1, lambda run, rows: change_json(run, out+base, lambda v: v['input'][0].__setitem__('content', v['input'][0]['content']+' ALTERED')))
    elif name == 'raw_provider_response_altered':
        refinalize(last_d1, lambda run, rows: change_json(run, out+'provider-response.json', lambda v: v.__setitem__('status', 'failed')))
    elif name == 'reconstruction_context_false':
        def change(run, rows):
            change_json(run, 'stages/reconstruct/output/context.json', lambda v: v.__setitem__('target', 'False'))
            matches = [r for r in rows if r['event'] == 'context_validated' and r['stage'] == 'reconstruct']; assert len(matches) == 1
            matches[0]['payload']['captured_context_sha256'] = r6.sha(run/'stages/reconstruct/output/context.json')
        refinalize(last_d1, change)
    elif name == 'summary_wrong_task':
        refinalize(last_d1, lambda run, rows: change_json(run, 'credential-summary.json', lambda v: v.__setitem__('task_id', C8)))
    elif name == 'summary_nested_allowance_zero':
        refinalize(last_d1, lambda run, rows: change_json(run, 'credential-summary.json', lambda v: v['accounting'].__setitem__('allowance_consumed', 0)))
    elif name == 'accounting_allowance_zero':
        refinalize(last_d1, lambda run, rows: change_json(run, 'accounting.json', lambda v: v.__setitem__('allowance_consumed', 0)))
    elif name == 'accounting_and_summary_allowance_zero':  # both mirrors agree on the wrong value: only recomputation catches it
        def change(run, rows):
            change_json(run, 'accounting.json', lambda v: v.__setitem__('allowance_consumed', 0))
            change_json(run, 'credential-summary.json', lambda v: v['accounting'].__setitem__('allowance_consumed', 0))
        refinalize(last_d1, change)
    elif name == 'credential_receipt_false':
        refinalize(last_d1, lambda run, rows: change_json(run, 'credential-receipt.json', lambda v: v.__setitem__('exact_receipt', False)))
    elif name == 'proposer_attribution_altered':
        def change(run, rows):
            matches = [r for r in rows if r['event'] == 'recovery_started']; assert len(matches) == 1 and matches[0]['payload']['proposer'] == 'canned_provider_response'
            matches[0]['payload']['proposer'] = 'live_model_response'
        refinalize(last_d1, change)
    elif name == 'authoritative_ledger_mount_changed':
        def alter(v):
            argv = v['argv']; hits = [i for i, x in enumerate(argv) if x == '/ledger.ndjson' and i >= 2 and argv[i-2] == '--ro-bind']; assert len(hits) == 1
            argv[hits[0]-1] = '/tmp/non-authoritative-ledger.ndjson'
        refinalize(last_d1, lambda run, rows: change_json(run, 'stages/proposal-1/command.json', alter))
    elif name == 'retained_imported_module_changed':
        p = last_d1/'provenance/campaign-harness/campaign_ledger.py'; assert p.exists()
        refinalize(last_d1, lambda run, rows: p.write_bytes(p.read_bytes()+b'\n# altered retained imported module\n'))
    elif name == 'unlisted_file_after_seal':
        (last_d1/'unlisted-evidence.txt').write_text('added after scan and seal\n')
    elif name == 'publication_report_rejected':  # coherent report/terminal/seal digests; one false publication result must reject
        change_json(last_d1, 'publication-scan.json', lambda v: v.__setitem__('accepted', False))
        rows = events.read(last_d1/'events.ndjson'); rows[-1]['payload']['publication_scan_sha256'] = r6.sha(last_d1/'publication-scan.json')
        rechain(last_d1, rows); driver.publication_driver.seal(last_d1, True)
    elif name == 'd1_bytes_in_c8_run':  # the second-task control at audit level: a C8 run whose serialized bytes are D1's
        def change(run, rows):
            shutil.copyfile(last_d1/out/'serialized-body.json', run/out/'serialized-body.json')
            change_json(run, out+'pricing-check.json', lambda v: v.__setitem__('body_sha256', r6.sha(run/out/'serialized-body.json')))
        refinalize(root/LAST, change)
    elif name == 'refusal_code_altered':
        refinalize(root/'r2-d1-draw1-refused', lambda run, rows: change_json(run, 'host-pricing-admission.json', lambda v: v.__setitem__('failure_code', 'cohort_slot_not_scheduled')))
    elif name == 'permit_task_join_altered':  # the permit's task identity names the other task's manifest
        other = J(root/LAST_D1/'campaign-permit.json')['task_manifest_sha256']
        refinalize(root/LAST, lambda run, rows: change_json(run, 'campaign-permit.json', lambda v: v.__setitem__('task_manifest_sha256', other)))
    elif name == 'grant_reordered_coherent':
        rebind_http(root, book, campaign, LAST, lambda v: v.__setitem__('header_send_at_ns', v['tls_verified_at_ns']))
    elif name == 'zero_reservation_coherent': coherent_zero(root, book, campaign, LAST)
    elif name == 'nonzero_sender_exit_coherent': coherent_exit(root, book, campaign, LAST)
    elif name == 'mounted_adapter_foreign':  # the approved basename from an unapproved directory
        def alter(v):
            argv = v['argv']; hits = [i for i, x in enumerate(argv) if x == '/adapter.py' and i >= 2 and argv[i-2] == '--ro-bind']; assert len(hits) == 1
            argv[hits[0]-1] = '/tmp/r6-009-controls-unapproved/cohort_https.py'
        refinalize(root/LAST, lambda run, rows: change_json(run, 'stages/proposal-1/command.json', alter))
    elif name == 'credential_hash_pair_false':  # both hashes false but equal, in the file and its receipt event
        def change(run, rows):
            receipt = J(run/'credential-receipt.json'); receipt['expected_authorization_sha256'] = receipt['observed_authorization_sha256'] = '0'*64
            W(run/'credential-receipt.json', receipt); mirror = event(rows, 'credential_receipt_checked'); mirror.clear(); mirror.update(receipt)
        refinalize(root/LAST, change)
    elif name == 'pricing_admitted_receipt_wrong':
        refinalize(root/LAST, lambda run, rows: event(rows, 'pricing_admitted').__setitem__('admission_sha256', '0'*64))
    elif name == 'request_reserved_receipt_wrong':
        refinalize(root/LAST, lambda run, rows: event(rows, 'request_reserved').__setitem__('reserved_micro_usd', 0))
    elif name == 'reservation_reconciled_receipt_wrong':
        refinalize(root/LAST, lambda run, rows: event(rows, 'reservation_reconciled').__setitem__('row_hash', '0'*64))
    elif name == 'https_observed_receipt_wrong':
        refinalize(root/LAST, lambda run, rows: event(rows, 'https_observed').__setitem__('http_sha256', '0'*64))
    elif name == 'transport_validated_receipt_false':
        refinalize(root/LAST, lambda run, rows: event(rows, 'transport_validated')['outbound_envelope'].__setitem__('accepted', False))
    elif name == 'resource_limit_receipt_wrong':
        refinalize(root/LAST, lambda run, rows: event(rows, 'stage_started', 'proposal-1').__setitem__('wall_limit_seconds', 0))
    elif name in ('runtime_source_and_role_foreign', 'interpreter_source_and_role_foreign'):  # the mount and the recorded role agree; the pin does not
        key = 'runtime_path' if name.startswith('runtime') else 'python'
        def change(run, rows):
            roles = J(run/'provenance/roles.json'); old = roles[key]; new = '/tmp/r6-009-controls-unapproved/'+('stdlib' if key == 'runtime_path' else 'python3.14')
            def alter(v):
                hits = [i for i, x in enumerate(v['argv']) if x == old and i >= 1 and v['argv'][i-1] == '--ro-bind']; assert len(hits) == 1
                v['argv'][hits[0]] = new
            change_json(run, 'stages/proposal-1/command.json', alter); roles[key] = new; W(run/'provenance/roles.json', roles)
        refinalize(root/LAST, change)
    elif name == 'extra_readonly_host_mount':  # one more read-only mount, everything else unchanged
        refinalize(root/LAST, lambda run, rows: change_json(run, 'stages/proposal-1/command.json', lambda v: v['argv'].__setitem__(slice(1, 1), ['--ro-bind', str(ROOT.parents[1]), '/extra-reference'])))
    elif name in ('nonzero_assembly_exit_coherent', 'nonzero_whole_validation_exit_coherent'):  # a later stage failed, its finish receipt agrees
        stage = 'assembly' if 'assembly' in name else 'validation-whole'
        def change(run, rows):
            path = run/'stages'/stage/(stage+'.process.json'); record = J(path); assert record['exit_code'] == 0; record['exit_code'] = 7; W(path, record)
            finish = event(rows, 'stage_finished', stage); finish.clear(); finish.update(record)
        refinalize(root/LAST, change)
    else: raise AssertionError(name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    results = {}
    for name in CONTROLS:
        with tempfile.TemporaryDirectory(prefix='r6-009-controls-') as temp:
            root = Path(temp)/'cohort-runs'; ledgers = Path(temp)/'ledgers'
            shutil.copytree(ROOT/RUNS, root); shutil.copytree(ROOT/'ledgers/campaigns', ledgers)
            baseline = run_audit(root, ledgers); assert baseline['accepted'] is True, baseline
            if name == 'baseline': results[name] = baseline; continue
            if name == 'audit_case_removed':
                original = audit.Audit.require
                def omit(self, ok, case, detail=''):
                    if case == f'{LAST_D1}:proof:shared_checker': return
                    return original(self, ok, case, detail)
                with patch.object(audit.Audit, 'require', omit): observed = run_audit(root, ledgers)
            else:
                mutate(name, root, ledgers); observed = run_audit(root, ledgers)
            assert observed['accepted'] is False and observed['rejected_case'] == EXPECTED[name], (name, observed)
            results[name] = {'rejected': True, 'rejected_case': observed['rejected_case']}
            print(name, observed['rejected_case'], flush=True)
    assert tuple(results) == CONTROLS and set(results) == {'baseline', *EXPECTED}, sorted(results)
    record = {'passed': True, 'controls': len(results), 'expected_controls': list(CONTROLS), 'results': results, 'runs': RUNS, 'revision': audit.contract.NAME,
              'auditor_sha256': r6.sha(Path(__file__).with_name('cohort_audit.py')), 'program_sha256': r6.sha(Path(__file__)),
              'live_model_calls': 0, 'credentials_read': 0, 'scope': 'temporary copies; one relationship per mutation; exact control population'}
    r6.write_json(args.output, record)
    print(json.dumps({'passed': True, 'controls': len(results), 'baseline_cases': results['baseline']['case_count']}, indent=1))


if __name__ == '__main__':
    main()
