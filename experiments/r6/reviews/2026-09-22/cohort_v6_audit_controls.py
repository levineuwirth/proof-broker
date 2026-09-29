#!/usr/bin/env python3
"""Controls for the R6-013 cohort v6 auditor: one relationship per mutation on copies of the runs, the campaign ledgers, the classification
and the historical v4/v5 runs.

Every mutation is applied to a fresh copy that first passes the unmutated audit; the mutated copy must be rejected at exactly the named
case. Where a mutation touches a record that later records commit to by digest, the production finalizer (scan, terminal event, seal),
the historical seal, the classification's seal or a coherent ledger rebind is applied, so that the rejection is the intended relationship
and not an incidental hash mismatch. The control population is fixed: the record is refused unless exactly these names were exercised.

Carried forward from the R6-009 controls (`reviews/2026-09-14/cohort_audit_controls.py`), each adapted to a site run or stated as having
no instance (`NOT_APPLICABLE`); added for R6-013: the consumption receipt removed, forged, naming the wrong closer, a closer selection for
another certificate, a verdict naming another closer, reconstruction IR differing from preparation; a refused reconstruction without
branch evidence, with its diagnosis altered, from a crashed process, with an unrelated error, and with fabricated completion; site
identity, preparation, context, renaming, eligibility, pricing and bridge-revision bindings; and the v4 and v5 historical checks,
including a synthesized v5 consumption receipt.

Revision 2, after the R6-013 review: its six accepted probes (`reviews/2026-09-23/cohort_v6_review_probes.py`) under their names, each now
rejected at its own case, and one control per new binding: the refused path's trace and child component, the proof path's dispatched final
IR, a coherent relabeling of the refused closer, foreign inputs in the certificate-check, assembly, preparation, pipeline and replay
commands, an altered export target, and a wrong historical kernel target in v4. Two earlier controls now reject at the new
evidence-binding case, which runs before the closer-selection and consumption cases.

Revision 3, after the revision 2 review (`reviews/2026-09-23/cohort_v6_v2_review_probes.py`): its three rejecting probes under their names,
and one control per new binding: a changed helper on the proof path, a library pair removed in one run, a library pair added to every copy
of one stage (so the first-observed block cannot be its own authority), and a challenge path inside the recorded root. The review's fourth
probe (`replay_challenge_unverified_location`) is a path qualification: it stays accepted, and is recorded under `CHARACTERIZED`.
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
import proposal_instrument as overlay
import run as r6
import site_network
import site_representability as rep
import site_task

spec = importlib.util.spec_from_file_location('r6_013_cohort_audit', Path(__file__).with_name('cohort_v6_audit.py'))
audit = importlib.util.module_from_spec(spec); spec.loader.exec_module(audit)
J = lambda p: json.loads(Path(p).read_bytes()); W = lambda p, v: Path(p).write_bytes(events.canonical(v)+b'\n')
LAST, NAT, FIRST, REF, NEG, IFACE, REL, RENAMED = ('l099-draw1', 'l070-draw1', 'l069-draw1', 'l204-draw1', 'l170-draw1', 'l098-draw1',
                                                   'l096-draw2-format', 'l178-draw1')
EXPECTED = {
    # R6-009 v1 controls, adapted
    'instruction_altered_in_one_run': f'{NAT}:versions:policy_lock_contract_campaign_bound',
    'policy_digest_in_request': f'{NAT}:request:regenerated_under_contract',
    'arguments_option_altered': f'{NAT}:envelope:recomputed_from_contract',
    'activation_row_removed': 'ledger:continuous_single_revision',
    'slot_marker_removed': 'ledger:continuous_single_revision',
    'retained_contract_altered': f'{FIRST}:versions:policy_lock_contract_campaign_bound',
    'run_added': 'population:exactly_expected_runs',
    # the R6-009 independent review's corrupted copies
    'serialized_body_altered': f'{NAT}:transport:bodies_are_the_contract_rendering',
    'outbound_body_altered': f'{NAT}:transport:bodies_are_the_contract_rendering',
    'received_body_altered': f'{NAT}:transport:bodies_are_the_contract_rendering',
    'raw_provider_response_altered': f'{NAT}:transport:local_send_and_remote_receipt',
    'reconstruction_context_false': f'{NAT}:proof:shared_checker',
    'summary_wrong_task': f'{NAT}:summary:bound_to_audited_records',
    'summary_nested_allowance_zero': f'{NAT}:summary:bound_to_audited_records',
    'accounting_allowance_zero': f'{NAT}:summary:bound_to_audited_records',
    'credential_receipt_false': f'{NAT}:credential_receipt:recorded',
    'proposer_attribution_altered': f'{NAT}:proof:attribution_passed_through',
    'authoritative_ledger_mount_changed': f'{NAT}:mounts:authority_bound',
    'retained_imported_module_changed': 'modules:bound_to_retained_copies',
    'unlisted_file_after_seal': f'{NAT}:seal:retained_hashes',
    'publication_report_rejected': f'{NAT}:publication:recomputed',
    'audit_case_removed': 'cases:population',
    # R6-009 revision 2
    'arguments_option_type_altered': f'{NAT}:envelope:recomputed_from_contract',
    'accounting_and_summary_allowance_zero': f'{NAT}:accounting:recomputed',
    'other_site_bytes_in_run': f'{LAST}:transport:bodies_are_the_contract_rendering',
    'interface_refusal_altered': f'{IFACE}:interface:refused_before_reservation',
    'permit_task_join_altered': f'{LAST}:ledger:permit_and_reconciliation_bound',
    'grant_reordered_coherent': f'{LAST}:grant:ordered_before_first_header_byte',
    # the R6-009 v2 review's corrupted copies
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
    # the R6-009 v3 review's corrupted copies
    'runtime_source_and_role_foreign': f'{LAST}:command:reconstructed_from_pinned_runtime_and_layout',
    'interpreter_source_and_role_foreign': f'{LAST}:command:reconstructed_from_pinned_runtime_and_layout',
    'extra_readonly_host_mount': f'{LAST}:command:reconstructed_from_pinned_runtime_and_layout',
    'nonzero_assembly_exit_coherent': f'{LAST}:stages:every_stage_on_the_path_returned',
    'nonzero_whole_validation_exit_coherent': f'{LAST}:stages:every_stage_on_the_path_returned',
    # R6-013: consumption receipts (LAST is the core ℤ closer; NAT the ℕ closer)
    'consumption_receipt_removed': f'{LAST}:chain:expected_sequence',
    'consumption_receipt_forged_certificate': f'{LAST}:reconstruction:evidence_bound',  # revision 2: bound before consumption
    'consumption_receipt_wrong_closer': f'{LAST}:proof:certificate_consumed',
    'nat_consumption_receipt_wrong_closer': f'{NAT}:proof:certificate_consumed',
    'closer_selection_wrong_certificate': f'{LAST}:reconstruction:evidence_bound',  # revision 2: bound before selection
    'verdict_names_another_closer': f'{LAST}:proof:certificate_consumed',
    'reconstruction_ir_differs_from_preparation': f'{LAST}:reconstruction:preparation_ir_equal',
    # R6-013: refused reconstruction
    'refusal_without_branch_evidence': f'{REF}:chain:expected_sequence',
    'refusal_diagnosis_altered': f'{REF}:reconstruction:refusal_diagnosed',
    'refusal_from_crashed_process': f'{REF}:reconstruction:refusal_diagnosed',
    'refusal_with_unrelated_error': f'{REF}:reconstruction:refusal_diagnosed',
    'refused_run_certificate_verdict_false': f'{REF}:certificate:verified_and_bound',
    'fabricated_verdict_on_refused_run': f'{REF}:summary:bound_to_audited_records',
    'fabricated_export_stage_on_refused_run': f'{REF}:receipts:payloads_bound_to_records',  # a stage without its supervisor receipts
    'negative_control_verifier_accepted': f'{NEG}:negative:verifier_rejected_and_stopped',
    # R6-013: sites, eligibility and revision bindings
    'prepared_problem_differs_from_classification': f'{NAT}:site:prepared_equals_classification',
    'unrepaired_helper_in_preparation_input': f'{NAT}:site:preparation_is_the_repaired_helper',
    'frozen_context_altered_in_preparation': f'{NAT}:site:original_context_bound',
    'search_context_rename_reverted': f'{RENAMED}:site:renaming_recorded',
    'retained_site_lock_altered': f'{NAT}:site:identity_bound',
    'classification_certificate_altered': 'eligibility:recomputed_fifteen_sites',
    'pricing_origin_not_the_reviewed_capture': 'revision:runtime_pricing_ledger_publication_bound',
    'bridge_patch_not_revision_2': 'revision:runtime_pricing_ledger_publication_bound',
    # R6-013: history
    'history_v4_run_removed': 'history_v4:population_exact',
    'history_v4_seal_broken': 'history_v4:seals_and_chains',
    'history_v4_certificate_verdict_false': 'history_v4:verified_certificates',
    'history_v4_guard_message_removed': 'history_v4:reconstruction_errors',
    'history_v4_terminal_row_dropped': 'history_v4:ledger_dispositions',
    'history_v5_run_removed': 'history_v5:population_exact',
    'history_v5_seal_broken': 'history_v5:seals_and_chains',
    'history_v5_consumption_receipt_synthesized': 'history_v5:qualified_kernel_successes',
    'history_v5_refusal_recategorized': 'history_v5:closer_refusals_recorded',
    'history_v5_terminal_row_dropped': 'history_v5:ledger_dispositions',
    # R6-013 review: the six accepted probes, by the reviewer's names
    'refused_dispatch_certificate': f'{REF}:reconstruction:evidence_bound',
    'refused_dispatch_final_ir': f'{REF}:reconstruction:evidence_bound',
    'refused_verification_started_certificate': f'{REF}:reconstruction:evidence_bound',
    'coherent_wrong_success_closer': f'{LAST}:reconstruction:closer_selected',
    'refused_reconstruction_foreign_packet': f'{REF}:stages:commands_reconstructed',
    'historical_wrong_kernel_target': 'history_v5:qualified_kernel_successes',
    # R6-013 review: one control per further binding
    'refused_dispatch_trace': f'{REF}:reconstruction:evidence_bound',
    'refused_child_foreign_component': f'{REF}:reconstruction:evidence_bound',
    'proof_dispatch_final_ir': f'{LAST}:reconstruction:evidence_bound',
    'coherent_wrong_refused_closer': f'{REF}:reconstruction:closer_selected',
    'certificate_check_foreign_packet': f'{LAST}:stages:commands_reconstructed',
    'assembly_foreign_prepared_problem': f'{LAST}:stages:commands_reconstructed',
    'preparation_foreign_input': f'{NAT}:stages:commands_reconstructed',
    'pipeline_prepare_foreign_ir': f'{IFACE}:stages:commands_reconstructed',
    'validation_foreign_solution': f'{NAT}:stages:commands_reconstructed',
    'export_target_altered': f'{NAT}:stages:commands_reconstructed',
    'history_v4_wrong_kernel_target': 'history_v4:kernel_reports_bound',
    # revision 2 review: the three rejecting probes, by the reviewer's names
    'refused_reconstruction_helper_changed': f'{REF}:reconstruction:sources_bound',
    'refused_reconstruction_source_changed': f'{REF}:reconstruction:sources_bound',
    'library_source_escapes_system_directory': 'l069-draw1:stages:commands_reconstructed',  # every copy altered; the first run audited rejects
    # revision 2 review: one control per further binding
    'proof_reconstruction_helper_changed': f'{LAST}:reconstruction:sources_bound',
    'library_pair_removed_in_one_run': f'{LAST}:stages:commands_reconstructed',
    'library_pair_added_to_every_assembly': 'l069-draw1:stages:commands_reconstructed',
    'challenge_path_inside_recorded_root': f'{NAT}:stages:commands_reconstructed',
}
# Accepted by design: a qualification, not a binding (the temporary challenge's bytes were not retained).
CHARACTERIZED = {'replay_challenge_unverified_location': 'both replay commands name one path of the driver pattern outside the recorded root; accepted, '
                                                         'because the temporary copy was not retained and its content is a property of the pinned driver'}
REVIEW_PROBES = ('refused_dispatch_certificate', 'refused_dispatch_final_ir', 'refused_verification_started_certificate',
                 'coherent_wrong_success_closer', 'refused_reconstruction_foreign_packet', 'historical_wrong_kernel_target')
NOT_APPLICABLE = {'revision_row_removed': 'one revision: its only revision row is the activation, exercised by activation_row_removed',
                  'refusal_code_altered': 'no slot-consumed refusal in a single-revision checkpoint; the refusal kind here is exercised by interface_refusal_altered',
                  'd1_bytes_in_c8_run': 'renamed other_site_bytes_in_run: l070 bytes in the l099 run'}
CONTROLS = ('baseline', *EXPECTED)


def run_audit(paths):
    try: result = audit.audit(paths['runs'], paths['ledgers'], paths['representability'], paths['v4'], paths['v5'])
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


def reseal_history(run, change):
    """A historical run: apply `change` to its artifacts and events (rechained), then the production seal with the recorded outcome."""
    rows = events.read(run/'events.ndjson'); change(run, rows); rechain(run, rows)
    accepted = J(run/'seal.json')['accepted']; (run/'seal.json').unlink(); site_network.seal(run, accepted)


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


def event(rows, name, stage=None, source='supervisor'):
    matches = [r for r in rows if r['event'] == name and (stage is None or r['stage'] == stage) and r['source'] == source]
    assert len(matches) == 1, (name, len(matches))
    return matches[0]['payload']


def child(rows, name):
    return event(rows, name, 'reconstruct', 'child_report')['data']


def rebind_terminal_row(root, book, campaign, name, rec, change_events):
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
    run = root/name; http_path = run/'stages/proposal-1/output/http.json'
    change_json(run, 'stages/proposal-1/output/http.json', change)
    rec = J(run/'campaign-reconciliation.json'); rec['evidence']['http_sha256'] = r6.sha(http_path)
    rebind_terminal_row(root, book, campaign, name, rec, lambda run, rows: event(rows, 'https_observed').__setitem__('http_sha256', r6.sha(http_path)))


def coherent_exit(root, book, campaign, name):
    run = root/name; p = run/'stages/proposal-1/proposal-1.process.json'
    process = J(p); assert process['exit_code'] == 0; process['exit_code'] = 7; W(p, process)
    rec = J(run/'campaign-reconciliation.json'); rec['evidence']['process_sha256'] = r6.sha(p); rec['evidence']['process_exit_code'] = 7
    def change(run, rows):
        finish = event(rows, 'stage_finished', 'proposal-1'); finish.clear(); finish.update(process)
    rebind_terminal_row(root, book, campaign, name, rec, change)


def coherent_zero(root, book, campaign, name):
    run = root/name; rows = [json.loads(l) for l in (book/'ledger.ndjson').read_bytes().splitlines()]
    permit, rec = rows[-2], rows[-1]
    assert permit['reservation_id'] == rec['reservation_id'] and permit['kind'] == 'reservation' and permit['reserved_micro_usd'] == 102400 and permit['episode_id'] == name
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


def rebind_verdict(run, rows, change):
    """Change verdict.json and the proof_validated receipt that names its digest."""
    change_json(run, 'verdict.json', change); event(rows, 'proof_validated')['verdict_sha256'] = r6.sha(run/'verdict.json')


def drop_terminal_row(book, campaign, episode_id):
    rows = [json.loads(l) for l in (book/'ledger.ndjson').read_bytes().splitlines()]
    kept = [r for r in rows if not (r['kind'] in audit.ledger.TERMINAL and r.get('episode_id') == episode_id)]
    assert len(kept) == len(rows)-1; rewrite_ledger(book, campaign, kept)


def mutate(name, paths):
    root, ledgers, representability, v4, v5 = paths['runs'], paths['ledgers'], paths['representability'], paths['v4'], paths['v5']
    campaign = J(root/LAST/'search-policy.json')['campaign_id']; book = ledgers/campaign/'rehearsal'
    out = 'stages/proposal-1/output/'; nat = root/NAT
    if name == 'instruction_altered_in_one_run':
        refinalize(nat, lambda run, rows: (run/'transport-instruction.txt').write_text((run/'transport-instruction.txt').read_text()+' '))
    elif name == 'policy_digest_in_request':
        refinalize(nat, lambda run, rows: change_json(run, 'live-request.json', lambda v: v.__setitem__('policy_sha256', J(run/'search-policy.json')['config_sha256'])))
    elif name == 'arguments_option_altered':
        refinalize(nat, lambda run, rows: change_json(run, 'live-arguments.json', lambda v: v.__setitem__('max_output_tokens', 4097)))
    elif name == 'arguments_option_type_altered':
        refinalize(nat, lambda run, rows: change_json(run, 'live-arguments.json', lambda v: v.__setitem__('max_output_tokens', 4096.0)))
    elif name == 'activation_row_removed':
        rows = [json.loads(l) for l in (book/'ledger.ndjson').read_bytes().splitlines()]
        rewrite_ledger(book, campaign, [r for r in rows if r['kind'] != 'activation'])
    elif name == 'slot_marker_removed':
        rows = [json.loads(l) for l in (book/'ledger.ndjson').read_bytes().splitlines()]; rid = J(root/FIRST/'campaign-permit.json')['reservation_id']
        rewrite_ledger(book, campaign, [r for r in rows if not (r['kind'] == 'send_grant' and r['reservation_id'] == rid)])
    elif name == 'retained_contract_altered':
        refinalize(root/FIRST, lambda run, rows: change_json(run, 'provenance/cohort-harness/'+audit.CONTRACT_PATH, lambda v: v.__setitem__('scope', 'altered')))
    elif name == 'run_added': shutil.copytree(root/LAST, root/'l099-draw3')
    elif name in ('serialized_body_altered', 'outbound_body_altered', 'received_body_altered'):
        base = name.removesuffix('_altered').replace('_', '-')+'.json'
        refinalize(nat, lambda run, rows: change_json(run, out+base, lambda v: v['input'][0].__setitem__('content', v['input'][0]['content']+' ALTERED')))
    elif name == 'raw_provider_response_altered':
        refinalize(nat, lambda run, rows: change_json(run, out+'provider-response.json', lambda v: v.__setitem__('status', 'failed')))
    elif name == 'reconstruction_context_false':
        def change(run, rows):
            change_json(run, 'stages/reconstruct/output/context.json', lambda v: v.__setitem__('target', 'False'))
            event(rows, 'context_validated', 'reconstruct')['captured_context_sha256'] = r6.sha(run/'stages/reconstruct/output/context.json')
        refinalize(nat, change)
    elif name == 'summary_wrong_task':
        refinalize(nat, lambda run, rows: change_json(run, 'credential-summary.json', lambda v: v.__setitem__('task_id', 'bracket-l204')))
    elif name == 'summary_nested_allowance_zero':
        refinalize(nat, lambda run, rows: change_json(run, 'credential-summary.json', lambda v: v['accounting'].__setitem__('allowance_consumed', 0)))
    elif name == 'accounting_allowance_zero':
        refinalize(nat, lambda run, rows: change_json(run, 'accounting.json', lambda v: v.__setitem__('allowance_consumed', 0)))
    elif name == 'accounting_and_summary_allowance_zero':
        def change(run, rows):
            change_json(run, 'accounting.json', lambda v: v.__setitem__('allowance_consumed', 0))
            change_json(run, 'credential-summary.json', lambda v: v['accounting'].__setitem__('allowance_consumed', 0))
        refinalize(nat, change)
    elif name == 'credential_receipt_false':
        refinalize(nat, lambda run, rows: change_json(run, 'credential-receipt.json', lambda v: v.__setitem__('exact_receipt', False)))
    elif name == 'proposer_attribution_altered':
        refinalize(nat, lambda run, rows: event(rows, 'recovery_started').__setitem__('proposer', 'live_model_response'))
    elif name == 'authoritative_ledger_mount_changed':
        def alter(v):
            argv = v['argv']; hits = [i for i, x in enumerate(argv) if x == '/ledger.ndjson' and i >= 2 and argv[i-2] == '--ro-bind']; assert len(hits) == 1
            argv[hits[0]-1] = '/tmp/non-authoritative-ledger.ndjson'
        refinalize(nat, lambda run, rows: change_json(run, 'stages/proposal-1/command.json', alter))
    elif name == 'retained_imported_module_changed':
        p = nat/'provenance/campaign-harness/campaign_ledger.py'; assert p.exists()
        refinalize(nat, lambda run, rows: p.write_bytes(p.read_bytes()+b'\n# altered retained imported module\n'))
    elif name == 'unlisted_file_after_seal':
        (nat/'unlisted-evidence.txt').write_text('added after scan and seal\n')
    elif name == 'publication_report_rejected':
        change_json(nat, 'publication-scan.json', lambda v: v.__setitem__('accepted', False))
        rows = events.read(nat/'events.ndjson'); rows[-1]['payload']['publication_scan_sha256'] = r6.sha(nat/'publication-scan.json')
        rechain(nat, rows); driver.network.seal(nat, True)
    elif name == 'other_site_bytes_in_run':
        def change(run, rows):
            shutil.copyfile(nat/out/'serialized-body.json', run/out/'serialized-body.json')
            change_json(run, out+'pricing-check.json', lambda v: v.__setitem__('body_sha256', r6.sha(run/out/'serialized-body.json')))
        refinalize(root/LAST, change)
    elif name == 'interface_refusal_altered':  # a different refusal message, its receipt rebound
        def change(run, rows):
            p = run/'stages/pipeline-prepare/pipeline-prepare.stderr'; p.write_text('Failure("a different refusal")\n')
            event(rows, 'interface_refused')['stderr_sha256'] = r6.sha(p)
        refinalize(root/IFACE, change)
    elif name == 'permit_task_join_altered':
        other = J(nat/'campaign-permit.json')['task_manifest_sha256']
        refinalize(root/LAST, lambda run, rows: change_json(run, 'campaign-permit.json', lambda v: v.__setitem__('task_manifest_sha256', other)))
    elif name == 'grant_reordered_coherent':
        rebind_http(root, book, campaign, LAST, lambda v: v.__setitem__('header_send_at_ns', v['tls_verified_at_ns']))
    elif name == 'zero_reservation_coherent': coherent_zero(root, book, campaign, LAST)
    elif name == 'nonzero_sender_exit_coherent': coherent_exit(root, book, campaign, LAST)
    elif name == 'mounted_adapter_foreign':
        def alter(v):
            argv = v['argv']; hits = [i for i, x in enumerate(argv) if x == '/adapter.py' and i >= 2 and argv[i-2] == '--ro-bind']; assert len(hits) == 1
            argv[hits[0]-1] = '/tmp/r6-013-controls-unapproved/cohort_https.py'
        refinalize(root/LAST, lambda run, rows: change_json(run, 'stages/proposal-1/command.json', alter))
    elif name == 'credential_hash_pair_false':
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
    elif name in ('runtime_source_and_role_foreign', 'interpreter_source_and_role_foreign'):
        key = 'runtime_path' if name.startswith('runtime') else 'python'
        def change(run, rows):
            roles = J(run/'provenance/roles.json'); old = roles[key]; new = '/tmp/r6-013-controls-unapproved/'+('stdlib' if key == 'runtime_path' else 'python3.14')
            def alter(v):
                hits = [i for i, x in enumerate(v['argv']) if x == old and i >= 1 and v['argv'][i-1] == '--ro-bind']; assert len(hits) == 1
                v['argv'][hits[0]] = new
            change_json(run, 'stages/proposal-1/command.json', alter); roles[key] = new; W(run/'provenance/roles.json', roles)
        refinalize(root/LAST, change)
    elif name == 'extra_readonly_host_mount':
        refinalize(root/LAST, lambda run, rows: change_json(run, 'stages/proposal-1/command.json', lambda v: v['argv'].__setitem__(slice(1, 1), ['--ro-bind', str(ROOT.parents[1]), '/extra-reference'])))
    elif name in ('nonzero_assembly_exit_coherent', 'nonzero_whole_validation_exit_coherent'):
        stage = 'assembly' if 'assembly' in name else 'validation-whole'
        def change(run, rows):
            path = run/'stages'/stage/(stage+'.process.json'); record = J(path); assert record['exit_code'] == 0; record['exit_code'] = 7; W(path, record)
            finish = event(rows, 'stage_finished', stage); finish.clear(); finish.update(record)
        refinalize(root/LAST, change)
    # ---------------------------------------------------------------- consumption receipts
    elif name == 'consumption_receipt_removed':
        refinalize(root/LAST, lambda run, rows: rows.remove(next(r for r in rows if r['source'] == 'child_report' and r['event'] == 'reconstruction_finished')))
    elif name == 'consumption_receipt_forged_certificate':
        def change(run, rows):
            data = child(rows, 'reconstruction_finished'); data['certificate'] = {**data['certificate'], 'cert_version': 'forged'}
        refinalize(root/LAST, change)
    elif name in ('consumption_receipt_wrong_closer', 'nat_consumption_receipt_wrong_closer'):
        run_name = LAST if name.startswith('consumption') else NAT
        def change(run, rows):
            data = child(rows, 'reconstruction_finished'); data['closer'] = 'term_mode_nat' if data['closer'] == 'term_mode_int' else 'term_mode_int'
        refinalize(root/run_name, change)
    elif name == 'closer_selection_wrong_certificate':
        refinalize(root/LAST, lambda run, rows: child(rows, 'closer_selected').__setitem__('certificate', {'forged': True}))
    elif name == 'verdict_names_another_closer':
        refinalize(root/LAST, lambda run, rows: rebind_verdict(run, rows, lambda v: v.__setitem__('closer', 'term_mode_ext')))
    elif name == 'reconstruction_ir_differs_from_preparation':
        def change(run, rows):
            ir = child(rows, 'reification_finished')['ir']; ir['context']['hypotheses'][0]['name'] += '_altered'
        refinalize(root/LAST, change)
    # ---------------------------------------------------------------- refused reconstruction
    elif name == 'refusal_without_branch_evidence':
        refinalize(root/REF, lambda run, rows: rows.remove(next(r for r in rows if r['source'] == 'child_report' and r['event'] == 'closer_selected')))
    elif name == 'refusal_diagnosis_altered':  # the record and its receipt agree on a diagnosis the evidence does not give
        def change(run, rows):
            change_json(run, 'reconstruction-refusal.json', lambda v: v.__setitem__('diagnosis', 'nat_closer_non_nat_goal'))
            receipt = event(rows, 'reconstruction_refused', 'reconstruct'); receipt.clear(); receipt.update(J(run/'reconstruction-refusal.json'))
        refinalize(root/REF, change)
    elif name == 'refusal_from_crashed_process':  # a killed process with a coherent finish receipt is not the closer's refusal
        def change(run, rows):
            p = run/'stages/reconstruct/reconstruct.process.json'; record = J(p); record['exit_code'] = 137; W(p, record)
            finish = event(rows, 'stage_finished', 'reconstruct'); finish.clear(); finish.update(record)
        refinalize(root/REF, change)
    elif name == 'refusal_with_unrelated_error':
        def change(run, rows):
            p = run/'stages/reconstruct/reconstruct.stderr'; p.write_text(p.read_text()+'/input/Frozen.lean:1:1: error: unrelated failure\n')
        refinalize(root/REF, change)
    elif name == 'refused_run_certificate_verdict_false':
        refinalize(root/REF, lambda run, rows: change_json(run, 'certificate-verdict.json', lambda v: v.__setitem__('accepted', False))
                   or event(rows, 'independent_certificate_verdict').__setitem__('accepted', False))
    elif name == 'fabricated_verdict_on_refused_run':
        refinalize(root/REF, lambda run, rows: shutil.copyfile(root/LAST/'verdict.json', run/'verdict.json'))
    elif name == 'fabricated_export_stage_on_refused_run':
        refinalize(root/REF, lambda run, rows: shutil.copytree(root/LAST/'stages/export', run/'stages/export'))
    elif name == 'negative_control_verifier_accepted':
        def change(run, rows):
            change_json(run, 'certificate-verdict.json', lambda v: v.__setitem__('accepted', True))
            receipt = event(rows, 'independent_certificate_verdict'); receipt['accepted'] = True
        refinalize(root/NEG, change)
    # ---------------------------------------------------------------- sites, eligibility, revision
    elif name == 'prepared_problem_differs_from_classification':
        refinalize(nat, lambda run, rows: change_json(run, 'prepared.json', lambda v: v['rows'][0].__setitem__('constant', str(int(v['rows'][0]['constant'])+1))))
    elif name == 'unrepaired_helper_in_preparation_input':
        refinalize(nat, lambda run, rows: (run/'preparation-input/PreparationCapture.lean').write_text(overlay.capture_source(site_task.get('bracket-l070'), True)))
    elif name == 'frozen_context_altered_in_preparation':
        refinalize(nat, lambda run, rows: change_json(run, 'stages/preparation/output/context.json', lambda v: v.__setitem__('target', 'False')))
    elif name == 'search_context_rename_reverted':  # both the run and the classification record the unrenamed name; the classification's record does not
        def revert(v):
            e = next(e for e in v['search_context'] if e['original_name'] != e['search_name']); e['search_name'] = e['original_name']
        change_json(representability/'bracket-l178', 'stages/preparation/output/reification.json', revert); rep.seal(representability/'bracket-l178')
        refinalize(root/RENAMED, lambda run, rows: shutil.copyfile(representability/'bracket-l178/stages/preparation/output/reification.json',
                                                                   run/'stages/preparation/output/reification.json'))
    elif name == 'retained_site_lock_altered':
        refinalize(nat, lambda run, rows: change_json(run, 'provenance/site-harness/policies/'+audit.SITE_LOCK, lambda v: v.__setitem__('site_task.py', '0'*64)))
    elif name == 'classification_certificate_altered':
        run = representability/'bracket-l204'
        change_json(run, 'representability.json', lambda v: v['certificate'][0].__setitem__('coefficient', str(int(v['certificate'][0]['coefficient'])+1)))
        rows = events.read(run/'events.ndjson'); rows.pop(); rows.pop()
        rechain(run, rows)
        events.append(run, 'representability', 'classified', {'class': J(run/'representability.json')['class'], 'representability_sha256': r6.sha(run/'representability.json')})
        events.append(run, 'episode', 'episode_finished', {'representability_sha256': r6.sha(run/'representability.json')})
        rep.seal(run)
    elif name == 'pricing_origin_not_the_reviewed_capture':
        def change(run, rows):
            for d in ('pricing-origin', 'pricing-sources'):
                p = run/d/'caching.receipt.json'; value = J(p); value['r6_control'] = 'altered'; W(p, value)
        refinalize(nat, change)
    elif name == 'bridge_patch_not_revision_2':
        refinalize(nat, lambda run, rows: (run/'provenance/instrumentation.patch').write_text(overlay.source_record()[1]))
    # ---------------------------------------------------------------- history
    elif name == 'history_v4_run_removed': shutil.rmtree(v4/'l070-draw1')
    elif name == 'history_v4_seal_broken': (v4/'l070-draw1/unlisted-evidence.txt').write_text('added after the seal\n')
    elif name == 'history_v4_certificate_verdict_false':
        def change(run, rows):
            change_json(run, 'certificate-verdict.json', lambda v: v.__setitem__('accepted', False))
        reseal_history(v4/'l166-draw1', change)
    elif name == 'history_v4_guard_message_removed':
        def change(run, rows):
            for s in ('stdout', 'stderr'):
                p = run/'stages/reconstruct'/f'reconstruct.{s}'; p.write_text(p.read_text().replace(audit.GUARD, 'R6 proposal input accepted'))
        reseal_history(v4/'l099-draw1', change)
    elif name == 'history_v4_terminal_row_dropped':
        c4 = J(ROOT/'policies'/audit.HISTORY_V4['policy'])['campaign']['id']; drop_terminal_row(ledgers/c4/'rehearsal', c4, 'l170-draw1')
    elif name == 'history_v5_run_removed': shutil.rmtree(v5/'l070-draw1')
    elif name == 'history_v5_seal_broken': (v5/'l070-draw1/unlisted-evidence.txt').write_text('added after the seal\n')
    elif name == 'history_v5_consumption_receipt_synthesized':  # never: a receipt written into a v5 kernel success must reject
        def change(run, rows):
            index = max(i for i, r in enumerate(rows) if r['source'] == 'child_report')
            synthesized = json.loads(json.dumps(rows[index])); synthesized['event'] = 'reconstruction_finished'
            synthesized['payload']['data'] = {'certificate': J(run/'evidence.json')['certificate'], 'closer': 'term_mode_int', 'certificate_consumed': True,
                                              'derivation_replayed': False, 'residual_closer': 'omega'}
            rows.insert(index+1, synthesized)
        reseal_history(v5/'l096-draw1', change)
    elif name == 'history_v5_refusal_recategorized':
        reseal_history(v5/'l166-draw1', lambda run, rows: change_json(run, 'credential-summary.json', lambda v: v.__setitem__('failure_category', 'reconstruction_refused')))
    elif name == 'history_v5_terminal_row_dropped':
        c5 = J(ROOT/'policies'/audit.HISTORY_V5['policy'])['campaign']['id']; drop_terminal_row(ledgers/c5/'rehearsal', c5, 'l204-draw1')
    # ---------------------------------------------------------------- R6-013 review
    elif name in ('refused_dispatch_certificate', 'refused_dispatch_final_ir', 'refused_verification_started_certificate', 'refused_dispatch_trace', 'proof_dispatch_final_ir'):
        observation = 'certificate_verification_started' if name == 'refused_verification_started_certificate' else 'dispatch_received'
        key = {'refused_dispatch_final_ir': 'final_ir', 'proof_dispatch_final_ir': 'final_ir', 'refused_dispatch_trace': 'trace'}.get(name, 'certificate')
        def change(run, rows):
            data = child(rows, observation); assert data[key] != {'review_probe': 'different_evidence'}; data[key] = {'review_probe': 'different_evidence'}
        refinalize(root/(LAST if name.startswith('proof') else REF), change)
    elif name == 'refused_child_foreign_component':  # an observation inside the reconstruction window attributed to another component
        def change(run, rows):
            r = next(r for r in rows if r['source'] == 'child_report' and r['event'] == 'reification_started'); r['payload']['component'] = 'other_component'
        refinalize(root/REF, change)
    elif name in ('coherent_wrong_success_closer', 'coherent_wrong_refused_closer'):  # every closer mirror changed together; the IR is not
        target, old, new = (LAST, 'term_mode_int', 'term_mode_nat') if name == 'coherent_wrong_success_closer' else (REF, 'term_mode_nat', 'term_mode_int')
        def change(run, rows):
            for observed in ('closer_selected', 'reconstruction_finished'):
                if any(r['source'] == 'child_report' and r['event'] == observed for r in rows):
                    data = child(rows, observed); assert data['closer'] == old; data['closer'] = new
            if (run/'verdict.json').exists(): rebind_verdict(run, rows, lambda v: v.__setitem__('closer', new))
            if (run/'reconstruction-refusal.json').exists():
                change_json(run, 'reconstruction-refusal.json', lambda v: v.__setitem__('closer', new))
                receipt = event(rows, 'reconstruction_refused', 'reconstruct'); receipt.clear(); receipt.update(J(run/'reconstruction-refusal.json'))
        refinalize(root/target, change)
    elif name in ('refused_reconstruction_foreign_packet', 'certificate_check_foreign_packet', 'assembly_foreign_prepared_problem', 'preparation_foreign_input',
                  'pipeline_prepare_foreign_ir', 'validation_foreign_solution'):
        target, stage, guest, other = {
            'refused_reconstruction_foreign_packet': (REF, 'reconstruct', '/evidence.json', NAT),
            'certificate_check_foreign_packet': (LAST, 'certificate-check', '/evidence.json', NAT),
            'assembly_foreign_prepared_problem': (LAST, 'assembly', '/prepared.json', NAT),
            'preparation_foreign_input': (NAT, 'preparation-build', '/input', FIRST),
            'pipeline_prepare_foreign_ir': (IFACE, 'pipeline-prepare', '/input-ir.json', 'l101-draw1'),
            'validation_foreign_solution': (NAT, 'validation-local', '/solution.ndjson', FIRST)}[name]
        def change(run, rows):
            def command(v):
                a = v['argv']; i = a.index(guest)
                assert a[i-2] == '--ro-bind' and f'/{target}/' in a[i-1]; a[i-1] = a[i-1].replace(f'/{target}/', f'/{other}/')
            change_json(run, f'stages/{stage}/command.json', command)
        refinalize(root/target, change)
    elif name == 'export_target_altered':
        def change(run, rows):
            def command(v):
                a = v['argv']; i = a.index('--', a.index('Frozen')); assert a[i+1].startswith('Bracket.'); a[i+1] = 'Unrelated.theorem'
            change_json(run, 'stages/export/command.json', command)
        refinalize(nat, change)
    elif name in ('historical_wrong_kernel_target', 'history_v4_wrong_kernel_target'):
        base = v5 if name.startswith('historical') else v4; run_name = 'l096-draw1' if name.startswith('historical') else 'l070-draw1'
        def change(run, rows):
            def verdict(v):
                target = v['final_validation']['local']['targets'][0]; assert target['name'] != 'Unrelated.theorem'; target['name'] = 'Unrelated.theorem'
            rebind_verdict(run, rows, verdict)
        reseal_history(base/run_name, change)
    # ---------------------------------------------------------------- revision 2 review
    elif name in ('refused_reconstruction_helper_changed', 'proof_reconstruction_helper_changed'):
        def change(run, rows):
            p = run/'input/ProposalCapture.lean'; text = p.read_text(); old = 'evalTactic (← `(tactic| proof_broker_term [$adapter:ident]))'
            assert text.count(old) == 1; p.write_text(text.replace(old, 'evalTactic (← `(tactic| omega))'))
        refinalize(root/(REF if name.startswith('refused') else LAST), change)
    elif name == 'refused_reconstruction_source_changed':
        def change(run, rows):
            p = run/'input/Frozen.lean'; other = root/NAT/'input/Frozen.lean'; assert p.read_bytes() != other.read_bytes(); p.write_bytes(other.read_bytes())
        refinalize(root/REF, change)
    elif name in ('library_source_escapes_system_directory', 'library_pair_added_to_every_assembly'):
        stage, pair = (('reconstruct', ['--ro-bind', '/usr/lib/../../etc/hostname', '/usr/lib/review-extra-data']) if name.startswith('library_source')
                       else ('assembly', ['--ro-bind', '/usr/lib/libz.so.1', '/usr/lib/libz.so.1']))
        changed = 0
        for run in sorted(root.iterdir()):
            if not (run/'stages'/stage).is_dir(): continue
            def change(run, rows):
                def command(v):
                    argv = v['argv']; i = len(audit.SANDBOX) + (12 if stage == 'reconstruct' else 0)  # after the toolchain block, inside the library block
                    assert argv[i] == '--ro-bind' and argv[i+1].startswith('/usr/lib/'); argv[i:i] = pair
                change_json(run, f'stages/{stage}/command.json', command)
            refinalize(run, change); changed += 1
        assert changed >= 4
    elif name == 'library_pair_removed_in_one_run':
        def change(run, rows):
            def command(v):
                argv = v['argv']; i = argv.index('--ro-bind', len(audit.SANDBOX)); assert argv[i+1].startswith('/usr/lib/'); del argv[i:i+3]
            change_json(run, 'stages/certificate-check/command.json', command)
        refinalize(root/LAST, change)
    elif name == 'replay_challenge_unverified_location':  # characterized: must stay accepted
        def change(run, rows):
            for stage in ('validation-local', 'validation-whole'):
                def command(v):
                    argv = v['argv']; i = argv.index('/challenge.ndjson'); argv[i-1] = '/etc/r6-campaign-challenge-review/challenge.ndjson'
                change_json(run, f'stages/{stage}/command.json', command)
        refinalize(nat, change)
    elif name == 'challenge_path_inside_recorded_root':
        def change(run, rows):
            for stage in ('validation-local', 'validation-whole'):
                def command(v):
                    argv = v['argv']; i = argv.index('/challenge.ndjson')
                    argv[i-1] = v['run']+'/r6-campaign-challenge-inside/challenge.ndjson'
                change_json(run, f'stages/{stage}/command.json', command)
        refinalize(nat, change)
    else: raise AssertionError(name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--only', nargs='*', help='trial: run only these controls; the record requires the full population')
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    selected = [c for c in CONTROLS if not args.only or c in args.only or c == 'baseline']
    results = {}
    for name in selected:
        with tempfile.TemporaryDirectory(prefix='r6-013-controls-') as temp:
            temp = Path(temp)
            paths = {'runs': temp/'runs', 'ledgers': temp/'ledgers', 'representability': temp/'representability', 'v4': temp/'v4', 'v5': temp/'v5'}
            shutil.copytree(ROOT/audit.RUNS, paths['runs']); shutil.copytree(ROOT/'ledgers/campaigns', paths['ledgers'])
            shutil.copytree(ROOT/audit.REPRESENTABILITY, paths['representability'])
            shutil.copytree(ROOT/audit.HISTORY_V4['runs'], paths['v4']); shutil.copytree(ROOT/audit.HISTORY_V5['runs'], paths['v5'])
            baseline = run_audit(paths); assert baseline['accepted'] is True, baseline
            if name == 'baseline': results[name] = baseline; print(name, baseline, flush=True); continue
            if name == 'audit_case_removed':
                original = audit.Audit.require
                def omit(self, ok, case, detail=''):
                    if case == f'{NAT}:proof:shared_checker': return
                    return original(self, ok, case, detail)
                with patch.object(audit.Audit, 'require', omit): observed = run_audit(paths)
            else:
                mutate(name, paths); observed = run_audit(paths)
            assert observed['accepted'] is False and observed['rejected_case'] == EXPECTED[name], (name, observed)
            results[name] = {'rejected': True, 'rejected_case': observed['rejected_case']}
            print(name, observed['rejected_case'], flush=True)
    characterized = {}
    for name in CHARACTERIZED:
        with tempfile.TemporaryDirectory(prefix='r6-013-controls-') as temp:
            temp = Path(temp)
            paths = {'runs': temp/'runs', 'ledgers': temp/'ledgers', 'representability': temp/'representability', 'v4': temp/'v4', 'v5': temp/'v5'}
            shutil.copytree(ROOT/audit.RUNS, paths['runs']); shutil.copytree(ROOT/'ledgers/campaigns', paths['ledgers'])
            shutil.copytree(ROOT/audit.REPRESENTABILITY, paths['representability'])
            shutil.copytree(ROOT/audit.HISTORY_V4['runs'], paths['v4']); shutil.copytree(ROOT/audit.HISTORY_V5['runs'], paths['v5'])
            mutate(name, paths); observed = run_audit(paths)
            assert observed['accepted'] is True, (name, observed)  # the documented qualification: a path claim, not a content binding
            characterized[name] = {'accepted': True, 'reason': CHARACTERIZED[name]}; print(name, 'accepted (characterized)', flush=True)
    if args.only:
        print(json.dumps({'trial': True, 'controls': len(results)})); return
    assert tuple(results) == CONTROLS and set(results) == {'baseline', *EXPECTED}, sorted(results)
    record = {'passed': True, 'controls': len(results), 'expected_controls': list(CONTROLS), 'results': results, 'not_applicable': NOT_APPLICABLE,
              'review_probes': list(REVIEW_PROBES), 'baseline_cases': results['baseline']['case_count'], 'characterized': characterized,
              'runs': audit.RUNS, 'revision': audit.REVISION, 'auditor_sha256': r6.sha(Path(__file__).with_name('cohort_v6_audit.py')),
              'program_sha256': r6.sha(Path(__file__)), 'live_model_calls': 0, 'credentials_read': 0,
              'scope': 'temporary copies; one relationship per mutation; exact control population'}
    r6.write_json(args.output, record)
    print(json.dumps({'passed': True, 'controls': len(results), 'baseline_cases': results['baseline']['case_count']}, indent=1))


if __name__ == '__main__':
    main()
