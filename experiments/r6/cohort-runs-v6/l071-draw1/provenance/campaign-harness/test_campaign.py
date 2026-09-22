#!/usr/bin/env python3
"""R6-008 focused controls for the repaired guards. Canned; nothing connects.

Ledger semantics are exercised on temporary ledgers; the actor runs as a plain
subprocess against the loopback TLS fixture with a synthetic canary, so the
grant, the commitment, the classified credential failure and the permit checks
are observed on real records rather than asserted from source.
"""
import argparse
import copy
import json
import os
import shutil
import threading
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import types

import campaign_budget as budget
import campaign_contract as contract
import campaign_episode as driver
import campaign_https as actor
import campaign_ledger as ledger
import campaign_network as network
import credential
import episode
import events
import live_tls_fixture
import pricing_gate_v2 as gate
import run as r6
from test_proposals import Suite, rejected, require
from unittest.mock import patch

CASES = '''policy_frozen_disabled ledger_path_derived_from_policy_digest authorization_scope_one_function
ledger_activation_requires_signature ledger_one_transmission_across_runs ledger_release_only_established_termination
ledger_presend_attempt_limit ledger_ambiguous_outcome_consumed ledger_stale_counters_do_not_release
ledger_serializes_reservations ledger_money_ceiling ledger_refuses_recreation_and_truncation
ledger_directory_durability permit_reuse_refused grant_single_use grant_concurrent_single_winner
slot_marker_closes_reservation unreadable_grant_consumed activation_bound_to_policy_and_mode
signing_preserves_checkpoint_and_activates actor_credential_format_classified actor_grant_before_first_header_byte
actor_commitment_recorded actor_permit_verified_against_ledger actor_permit_replay_refused
actor_live_rejects_unsigned_policy actor_live_rejects_rehearsal_activation
interpretation_splits_local_send_from_remote_receipt network_stage_receipts_owned_by_supervisor
network_stage_isolation_switch attribution_passed_through finalize_seals_every_failure
interrupted_record_finalized_and_consumed lifecycle_pre_launch_failure_released lifecycle_non_object_records_consumed
lifecycle_reconciliation_failure_reported unreadable_records_are_evidence grant_short_write_completed
grant_partial_write_failure_consumed persistence_fault_sweep ledger_partial_append_recovered
marker_recovery_complete_and_torn finalize_requires_complete_evidence
live_publication_pending_not_accepted counters_separate
ca_bundle_pinned live_refuses_fixture rehearsal_requires_fixture endpoint_allowlist_exact'''.split()
PREPARED = r6.ROOT/'runs/provider-checkpoint-v1/d1_valid/prepared.json'


def signed_record(**overrides):
    record = {'approved_by': 'author', 'approved_utc': '2026-09-13T00:00:00Z', 'model_id': contract.MODEL,
              'maximum_transmissions': 1, 'maximum_micro_usd': contract.ATTEMPT_MICRO_USD,
              'maximum_presend_attempts': contract.MAXIMUM_PRESEND_ATTEMPTS, 'scope': 'one transmission'}
    record.update(overrides)
    return record


def signed(c, **overrides):
    return {**copy.deepcopy(c), 'live_enabled': True, 'authorization': signed_record(**overrides)}


def refused(fn, code):
    try: fn()
    except ledger.Failure as error:
        require(error.code == code, f'wrong code {error.code}, wanted {code}')
        return {'rejected': True, 'code': error.code}
    raise AssertionError('accepted: '+code)


def temp_ledger(directory, record=None, digest='a'*64, purpose='live'):
    book = ledger.Ledger(directory, digest)
    book.activate(record or signed_record(), purpose)
    return book


TERMINATED = {'exit_code': 1, 'workload_empty_after_cleanup': True, 'monitor_error': None, 'observation_error': None,
              'accounting_scope': 'sandbox_process_tree'}
SENT = {'body_sends_started': 1, 'header_sends_started': 1, 'send_outcome': 'returned'}
UNSENT = {'body_sends_started': 0, 'header_sends_started': 0}


def reservation_shape(): return {'reserved_micro_usd': 102400, 'message_utf8_bytes': 5000}
BIND = {'request_sha256': 'b'*64, 'arguments_sha256': 'c'*64}


def reserve(book, name): return book.reserve(name, reservation_shape(), BIND, {'accepted': True})[0]


def with_grant(book, permit):
    ledger.commit_grant(book.slot(permit['reservation_id']), ledger.grant_record(permit, 1))
    return book.slot(permit['reservation_id'])


def units(output):
    suite = Suite(output, CASES)
    c = contract.config()

    def frozen_disabled():
        require(c['live_enabled'] is False and c['authorization'] is None and c['live_model_calls_authorized'] == 0)
        live_book, rehearsal_book = contract.campaign_ledger(True), contract.campaign_ledger(False)
        require(not live_book.path.exists() and not live_book.head.exists(), 'live ledger exists before signing')
        require(rehearsal_book.path.exists() and rehearsal_book.snapshot()[1]['maximum_transmissions'] == 64)
        rejected(lambda: contract.live_permitted(c), 'campaign_live_disabled')
        return {'live_enabled': False, 'authorization': None, 'live_ledger_activated': False, 'rehearsal_ledger_activated': True}
    suite.case('policy_frozen_disabled', frozen_disabled)

    def ledger_path():
        book = contract.campaign_ledger(True)
        require(book.path.name == contract.policy_sha256()+'.ndjson' and book.path.parent == contract.LEDGERS/'live')
        require(contract.campaign_ledger(False).path.parent == contract.LEDGERS/'rehearsal')
        other = ledger.Ledger(contract.LEDGERS/'live', r6.hashlib.sha256(contract.CONFIG.read_bytes()+b' ').hexdigest())
        require(other.path != book.path and not other.path.exists())
        return {'live_ledger': str(book.path.relative_to(r6.ROOT)), 'derived_from': 'sha256 of the approved policy bytes',
                'rehearsal_ledger': str(contract.campaign_ledger(False).path.relative_to(r6.ROOT))}
    suite.case('ledger_path_derived_from_policy_digest', ledger_path)

    def scope():
        require(contract.authorization is not None and contract.authorization.__code__ is not None)
        probes = {'campaign_authorization_maximum_micro_usd': dict(maximum_micro_usd=0),
                  'campaign_authorization_approver': dict(approved_by=''),
                  'campaign_authorization_transmissions': dict(maximum_transmissions=2),
                  'campaign_authorization_subject': dict(model_id='gpt-5.4'),
                  'campaign_authorization_timestamp': dict(approved_utc='2026-09-13'),
                  'campaign_authorization_maximum_presend_attempts': dict(maximum_presend_attempts=0),
                  'campaign_authorization_money': dict(maximum_micro_usd=1)}
        seen = {}
        for code, overrides in probes.items():
            mutant = signed(c, **overrides)
            host = refused(lambda: contract.authorization(mutant), code)['code']
            inside = refused(lambda: ledger.authorization_scope(mutant), code)['code']
            require(host == inside == code); seen[code] = True
        absent = signed(c); del absent['authorization']['scope']
        refused(lambda: ledger.authorization_scope(absent), 'campaign_authorization_absent')
        extra = signed(c); extra['authorization']['note'] = 'x'
        refused(lambda: ledger.authorization_scope(extra), 'campaign_authorization_absent')
        require(ledger.authorization_scope(signed(c))['maximum_transmissions'] == 1)
        return {'host_and_actor_share': 'campaign_ledger.authorization_scope', 'rejections': sorted(seen)}
    suite.case('authorization_scope_one_function', scope)

    def activation():
        with tempfile.TemporaryDirectory() as d:
            book = ledger.Ledger(d, 'f'*64)
            refused(lambda: book.reserve('run-a', reservation_shape(), BIND, {}), 'campaign_ledger_not_activated')
            refused(lambda: book.snapshot(), 'campaign_ledger_not_activated')
            require(not book.path.exists(), 'a refused reservation created a ledger')
            book.activate(signed_record(), 'live')
            refused(lambda: book.activate(signed_record(), 'live'), 'campaign_ledger_already_activated')
            refused(lambda: ledger.Ledger(d, 'e'*64).activate(signed_record(), 'test'), 'campaign_activation_purpose')
        return {'unactivated_digest_has_no_authority': True, 'activation_once': True, 'purpose_required': True}
    suite.case('ledger_activation_requires_signature', activation)

    def across_runs():
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d)
            permit = reserve(book, 'run-a')
            row, _ = book.reconcile(permit, TERMINATED, SENT, {})
            require(row['kind'] == 'unknown', 'a send without a grant is not a transmission')  # counters cannot claim a send
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d)
            permit = reserve(book, 'run-a'); with_grant(book, permit)
            row, _ = book.reconcile(permit, TERMINATED, SENT, {})
            require(row['kind'] == 'send_grant' and row['send_outcome'] == 'returned')
            refused(lambda: book.reserve('run-b', reservation_shape(), BIND, {}), 'campaign_transmissions_exhausted')
            _, s = book.snapshot()
        return {'runs': ['run-a', 'run-b'], 'second_run_refused': 'campaign_transmissions_exhausted', 'state': {k: s[k] for k in ('transmissions_consumed', 'reservations')}}
    suite.case('ledger_one_transmission_across_runs', across_runs)

    def release():
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d)
            permit = reserve(book, 'run-a')
            row, _ = book.reconcile(permit, TERMINATED, {**UNSENT, 'failure_category': 'credential_format'}, {'process_sha256': 'x'})
            require(row['kind'] == 'release' and row['failure_category'] == 'credential_format' and row['termination_established'] is True)
            require((book.slot(permit['reservation_id'])/'release.json').exists())
            again = reserve(book, 'run-b')
            _, s = book.snapshot()
            require(s['presend_attempts_used'] == 1 and s['transmissions_consumed'] == 0 and s['open_reservations'] == [again['reservation_id']])
        outcomes = {}
        for label, process in [('empty_record', {}), ('workload_still_alive', {**TERMINATED, 'workload_empty_after_cleanup': False}),
                               ('monitor_error', {**TERMINATED, 'monitor_error': 'lost'}), ('observation_error', {**TERMINATED, 'observation_error': 'x'}),
                               ('exit_code_only', {'exit_code': 1}), ('no_record', None)]:
            with tempfile.TemporaryDirectory() as d:
                book = temp_ledger(d); permit = reserve(book, 'run-a')
                row, _ = book.reconcile(permit, process, UNSENT, {})
                require(row['kind'] == 'unknown' and row['termination_established'] is False, label)
                refused(lambda: book.reserve('run-b', reservation_shape(), BIND, {}), 'campaign_transmissions_exhausted')
                outcomes[label] = 'unknown, consumed'
        return {'established_termination': 'released', **outcomes}
    suite.case('ledger_release_only_established_termination', release)

    def presend_limit():
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d, signed_record(maximum_presend_attempts=2))
            for i in range(2):
                permit = reserve(book, f'run-{i}'); book.reconcile(permit, TERMINATED, UNSENT, {})
            refused(lambda: book.reserve('run-2', reservation_shape(), BIND, {}), 'campaign_presend_attempts_exhausted')
        return {'maximum_presend_attempts': 2, 'third_refused': True}
    suite.case('ledger_presend_attempt_limit', presend_limit)

    def ambiguous():
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d); permit = reserve(book, 'run-a')
            row, _ = book.reconcile(permit, None, None, {})
            require(row['kind'] == 'unknown' and (book.slot(permit['reservation_id'])/'unknown.json').exists())
            refused(lambda: book.reserve('run-b', reservation_shape(), BIND, {}), 'campaign_transmissions_exhausted')
            _, s = book.snapshot(); require(s['unknown_outcomes'] == 1 and s['committed_micro_usd'] == 102400)
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d); permit = reserve(book, 'run-a')
            row, _ = book.reconcile(permit, TERMINATED, SENT, {})
            require(row['kind'] == 'unknown')
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d); permit = reserve(book, 'run-a')
            row, _ = book.reconcile(permit, TERMINATED, None, {})
            require(row['kind'] == 'release' and row['transport_record_present'] is False)
        return {'no_process_record': 'unknown, consumed', 'counters_without_grant': 'unknown, consumed', 'terminated_without_transport_record': 'released'}
    suite.case('ledger_ambiguous_outcome_consumed', ambiguous)

    def stale():
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d); permit = reserve(book, 'run-a'); with_grant(book, permit)
            row, _ = book.reconcile(permit, {**TERMINATED, 'exit_code': 137}, UNSENT, {})
            require(row['kind'] == 'send_grant' and row['send_outcome'] == 'unknown')
            refused(lambda: book.reserve('run-b', reservation_shape(), BIND, {}), 'campaign_transmissions_exhausted')
        return {'grant_with_stale_zero_counters': 'send_grant / send_outcome unknown; consumed'}
    suite.case('ledger_stale_counters_do_not_release', stale)

    def serialized():
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d, signed_record(maximum_transmissions=3, maximum_micro_usd=400000))
            reserve(book, 'run-a')
            refused(lambda: book.reserve('run-b', reservation_shape(), BIND, {}), 'campaign_reservation_open')
        return {'open_reservation_blocks_second': True}
    suite.case('ledger_serializes_reservations', serialized)

    def money():
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d, signed_record(maximum_transmissions=2, maximum_micro_usd=102400))
            permit = reserve(book, 'run-a'); with_grant(book, permit); book.reconcile(permit, TERMINATED, SENT, {})
            refused(lambda: book.reserve('run-b', reservation_shape(), BIND, {}), 'campaign_money_exhausted')
        return {'slot_available_but_money_exhausted': True}
    suite.case('ledger_money_ceiling', money)

    def recreation():
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d); reserve(book, 'run-a')
            raw = book.path.read_bytes()
            book.path.write_bytes(raw.splitlines(True)[0])
            refused(lambda: book.snapshot(), 'campaign_ledger_truncated')
            book.path.write_bytes(raw.replace(b'"run-a"', b'"run-x"', 1))
            refused(lambda: book.snapshot(), 'campaign_ledger_chain')
            book.path.unlink()
            refused(lambda: book.snapshot(), 'campaign_ledger_missing_after_activation')
            refused(lambda: book.reserve('run-b', reservation_shape(), BIND, {}), 'campaign_ledger_missing_after_activation')
            require(not book.path.exists(), 'a refused operation recreated the ledger')
        return {'truncated': 'refused', 'tampered': 'refused', 'missing_after_activation': 'refused, not recreated'}
    suite.case('ledger_refuses_recreation_and_truncation', recreation)

    def durability():
        calls = []
        original = ledger.fsync_directory
        with tempfile.TemporaryDirectory() as d, patch.object(ledger, 'fsync_directory', lambda path: (calls.append(Path(path).name), original(path))[1]):
            book = temp_ledger(d); after_activation = list(calls)
            permit = reserve(book, 'run-a'); after_reserve = list(calls)
            with_grant(book, permit); after_grant = list(calls)
            book.reconcile(permit, TERMINATED, SENT, {})
        base = Path(d).name
        require(base in after_activation, 'activation does not fsync the ledger directory')
        require(len([c for c in after_reserve if c == base]) > len([c for c in after_activation if c == base]), 'reservation append/head does not fsync the directory')
        require(any(c == permit['reservation_id'] for c in after_grant[len(after_reserve):]), 'grant does not fsync its slot directory')
        require(len(calls) > len(after_grant), 'reconciliation does not fsync')
        return {'directory_fsync': ['activation', 'reservation', 'head replacement', 'grant slot', 'reconciliation'],
                'scope': 'fsync calls observed; power loss not simulated'}
    suite.case('ledger_directory_durability', durability)

    def reuse():
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d, signed_record(maximum_transmissions=2, maximum_micro_usd=400000))
            permit = reserve(book, 'run-a'); pol = signed(c, maximum_transmissions=2, maximum_micro_usd=400000)
            pol['limits'] = {**pol['limits'], 'maximum_transmissions': 2, 'total_micro_usd': 400000}
            raw_open = book.path.read_bytes()
            require(ledger.verify_permit(permit, raw_open, 'a'*64, 'run-a', pol, True)['open_reservations'] == [permit['reservation_id']])
            refused(lambda: ledger.verify_permit(permit, raw_open, 'a'*64, 'run-b', pol, True), 'campaign_permit_binding')
            refused(lambda: ledger.verify_permit(permit, raw_open, 'e'*64, 'run-a', pol, True), 'campaign_ledger_policy_mismatch')
            with_grant(book, permit); _, raw_after = book.reconcile(permit, TERMINATED, SENT, {})
            refused(lambda: ledger.verify_permit(permit, raw_after, 'a'*64, 'run-a', pol, True), 'campaign_permit_not_last_row')
            refused(lambda: book.reconcile(permit, TERMINATED, SENT, {}), 'campaign_reservation_not_open')
            refused(lambda: ledger.slot_open(book.slot(permit['reservation_id'])), 'campaign_grant_slot_used')
        return {'used_permit_refused': 'campaign_permit_not_last_row', 'second_reconcile_refused': 'campaign_reservation_not_open', 'slot_closed': True}
    suite.case('permit_reuse_refused', reuse)

    def grant_once():
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d); permit = reserve(book, 'run-a'); slot = with_grant(book, permit)
            refused(lambda: ledger.commit_grant(slot, ledger.grant_record(permit, 2)), 'campaign_grant_slot_used')
            require(ledger.read_grant(slot, permit)['reservation_id'] == permit['reservation_id'])
            refused(lambda: ledger.read_grant(slot, {**permit, 'reservation_id': 'other'}), 'campaign_grant_binding')
            refused(lambda: ledger.slot_open(Path(d)/'nonexistent'), 'campaign_grant_slot_missing')
            require(not any(p.name.endswith('.tmp') for p in slot.iterdir()))
        return {'single_use': True, 'bound_to_reservation': True, 'missing_slot_refused': True}
    suite.case('grant_single_use', grant_once)

    def concurrent():
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d); permit = reserve(book, 'run-a'); slot = book.slot(permit['reservation_id'])
            barrier = threading.Barrier(2); results = {}
            original_open = ledger.slot_open
            def gated(directory):  # both callers observe an open slot before either creates
                original_open(directory); barrier.wait(timeout=10)
            def worker(name):
                try:
                    g = ledger.grant_record(permit, 1); ledger.commit_grant(slot, g)
                    results[name] = ('accepted', g['grant_id'])
                except ledger.Failure as error: results[name] = ('refused', error.code)
            threads = [threading.Thread(target=worker, args=(n,), name=n) for n in ('first', 'second')]
            with patch.object(ledger, 'slot_open', gated):  # patched once, from this thread, around both racers
                for t in threads: t.start()
                for t in threads: t.join(15)
            require(all(not t.is_alive() for t in threads))
            accepted = [v for v in results.values() if v[0] == 'accepted']; refused_ = [v for v in results.values() if v[0] == 'refused']
            require(len(accepted) == 1 and len(refused_) == 1 and refused_[0][1] == 'campaign_grant_slot_used')
            require(ledger.read_grant(slot, permit)['grant_id'] == accepted[0][1], 'retained grant is not the winner')
        return {'racing_writers': 2, 'grants': 1, 'loser': 'campaign_grant_slot_used', 'mechanism': 'O_EXCL on the final name'}
    suite.case('grant_concurrent_single_winner', concurrent)

    def markers():
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d, signed_record(maximum_transmissions=2, maximum_micro_usd=400000, maximum_presend_attempts=2))
            permit = reserve(book, 'run-a'); row, _ = book.reconcile(permit, TERMINATED, UNSENT, {})
            slot = book.slot(permit['reservation_id'])
            require(r6.read_json(slot/'release.json')['kind'] == 'release' and row['marker_sha256'] == r6.sha(slot/'release.json'))
            refused(lambda: ledger.slot_open(slot), 'campaign_grant_slot_used')
            refused(lambda: ledger.commit_grant(slot, ledger.grant_record(permit, 1)), 'campaign_grant_slot_used')
            permit2 = reserve(book, 'run-b'); book.reconcile(permit2, None, None, {})
            refused(lambda: ledger.slot_open(book.slot(permit2['reservation_id'])), 'campaign_grant_slot_used')
        return {'released_slot': 'closed by release.json', 'unknown_slot': 'closed by unknown.json', 'replay_after_release': 'refused'}
    suite.case('slot_marker_closes_reservation', markers)

    def unreadable():
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d); permit = reserve(book, 'run-a')
            (book.slot(permit['reservation_id'])/ledger.GRANT_FILE).write_bytes(b'{')
            row, _ = book.reconcile(permit, TERMINATED, UNSENT, {})
            require(row['kind'] == 'unknown' and row['grant_state'] == 'campaign_grant_unreadable')
            refused(lambda: book.reserve('run-b', reservation_shape(), BIND, {}), 'campaign_transmissions_exhausted')
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d); permit = reserve(book, 'run-a')
            ledger.commit_grant(book.slot(permit['reservation_id']), ledger.grant_record({**permit, 'reservation_id': 'other'}, 1))
            row, _ = book.reconcile(permit, TERMINATED, UNSENT, {})
            require(row['kind'] == 'unknown' and row['grant_state'] == 'campaign_grant_binding')
        return {'truncated_grant': 'unknown, consumed', 'foreign_grant': 'unknown, consumed'}
    suite.case('unreadable_grant_consumed', unreadable)

    def bound_activation():
        live_policy = signed(c)
        with tempfile.TemporaryDirectory() as d:
            rehearsal = ledger.Ledger(Path(d)/'r', 'a'*64); rehearsal.activate(contract.REHEARSAL_AUTHORIZATION, 'rehearsal')
            permit = reserve(rehearsal, 'run-a'); raw = rehearsal.path.read_bytes()
            refused(lambda: ledger.verify_permit(permit, raw, 'a'*64, 'run-a', live_policy, True), 'campaign_activation_purpose')
            require(ledger.verify_permit(permit, raw, 'a'*64, 'run-a', c, False)['purpose'] == 'rehearsal')
            other = ledger.Ledger(Path(d)/'o', 'a'*64); other.activate(signed_record(approved_by='someone else'), 'live')
            permit2 = reserve(other, 'run-a'); raw2 = other.path.read_bytes()
            refused(lambda: ledger.verify_permit(permit2, raw2, 'a'*64, 'run-a', live_policy, True), 'campaign_activation_authorization')
            mine = ledger.Ledger(Path(d)/'m', 'a'*64); mine.activate(live_policy['authorization'], 'live')
            permit3 = reserve(mine, 'run-a'); raw3 = mine.path.read_bytes()
            require(ledger.verify_permit(permit3, raw3, 'a'*64, 'run-a', live_policy, True)['purpose'] == 'live')
            refused(lambda: ledger.verify_permit(permit3, raw3, 'a'*64, 'run-a', c, False), 'campaign_activation_purpose')
            refused(lambda: ledger.check_activation(ledger.state(ledger.parse(raw3), 'a'*64), signed(c, approved_utc='2026-09-14T00:00:00Z'), True),
                    'campaign_activation_authorization')
        return {'rehearsal_activation_under_live_policy': 'campaign_activation_purpose', 'foreign_approver': 'campaign_activation_authorization',
                'live_activation_under_rehearsal_mode': 'campaign_activation_purpose', 'binding': 'purpose + exact authorization record + limits'}
    suite.case('activation_bound_to_policy_and_mode', bound_activation)

    def signing():
        with tempfile.TemporaryDirectory() as d:
            policies = Path(d)/'policies'; policies.mkdir(); ledgers = Path(d)/'ledgers'
            cfg = policies/contract.CONFIG.name; cfg.write_bytes(contract.CONFIG.read_bytes())
            checkpoint = policies/contract.CHECKPOINT.name
            with patch.object(contract, 'CONFIG', cfg), patch.object(contract, 'CHECKPOINT', checkpoint), patch.object(contract, 'LEDGERS', ledgers):
                before = r6.sha(cfg)
                digest = contract.sign('author', '2026-09-13T00:00:00Z')
                signed_policy = contract.config()
                require(checkpoint.read_bytes() == contract.CONFIG.read_bytes() if False else checkpoint.exists() and r6.sha(checkpoint) == before)
                require(signed_policy['live_enabled'] is True and signed_policy['signed_from_checkpoint_sha256'] == before and digest != before)
                record, state = contract.live_permitted(signed_policy)
                require(state['purpose'] == 'live' and state['authorization'] == record and state['maximum_transmissions'] == 1)
                require(contract.campaign_ledger(False).snapshot()[1]['purpose'] == 'rehearsal')
                rejected(lambda: contract.sign('author', '2026-09-13T00:00:00Z'), 'already signed')
                # a rehearsal activation put in the live ledger's place is refused by the host as well
                live_book = contract.campaign_ledger(True)
                live_book.path.unlink(); live_book.head.unlink()
                ledger.Ledger(live_book.directory, digest).activate(contract.REHEARSAL_AUTHORIZATION, 'rehearsal')
                rejected(lambda: contract.live_permitted(signed_policy), 'campaign_activation_purpose')
        require(contract.config()['live_enabled'] is False, 'the real policy was touched')
        return {'checkpoint_retained': True, 'signed_digest_differs': True, 'live_ledger_activated_at_signing': True, 'host_checks_activation': True}
    suite.case('signing_preserves_checkpoint_and_activates', signing)

    # --- the actor as a plain subprocess against the loopback fixture ---
    task = r6.get_task('verinf-d1-70')
    prepared = r6.read_json(PREPARED)

    def actor_run(directory, *, credential_text=None, mode='rehearsal', policy_path=None, book=None, permit=None, ledger_path=None,
                  activation=None, purpose=None):
        """The real actor as a subprocess. `book`/`permit` reuse an existing reservation (replay); otherwise a fresh temp ledger."""
        d = Path(directory); run = d/'run'; run.mkdir(exist_ok=True)
        policy_bytes = (policy_path or contract.CONFIG).read_bytes(); policy_digest = r6.hashlib.sha256(policy_bytes).hexdigest()
        policy_value = json.loads(policy_bytes)
        request = budget.request(task, prepared); arguments = budget.arguments(request)
        if policy_path is not None:
            request = json.loads(request); request['policy_sha256'] = policy_digest; request = events.canonical(request)+b'\n'
            arguments = budget.arguments(request)
        (d/'request.json').write_bytes(request); r6.write_json(d/'arguments.json', arguments)
        if book is None:
            admitted = gate.admission(policy_value, contract.SOURCES, arguments, request, time.time())
            book = ledger.Ledger(d/'ledger', policy_digest)
            purpose = purpose or ('live' if mode == 'live' else 'rehearsal')
            if activation is None:
                activation = contract.REHEARSAL_AUTHORIZATION if purpose == 'rehearsal' else (policy_value.get('authorization') or signed_record())
            book.activate(activation, purpose)
            bindings = {'request_sha256': gate.sha(request), 'arguments_sha256': gate.sha(gate.canonical(arguments))}
            permit, _ = book.reserve('probe', budget.reservation(arguments), bindings, admitted)
        r6.write_json(d/'permit.json', permit)
        out = d/'out'; out.mkdir(exist_ok=True); grant = book.slot(permit['reservation_id'])
        nonce = credential.nonce(); canary = credential.derive(nonce)
        cred = d/'credential'; cred.write_text(credential.header(canary)+'\n' if credential_text is None else credential_text)
        base_args = ['--mode', mode, '--policy', str(policy_path or contract.CONFIG), '--arguments', str(d/'arguments.json'),
                     '--credential-file', str(cred), '--out', str(out), '--sources', str(contract.SOURCES),
                     '--permit', str(d/'permit.json'), '--ledger', str(ledger_path or book.path), '--request', str(d/'request.json'),
                     '--episode', 'probe', '--grant', str(grant), '--commitment-nonce', nonce]
        if mode == 'rehearsal':
            fixture = driver.canned(task, request); r6.write_json(d/'fixture.json', fixture)
            with live_tls_fixture.materialize(run, 'valid') as (ca, cert, key):
                proc = subprocess.run([sys.executable, '-I', '-S', '-B', str(r6.ROOT/'campaign_https.py'), *base_args, '--ca', str(ca),
                                       '--fixture', str(d/'fixture.json'), '--server-cert', str(cert), '--server-key', str(key)],
                                      capture_output=True, text=True, timeout=120)
        else:
            ca, _ = contract.bundle()
            proc = subprocess.run([sys.executable, '-I', '-S', '-B', str(r6.ROOT/'campaign_https.py'), *base_args, '--ca', str(ca)],
                                  capture_output=True, text=True, timeout=120)
        require(proc.returncode == 0, 'actor crashed: '+proc.stderr[-800:])
        return types.SimpleNamespace(http=r6.read_json(out/'http.json'), out=out, grant=grant, canary=canary, nonce=nonce,
                                     request=request, book=book, permit=permit)

    def credential_format():
        with tempfile.TemporaryDirectory() as d:
            r = actor_run(d, credential_text='sk-no-bearer-prefix\n'); http = r.http
            require(http['failure_category'] == 'credential_format' and http['connection_attempts'] == 0
                    and http['grant_committed'] is False and http['send_outcome'] == 'not_started')
            require((r.out/'pricing-check.json').exists() and r6.read_json(r.out/'pricing-check.json')['accepted'] is True)
            require(not (r.grant/ledger.GRANT_FILE).exists())
            text = (r.out/'http.json').read_text(); require('sk-no-bearer' not in text and 'Bearer' not in text)
        return {'classified': 'credential_format', 'connections': 0, 'grant': None, 'traceback': False}
    suite.case('actor_credential_format_classified', credential_format)

    def grant_order():
        with tempfile.TemporaryDirectory() as d:
            r = actor_run(d); http = r.http
            record = ledger.read_grant(r.grant, r.permit)
            require(http['grant_committed'] is True and http['grant_id'] == record['grant_id'])
            require(http['tls_verified_at_ns'] < record['at_ns'] == http['grant_created_at_ns'] < http['grant_durable_at_ns'] < http['header_send_at_ns'],
                    'grant creation and durable completion are not both between certificate verification and the first header byte')
            require(http['send_outcome'] == 'returned' and http['http_status'] == 200 and http['body_sends_returned'] == 1)
            server = r6.read_json(r.out/'server.json')
            require(len(server['requests']) == 1 and server['requests'][0]['body_sha256'] == gate.sha((r.out/'serialized-body.json').read_bytes()))
            require((r.out/'outbound-body.json').read_bytes() == (r.out/'serialized-body.json').read_bytes() == (r.out/'received-body.json').read_bytes())
            require(r.grant.parent.name.endswith('.slots'), 'grant slot is not the authoritative slot beside the ledger')
        return {'order': 'tls_verified < grant created < grant durable < header_send', 'send_outcome': 'returned', 'slot': 'authoritative'}
    suite.case('actor_grant_before_first_header_byte', grant_order)

    def commitment():
        with tempfile.TemporaryDirectory() as d:
            r = actor_run(d); http = r.http
            expected = actor.commitment(r.nonce, credential.header(r.canary))
            require(http['credential_commitment_sha256'] == expected and http['commitment_nonce'] == r.nonce)
            require(r.canary not in (r.out/'http.json').read_text() and r.canary not in (r.out/'server.json').read_text())
            require(r6.read_json(r.out/'server.json')['requests'][0]['authorization_sha256'] == credential.commitment(r.canary))
        return {'commitment': 'sha256(domain:nonce:header)', 'value_absent_from_records': True}
    suite.case('actor_commitment_recorded', commitment)

    def permit_checked():
        with tempfile.TemporaryDirectory() as d:
            first = actor_run(d); require(first.http['http_status'] == 200)
            first.book.reconcile(first.permit, TERMINATED, first.http, {})
            second = Path(d)/'second'; second.mkdir()
            r = actor_run(second, book=first.book, permit=first.permit)  # authoritative ledger now records consumption
            require(r.http['failure_category'] == 'campaign_ledger' and r.http['ledger_failure_code'] == 'campaign_permit_not_last_row'
                    and r.http['connection_attempts'] == 0)
        return {'consumed_permit_against_authoritative_ledger': 'campaign_permit_not_last_row', 'connections': 0}
    suite.case('actor_permit_verified_against_ledger', permit_checked)

    def replay():
        """The review's loopback replay: same permit, old snapshot, fresh run directory. Now the slot refuses."""
        with tempfile.TemporaryDirectory() as d:
            first = actor_run(d); require(first.http['http_status'] == 200 and first.http['grant_committed'] is True)
            snapshot = Path(d)/'snapshot.ndjson'; snapshot.write_bytes(first.book.path.read_bytes()[:0] or b'')
            # snapshot as the actor saw it before its own grant: the ledger file is unchanged until reconciliation
            snapshot.write_bytes(first.book.path.read_bytes())
            second = Path(d)/'second'; second.mkdir()
            r = actor_run(second, book=first.book, permit=first.permit, ledger_path=snapshot)
            require(r.http['failure_category'] == 'campaign_ledger' and r.http['ledger_failure_code'] == 'campaign_grant_slot_used'
                    and r.http['connection_attempts'] == 0 and r.http['grant_committed'] is False)
            server = r6.read_json(r.out/'server.json'); require(server['requests'] == [])
            first.book.reconcile(first.permit, TERMINATED, first.http, {})
            third = Path(d)/'third'; third.mkdir()
            r2 = actor_run(third, book=first.book, permit=first.permit, ledger_path=snapshot)
            require(r2.http['ledger_failure_code'] == 'campaign_grant_slot_used' and r2.http['connection_attempts'] == 0)
            _, s = first.book.snapshot(); require(s['transmissions_consumed'] == 1)
        return {'before_reconciliation': 'campaign_grant_slot_used', 'after_reconciliation': 'campaign_grant_slot_used', 'receiver_requests_total': 1,
                'shared_ledger_consumed': 1}
    suite.case('actor_permit_replay_refused', replay)

    def live_unsigned():
        with tempfile.TemporaryDirectory() as d:
            r = actor_run(d, mode='live')
            require(r.http['failure_category'] == 'authorization' and r.http['ledger_failure_code'] == 'campaign_live_disabled'
                    and r.http['connection_attempts'] == 0 and r.http['authorization_present_in_policy'] is None)
            unsigned = signed(c, maximum_micro_usd=0); p = Path(d)/'policy.json'; p.write_bytes(gate.canonical(unsigned)+b'\n')
            second = Path(d)/'second'; second.mkdir()
            r2 = actor_run(second, mode='live', policy_path=p, activation=signed_record())
            require(r2.http['failure_category'] == 'authorization' and r2.http['ledger_failure_code'] == 'campaign_authorization_maximum_micro_usd')
        return {'disabled_policy': 'campaign_live_disabled', 'zero_money_signed_policy': 'campaign_authorization_maximum_micro_usd', 'connections': 0}
    suite.case('actor_live_rejects_unsigned_policy', live_unsigned)

    def live_rehearsal_activation():
        """The review's substitution: a synthetic live policy with a rehearsal activation for the same bytes."""
        with tempfile.TemporaryDirectory() as d:
            live_policy = signed(c); p = Path(d)/'policy.json'; p.write_bytes(gate.canonical(live_policy)+b'\n')
            r = actor_run(d, mode='live', policy_path=p, activation=contract.REHEARSAL_AUTHORIZATION, purpose='rehearsal')
            require(r.http['failure_category'] == 'campaign_ledger' and r.http['ledger_failure_code'] == 'campaign_activation_purpose'
                    and r.http['connection_attempts'] == 0 and r.http['authorization_present_in_policy'] is True
                    and r.http['credential_commitment_sha256'] is None and not (r.out/'pricing-check.json').exists())
            second = Path(d)/'second'; second.mkdir()
            r2 = actor_run(second, mode='live', policy_path=p, activation=signed_record(approved_by='someone else'), purpose='live')
            require(r2.http['ledger_failure_code'] == 'campaign_activation_authorization' and r2.http['connection_attempts'] == 0)
        return {'rehearsal_activation': 'campaign_activation_purpose', 'foreign_authorization': 'campaign_activation_authorization',
                'stopped_before': 'pricing check and credential read', 'connections': 0}
    suite.case('actor_live_rejects_rehearsal_activation', live_rehearsal_activation)

    def split():
        with tempfile.TemporaryDirectory() as d:
            r = actor_run(d); out, request = r.out, r.request
            _, _, _, validation, error = budget.interpret(out, request, False)
            require(error is None and validation['local_send_consistency']['accepted'] is True and validation['remote_receipt']['accepted'] is True)
            (out/'outbound-body.json').write_bytes((out/'outbound-body.json').read_bytes()+b' ')
            _, _, _, validation, error = budget.interpret(out, request, True)
            require(error is not None and error.category == 'transport_capture_failure' and validation['local_send_consistency']['accepted'] is False
                    and validation['remote_receipt']['checked'] is True)
            (out/'received-body.json').unlink()
            _, _, _, validation, error = budget.interpret(out, request, True)
            require(validation['remote_receipt']['checked'] is False and validation['remote_receipt']['accepted'] is None
                    and validation['local_send_consistency']['accepted'] is False and error.category == 'transport_capture_failure')
        return {'local_send_checked_without_receiver': True, 'remote_receipt_unobservable_recorded_as_none': True}
    suite.case('interpretation_splits_local_send_from_remote_receipt', split)

    def receipts():
        source = (r6.ROOT/'campaign_network.py').read_text()
        require("'stage_started'" not in source and "'stage_finished'" not in source, 'network stage appends its own receipts')
        require('supervise.py' in source)
        return {'receipt_owner': 'supervise.py', 'network_stage_appends': 0}
    suite.case('network_stage_receipts_owned_by_supervisor', receipts)

    def isolation():
        run = Path(tempfile.mkdtemp())/'run'; (run/'stages/x').mkdir(parents=True)
        probe = Path(sys.executable)
        shared, _ = network.command(run, 'x', probe, [], [], run/'grant', shared_network=True, wall=1, cpu=1, memory=1, output_limit=1)
        isolated, spec = network.command(run, 'x', probe, [], [], run/'grant', shared_network=False, wall=1, cpu=1, memory=1, output_limit=1)
        require('--unshare-net' not in shared and network.RESOLVER in shared)
        require('--unshare-net' in isolated and network.RESOLVER not in isolated and spec['network_namespace'] == 'unshared')
        for cmd in (shared, isolated):
            i = cmd.index('/grant'); require(cmd[i-2] == '--bind' and cmd[i-1] == str(run/'grant'))
            require(all(ns in cmd for ns in network.NAMESPACES) and '--cap-drop' in cmd and '--clearenv' in cmd)
        return {'rehearsal': 'unshare-net kept', 'live': 'network shared, resolver mounted', 'grant_slot': 'writable bind in both'}
    suite.case('network_stage_isolation_switch', isolation)

    def attribution():
        source = (r6.ROOT/'campaign_episode.py').read_text()
        body = source[source.index('def consume('):source.index('def finalize(')]
        require("'canned_provider_response'" not in body and "'live_model_response'" not in body, 'consumer hardcodes a proposer')
        require(c['attribution']['witness_proposer'] == 'live_model_response' and c['attribution']['rehearsal_witness_proposer'] == 'canned_provider_response')
        return {'consumer_parameters': ['proposer', 'route'], 'policy_attribution': c['attribution']}
    suite.case('attribution_passed_through', attribution)

    def finalize_failure():
        with tempfile.TemporaryDirectory() as d:
            run = Path(d)/'run'; run.mkdir(); nonce = credential.nonce()
            events.append(run, 'episode', 'episode_started', {'probe': True}, task_id=task.id)
            events.append(run, 'preparation', 'stage_failure_recorded', {'category': 'stage_rejected', 'stage': 'preparation'})
            summary = {'proof_accepted': False, 'credential_use_accepted': False, 'ledger_reconciled': True, 'evidence_complete': True, 'failure_category': 'stage_rejected'}
            r6.write_json(run/'credential-summary.json', summary)
            accepted, report, final = driver.finalize(run, credential.derive(nonce), nonce, summary, False)
            rows = events.read(run/'events.ndjson'); seal = r6.read_json(run/'seal.json')
            require(accepted is False and rows[-1]['event'] == 'episode_rejected' and seal['accepted'] is False
                    and seal['event_count'] == len(rows) and report['accepted'] is True and final['report_clean'] is True)
            require(all(r6.sha(run/k) == v for k, v in seal['retained_sha256'].items()))
            source = (r6.ROOT/'campaign_episode.py').read_text()
            body = source[source.index('def execute('):source.index('def main(')]
            require('except episode.StageFailure' in body and body.index('except episode.StageFailure') < body.index('finalize('))
        return {'failed_run': 'scanned, terminated, sealed', 'execute_catches_stage_failure_before_finalize': True}
    suite.case('finalize_seals_every_failure', finalize_failure)

    def production(stage_double=None, copy_failure=False, reconcile_failure=False, patches=None):
        """Production execute/invoke/reconcile/finalize with doubles for setup, preparation and the stage launcher.
        `patches(ctx)` may return extra (target, attribute, replacement) triples for fault injection."""
        with tempfile.TemporaryDirectory() as d:
            d = Path(d); run = d/'run'; run.mkdir()
            book = ledger.Ledger(d/'ledgers/rehearsal', contract.policy_sha256()); book.activate(contract.REHEARSAL_AUTHORIZATION, 'rehearsal')
            tools = {'expected': r6.frozen_task(task)[1], 'runtime': {'stdlib': '/probe', 'extension_binaries': []}, 'runtime_path': d, 'python': Path(sys.executable)}
            def prepare_double(run, task, tools):
                request = budget.request(task, prepared)
                (run/'live-request.json').write_bytes(request); r6.write_json(run/'live-arguments.json', budget.arguments(request)); return request
            def default_stage(run, name, binary, argv, mounts, grant, **kwargs):
                raise episode.StageFailure('proposal-1', 'stage_rejected', 'synthetic')
            real_copy = shutil.copytree
            def copy(source, destination, *args, **kwargs):
                if copy_failure and Path(destination) == run/'transport-pricing-sources': raise PermissionError('synthetic copy failure after reservation')
                return real_copy(source, destination, *args, **kwargs)
            real_reconcile = book.reconcile
            def failing_reconcile(*args, **kwargs): raise OSError('synthetic reconciliation failure')
            ctx = types.SimpleNamespace(run=run, book=book, d=d)
            extra = patches(ctx) if patches else []
            raised = None
            with patch.object(contract, 'campaign_ledger', lambda live: book), patch.object(driver, 'setup', lambda *a: tools), \
                 patch.object(driver, 'prepare', prepare_double), patch.object(driver.network, 'stage', stage_double or default_stage), \
                 patch.object(shutil, 'copytree', copy), patch.object(book, 'reconcile', failing_reconcile if reconcile_failure else real_reconcile):
                stack = [patch.object(t, a, r) for t, a, r in extra]
                for x in stack: x.start()
                try:
                    try: result = driver.execute(run, task, 'rehearsal', d, None)
                    except Exception as caught: result = None; raised = type(caught).__name__
                finally:
                    for x in reversed(stack): x.stop()
            rows = events.read(run/'events.ndjson') if (run/'events.ndjson').exists() else []
            sealed = (run/'seal.json').exists()
            if sealed:
                seal = r6.read_json(run/'seal.json')
                require(seal['event_count'] == len(rows) and all(r6.sha(run/k) == v for k, v in seal['retained_sha256'].items()), 'not sealed consistently')
            raw, state = book.snapshot(); ledger_rows = ledger.parse(raw)
            return types.SimpleNamespace(run=run, result=result, raised=raised, rows=rows, state=state, book=book, sealed=sealed,
                                         ledger_rows=ledger_rows, events=[r['event'] for r in rows],
                                         retained_grant=(run/'stages/proposal-1/grant/send-grant.json').exists(),
                                         accounting=r6.read_json(run/'accounting.json') if (run/'accounting.json').exists() else None,
                                         summary=r6.read_json(run/'credential-summary.json') if (run/'credential-summary.json').exists() else None,
                                         reconciliation=r6.read_json(run/'campaign-reconciliation.json') if (run/'campaign-reconciliation.json').exists() else None,
                                         slot_files=sorted(p.name for slot in book.slots.iterdir() for p in slot.iterdir()) if book.slots.exists() else [])

    def interrupted_stage(run, name, binary, argv, mounts, grant, **kwargs):
        out = run/'stages/proposal-1/output'; out.mkdir(parents=True); (out.parent/'command.json').write_bytes(b'{}\n')
        permit = r6.read_json(run/'campaign-permit.json'); ledger.commit_grant(grant, ledger.grant_record(permit, time.monotonic_ns()))
        r6.write_json(out.parent/'proposal-1.process.json', {**TERMINATED, 'exit_code': 137})
        (out/'http.json').write_bytes(b'{')
        raise episode.StageFailure('proposal-1', 'resource_exhaustion', 'synthetic termination during record write')

    def interrupted():
        """The review's interruption: committed grant, truncated http.json, killed stage. Accounting must not invent zeros."""
        p = production(interrupted_stage)
        require(p.rows[-1]['event'] == 'episode_rejected' and p.result['accepted'] is False and p.result['failure_category'] == 'transport_record_unreadable')
        require(p.reconciliation['kind'] == 'send_grant' and p.reconciliation['send_outcome'] == 'unknown'
                and p.reconciliation['evidence']['record_read_failures'][0]['path'] == 'http.json')
        require(p.state['open_reservations'] == [] and p.state['transmissions_consumed'] == 1)
        a = p.accounting
        require(a['attempts_reserved'] == 1 and a['grant_committed'] is True and a['send_outcome'] == 'unknown' and a['allowance_consumed'] == 1
                and a['transport_record_observed'] is False and a['transmissions_observed'] is None and a['connection_attempts'] is None
                and a['ledger_outcome'] == 'send_grant' and a['ledger_reconciled'] is True and p.summary['ledger_reconciled'] is True)
        require(p.retained_grant, 'slot contents not retained in the run')
        return {'terminal_event': 'episode_rejected', 'ledger': 'send_grant / unknown; consumed',
                'accounting': {k: a[k] for k in ('grant_committed', 'send_outcome', 'allowance_consumed', 'transmissions_observed', 'transport_record_observed')}}
    suite.case('interrupted_record_finalized_and_consumed', interrupted)

    def pre_launch():
        """The review's copy failure after reservation: no sender was ever launched, so the reservation is released and reported."""
        p = production(copy_failure=True)
        require(p.reconciliation['kind'] == 'release' and p.reconciliation['reason'] == 'pre_launch_failure' and p.reconciliation['launched'] is False)
        a = p.accounting
        require(a['attempts_reserved'] == 1 and a['ledger_outcome'] == 'release' and a['ledger_reconciled'] is True and a['allowance_consumed'] == 0
                and a['transport_record_observed'] is False and a['transmissions_observed'] is None and p.summary['ledger_reconciled'] is True)
        require(p.summary['failure_category'] == 'harness_failure' and p.state['open_reservations'] == [] and p.state['presend_attempts_used'] == 1)
        return {'copy_failure_after_reservation': 'release (pre_launch_failure), reported with attempts_reserved 1'}
    suite.case('lifecycle_pre_launch_failure_released', pre_launch)

    def non_object():
        outcomes = {}
        for label, http_bytes, process_value in (('http_list', b'[1]\n', {**TERMINATED, 'exit_code': 137}), ('process_list', b'{', [1])):
            def stage(run, name, binary, argv, mounts, grant, **kwargs):
                out = run/'stages/proposal-1/output'; out.mkdir(parents=True); (out.parent/'command.json').write_bytes(b'{}\n')
                permit = r6.read_json(run/'campaign-permit.json'); ledger.commit_grant(grant, ledger.grant_record(permit, time.monotonic_ns()))
                r6.write_json(out.parent/'proposal-1.process.json', process_value); (out/'http.json').write_bytes(http_bytes)
                raise episode.StageFailure('proposal-1', 'resource_exhaustion', 'synthetic')
            p = production(stage)
            require(p.reconciliation['kind'] == 'send_grant' and p.state['open_reservations'] == [] and p.accounting['attempts_reserved'] == 1
                    and p.accounting['grant_committed'] is True and p.summary['ledger_reconciled'] is True)
            failures = {f['path']: f['error'] for f in p.reconciliation['evidence']['record_read_failures']}
            require('not_an_object' in failures.values(), str(failures))
            outcomes[label] = {'ledger': 'send_grant', 'read_failures': failures}
        return outcomes
    suite.case('lifecycle_non_object_records_consumed', non_object)

    def reconcile_failure():
        p = production(interrupted_stage, reconcile_failure=True)
        a = p.accounting
        require(p.reconciliation is None and p.state['open_reservations'] != [] and a['attempts_reserved'] == 1 and a['ledger_reconciled'] is False
                and a['ledger_outcome'] is None and a['allowance_consumed'] is None and p.summary['ledger_reconciled'] is False
                and p.summary['failure_category'] == 'reconciliation_failure' and p.rows[-1]['event'] == 'episode_rejected'
                and p.rows[-1]['payload']['ledger_reconciled'] is False)
        require(any(r['event'] == 'reconciliation_failed' for r in p.rows))
        return {'reconciliation_failure': 'reported as open; sealed episode_rejected; nothing inferred'}
    suite.case('lifecycle_reconciliation_failure_reported', reconcile_failure)

    def unreadable():
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)/'record.json'; p.write_text('{}'); p.chmod(0)
            try:
                try: p.read_bytes(); raise AssertionError('precondition: file is readable')
                except PermissionError: pass
                value, failure_record = driver.read_record(p)
                require(value is None and failure_record['error'] == 'PermissionError' and failure_record['sha256'] is None)
                require(driver.safe_sha(p) is None)
            finally: p.chmod(0o600)
            book = temp_ledger(Path(d)/'book'); permit = reserve(book, 'run-a'); slot = with_grant(book, permit)
            (slot/ledger.GRANT_FILE).chmod(0)
            try:
                refused(lambda: ledger.read_grant(slot, permit), 'campaign_grant_unreadable')
                row, _ = book.reconcile(permit, TERMINATED, None, {})
                require(row['kind'] == 'unknown' and row['grant_state'] == 'campaign_grant_unreadable')
            finally: (slot/ledger.GRANT_FILE).chmod(0o600)
        return {'unreadable_record': 'evidence with error name, no hash', 'unreadable_grant': 'unknown, consumed'}
    suite.case('unreadable_records_are_evidence', unreadable)

    def short_write():
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d); permit = reserve(book, 'run-a'); slot = book.slot(permit['reservation_id'])
            grant = ledger.grant_record(permit, 1); real_write = os.write; progress = []
            def short(fd, data):
                n = real_write(fd, bytes(data[:7]) if not progress else bytes(data)); progress.append(n); return n
            with patch.object(os, 'write', short): durable = ledger.commit_grant(slot, grant)
            require(isinstance(durable, int) and progress[0] == 7 and len(progress) == 2)
            require((slot/ledger.GRANT_FILE).read_bytes() == ledger.canonical(grant)+b'\n' and ledger.read_grant(slot, permit) == grant)
            with tempfile.TemporaryDirectory() as e:
                other = temp_ledger(e); permit2 = reserve(other, 'run-a'); slot2 = other.slot(permit2['reservation_id'])
                with patch.object(os, 'write', lambda fd, data: 0):
                    refused(lambda: ledger.commit_grant(slot2, ledger.grant_record(permit2, 1)), 'campaign_write_stalled')
                require((slot2/ledger.GRANT_FILE).exists(), 'a stalled write must leave the marker')
        return {'short_write': 'completed by loop; full bytes durable', 'stalled_write': 'campaign_write_stalled; marker retained'}
    suite.case('grant_short_write_completed', short_write)

    def partial_failure():
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d); permit = reserve(book, 'run-a'); slot = book.slot(permit['reservation_id'])
            grant = ledger.grant_record(permit, 1); real_write = os.write; calls = []
            def failing(fd, data):
                if calls: raise OSError(5, 'synthetic I/O error after a partial write')
                calls.append(1); return real_write(fd, bytes(data[:7]))
            with patch.object(os, 'write', failing):
                try: ledger.commit_grant(slot, grant); raise AssertionError('accepted')
                except OSError: pass
            require((slot/ledger.GRANT_FILE).read_bytes() == (ledger.canonical(grant)+b'\n')[:7])
            refused(lambda: ledger.slot_open(slot), 'campaign_grant_slot_used')
            refused(lambda: ledger.read_grant(slot, permit), 'campaign_grant_unreadable')
            row, _ = book.reconcile(permit, TERMINATED, None, {})
            require(row['kind'] == 'unknown' and row['grant_state'] == 'campaign_grant_unreadable')
            refused(lambda: book.reserve('run-b', reservation_shape(), BIND, {}), 'campaign_transmissions_exhausted')
            source = (r6.ROOT/'campaign_https.py').read_text()
            require('campaign_grant_write_failure' in source and source.index('except (ledger.Failure, OSError)') < source.index("conn.putrequest"))
        return {'failure_after_partial_write': 'marker retained; slot closed; unknown, consumed; actor classifies and does not send'}
    suite.case('grant_partial_write_failure_consumed', partial_failure)

    def stage_writing(http_bytes, process_value, grant=True):
        def stage(run, name, binary, argv, mounts, slot, **kwargs):
            out = run/'stages/proposal-1/output'; out.mkdir(parents=True); (out.parent/'command.json').write_bytes(b'{}\n')
            if grant:
                permit = r6.read_json(run/'campaign-permit.json'); ledger.commit_grant(slot, ledger.grant_record(permit, time.monotonic_ns()))
            r6.write_json(out.parent/'proposal-1.process.json', process_value); (out/'http.json').write_bytes(http_bytes)
            raise episode.StageFailure('proposal-1', 'resource_exhaustion', 'synthetic interruption')
        return stage

    def ledger_fd_writer(ctx, behaviour):
        """Patch os.write only for the ledger file's inode."""
        inode = ctx.book.path.stat().st_ino; real = os.write; calls = []
        def write(fd, data):
            try: same = os.fstat(fd).st_ino == inode
            except OSError: same = False
            if not same: return real(fd, data)
            calls.append(len(data)); return behaviour(real, fd, data, len(calls))
        return [(os, 'write', write)]

    def json_writer_failure(target_name):
        real = r6.write_json
        def write_json(path, value):
            if Path(path).name == target_name: raise OSError(5, 'synthetic evidence-write failure: '+target_name)
            return real(path, value)
        return lambda ctx: [(r6, 'write_json', write_json)]

    def head_failure_at(rows_at, also_snapshot=False):
        def patches(ctx):
            real = ctx.book._write_head; real_snapshot = ctx.book.snapshot
            def head(rows, last_hash):
                if rows == rows_at: raise OSError(5, 'synthetic head failure at row '+str(rows))
                return real(rows, last_hash)
            def snapshot():
                if also_snapshot: raise OSError(5, 'synthetic snapshot failure after recovery')
                return real_snapshot()
            return [(ctx.book, '_write_head', head), (ctx.book, 'snapshot', snapshot)]
        return patches

    def append_failure(ctx):
        real = ctx.book._append
        def append(rows, row):
            if row['kind'] in ledger.TERMINAL: raise OSError(5, 'synthetic append failure before the terminal row')
            return real(rows, row)
        return [(ctx.book, '_append', append)]

    def event_failure_once(event_name, also=None):
        def patches(ctx):
            real = events.append; fired = []
            def append(run, stage, event, payload, *a, **k):
                if event == event_name and not fired: fired.append(1); raise OSError(5, 'synthetic receipt failure: '+event_name)
                return real(run, stage, event, payload, *a, **k)
            return [(events, 'append', append)]+(also(ctx) if also else [])
        return patches

    def copyfile_failure(ctx):
        real = shutil.copyfile
        def copyfile(src, dst, *a, **k):
            if 'slots' in str(src): raise OSError(5, 'synthetic evidence copy failure')
            return real(src, dst, *a, **k)
        return [(shutil, 'copyfile', copyfile)]

    valid_http = lambda: events.canonical({'connection_attempts': 0, 'header_sends_started': 0, 'header_sends_returned': 0, 'body_sends_started': 0,
        'body_sends_returned': 0, 'failure_category': None, 'http_status': None, 'grant_committed': False, 'send_outcome': 'not_started', 'mode': 'rehearsal',
        'request_sha256': 'a'*64, 'credential_commitment_sha256': None, 'commitment_nonce': 'n', 'reservation_id': None, 'tls_verified_at_ns': None,
        'header_send_at_ns': None})+b'\n'
    interrupted = lambda: stage_writing(b'{', {**TERMINATED, 'exit_code': 137})
    FAULTS = {
        # name: (stage double, patches builder, expectations over authoritative state / lifecycle / accounting / evidence)
        'ledger_short_append': (interrupted(), lambda ctx: ledger_fd_writer(ctx, lambda real, fd, data, n: real(fd, bytes(data[:7]))),
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant', 'attempts': 1, 'state': 'reserved', 'reconciled': True,
             'allowance': 1, 'evidence_complete': True, 'sealed': True, 'terminal_event': 'episode_rejected'}),
        'ledger_append_failure_after_partial': (interrupted(),
            lambda ctx: ledger_fd_writer(ctx, lambda real, fd, data, n: real(fd, bytes(data[:7])) if n == 1 else (_ for _ in ()).throw(OSError(5, 'synthetic I/O error after a partial append'))),
            {'reservations': 0, 'open': 0, 'consumed': 0, 'terminal': None, 'attempts': 0, 'state': 'not_reserved', 'reconciled': True,
             'allowance': None, 'evidence_complete': True, 'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'campaign_ledger',
             'events': ['reservation_uncertain']}),
        'reserve_head_failure': (interrupted(), head_failure_at(2),
            {'reservations': 1, 'open': 0, 'consumed': 0, 'terminal': 'release', 'attempts': 1, 'state': 'reserved', 'reconciled': True,
             'allowance': 0, 'evidence_complete': True, 'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'harness_failure',
             'events': ['reservation_uncertain', 'reservation_recovered']}),
        'reservation_receipt_failure': (interrupted(), json_writer_failure('campaign-permit.json'),
            {'reservations': 1, 'open': 0, 'consumed': 0, 'terminal': 'release', 'attempts': 1, 'state': 'reserved', 'reconciled': True,
             'allowance': 0, 'evidence_complete': True, 'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'harness_failure'}),
        'request_reserved_event_failure': (interrupted(), event_failure_once('request_reserved'),
            {'reservations': 1, 'open': 0, 'consumed': 0, 'terminal': 'release', 'attempts': 1, 'state': 'reserved', 'reconciled': True,
             'allowance': 0, 'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'harness_failure'}),
        'stage_interrupted_truncated_http': (interrupted(), None,
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant', 'attempts': 1, 'reconciled': True, 'allowance': 1,
             'evidence_complete': True, 'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'transport_record_unreadable'}),
        'http_empty_object': (stage_writing(b'{}\n', {**TERMINATED, 'exit_code': 137}), None,
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant', 'attempts': 1, 'reconciled': True, 'allowance': 1,
             'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'transport_record_unreadable', 'read_failure': 'schema'}),
        'http_wrong_types': (stage_writing(valid_http().replace(b'"connection_attempts":0', b'"connection_attempts":"0"'), {**TERMINATED, 'exit_code': 137}), None,
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant', 'attempts': 1, 'reconciled': True, 'allowance': 1,
             'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'transport_record_unreadable', 'read_failure': 'schema'}),
        'process_missing_fields_no_grant': (stage_writing(valid_http(), {'exit_code': 1}, grant=False), None,
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'unknown', 'attempts': 1, 'reconciled': True, 'allowance': 1,
             'sealed': True, 'terminal_event': 'episode_rejected', 'read_failure': 'schema'}),
        'reconciliation_receipt_failure': (interrupted(), json_writer_failure('campaign-reconciliation.json'),
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant', 'attempts': 1, 'reconciled': True, 'allowance': 1,
             'evidence_complete': False, 'sealed': True, 'terminal_event': 'episode_rejected', 'receipt_absent': True}),
        'reservation_uncertain_event_failure': (interrupted(), event_failure_once('reservation_uncertain', head_failure_at(2)),
            {'reservations': 1, 'open': 0, 'consumed': 0, 'terminal': 'release', 'attempts': 1, 'state': 'reserved', 'reconciled': True,
             'allowance': 0, 'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'harness_failure'}),
        'reservation_recovered_event_failure': (interrupted(), event_failure_once('reservation_recovered', head_failure_at(2)),
            {'reservations': 1, 'open': 0, 'consumed': 0, 'terminal': 'release', 'attempts': 1, 'state': 'reserved', 'reconciled': True,
             'allowance': 0, 'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'harness_failure'}),
        'reservation_reconciled_event_failure': (interrupted(), event_failure_once('reservation_reconciled'),
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant', 'attempts': 1, 'state': 'reserved', 'reconciled': True,
             'allowance': 1, 'evidence_complete': False, 'sealed': True, 'terminal_event': 'episode_rejected'}),
        'reconcile_append_failure_after_marker': (interrupted(), append_failure,
            {'reservations': 1, 'open': 1, 'consumed': 0, 'terminal': None, 'attempts': 1, 'reconciled': False, 'allowance': None,
             'evidence_complete': False, 'sealed': True, 'terminal_event': 'episode_rejected', 'category': 'reconciliation_failure', 'events': ['reconciliation_failed']}),
        'reconcile_head_failure_after_row': (interrupted(), head_failure_at(3),
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant', 'attempts': 1, 'reconciled': True, 'allowance': 1,
             'evidence_complete': True, 'sealed': True, 'terminal_event': 'episode_rejected', 'recovered': 'OSError'}),
        'reconcile_recovery_snapshot_failure': (interrupted(), head_failure_at(3, also_snapshot=True),
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant', 'attempts': 1, 'reconciled': True, 'allowance': 1,
             'evidence_complete': False, 'sealed': True, 'terminal_event': 'episode_rejected', 'recovered': 'OSError'}),
        'evidence_copy_failure': (interrupted(), copyfile_failure,
            {'reservations': 1, 'open': 0, 'consumed': 1, 'terminal': 'send_grant', 'attempts': 1, 'reconciled': True, 'allowance': 1,
             'evidence_complete': False, 'sealed': True, 'terminal_event': 'episode_rejected'}),
    }

    def fault_sweep():
        """Table-driven: for each injected fault, authoritative state, lifecycle state, allowance accounting and evidence completion are checked separately."""
        results = {}
        for name, (stage, patches, expect) in FAULTS.items():
            p = production(stage, patches=patches)
            require(p.raised is None, f'{name}: execute raised {p.raised}')
            observed = {'reservations': p.state['reservations'], 'open': len(p.state['open_reservations']), 'consumed': p.state['transmissions_consumed'],
                        'terminal': next((r['kind'] for r in p.ledger_rows if r['kind'] in ledger.TERMINAL), None),
                        'attempts': p.accounting['attempts_reserved'], 'state': p.accounting['reservation_state'],
                        'reconciled': p.accounting['ledger_reconciled'], 'allowance': p.accounting['allowance_consumed'],
                        'evidence_complete': p.accounting.get('evidence_complete'), 'sealed': p.sealed,
                        'terminal_event': p.events[-1] if p.events else None, 'category': p.summary['failure_category'],
                        'receipt_absent': p.reconciliation is None, 'events': p.events,
                        'read_failure': (next((f['error'] for f in (p.reconciliation or {}).get('evidence', {}).get('record_read_failures', [])), None)),
                        'recovered': (p.summary['accounting'].get('reconciliation_recovered') if p.summary else None)}
            observed['recovered'] = next((r['payload'].get('recovered') for r in p.rows if r['event'] == 'reservation_reconciled'), None)
            for key, value in expect.items():
                if key == 'events': require(all(e in observed['events'] for e in value), f'{name}: events {value} not all present in {observed["events"]}')
                else: require(observed[key] == value, f'{name}: {key} observed {observed[key]!r}, expected {value!r}')
            require(p.summary['ledger_reconciled'] == p.accounting['ledger_reconciled'] and p.summary['reservation_state'] == p.accounting['reservation_state']
                    and p.summary['evidence_complete'] == p.accounting['evidence_complete'], f'{name}: summary disagrees with accounting')
            if p.accounting['evidence_complete'] and p.accounting['attempts_reserved'] == 1:
                require(p.reconciliation is not None and 'reservation_reconciled' in p.events, f'{name}: evidence_complete without the reconciliation receipt or event')
            require(p.rows[-1]['payload']['evidence_complete'] == p.accounting['evidence_complete'] and p.rows[-1]['payload']['accepted'] is False,
                    f'{name}: terminal payload disagrees')
            results[name] = {k: observed[k] for k in ('reservations', 'open', 'consumed', 'terminal', 'attempts', 'state', 'reconciled', 'allowance', 'evidence_complete', 'sealed', 'terminal_event', 'category')}
        return results
    suite.case('persistence_fault_sweep', fault_sweep)

    def partial_append():
        with tempfile.TemporaryDirectory() as d:
            book = temp_ledger(d); complete = book.path.read_bytes()
            with open(book.path, 'ab') as f: f.write(b'{"domain":"r6-campaign-ledger-2","sequence":1,"kind":"reservation"')  # an append that never completed
            refused(lambda: ledger.parse(book.path.read_bytes()), 'campaign_ledger_partial_append')
            _, state = book.snapshot()
            require(book.path.read_bytes() == complete and state['reservations'] == 0 and getattr(book, 'recovered_partial_append', False))
            permit = reserve(book, 'run-a'); require(book.path.read_bytes().endswith(b'\n') and r6.read_json(book.head)['rows'] == 2)
            lines = book.path.read_bytes().splitlines(True); book.path.write_bytes(b''.join(lines[:-1]))  # a committed row removed: head is a floor
            refused(lambda: book.snapshot(), 'campaign_ledger_truncated')
        return {'partial_trailing_line': 'discarded under the head floor', 'committed_row_removed': 'campaign_ledger_truncated'}
    suite.case('ledger_partial_append_recovered', partial_append)

    def marker_recovery():
        with tempfile.TemporaryDirectory() as d:  # complete marker, terminal append fails, next call completes from the validated marker
            book = temp_ledger(d); permit = reserve(book, 'run-a'); slot = book.slot(permit['reservation_id'])
            real = book._append
            def failing(rows, row):
                if row['kind'] in ledger.TERMINAL: raise OSError(5, 'synthetic append failure after the marker')
                return real(rows, row)
            with patch.object(book, '_append', failing):
                try: book.reconcile(permit, TERMINATED, UNSENT, {}); raise AssertionError('accepted')
                except OSError: pass
            require((slot/'release.json').exists() and book.snapshot()[1]['open_reservations'] == [permit['reservation_id']])
            row, _ = book.reconcile(permit, TERMINATED, UNSENT, {})
            require(row['kind'] == 'release' and row['reason'] == 'completed_from_marker' and row['recovered'] is True
                    and row['marker_sha256'] == r6.sha(slot/'release.json') and r6.read_json(slot/'release.json')['kind'] == 'release')
        with tempfile.TemporaryDirectory() as d:  # torn marker: seven bytes of release.json, then the next call consumes with a valid unknown receipt
            book = temp_ledger(d); permit = reserve(book, 'run-a'); slot = book.slot(permit['reservation_id'])
            real_write = os.write; calls = []
            def torn(fd, data):
                if calls: raise OSError(5, 'synthetic I/O error after a partial marker write')
                calls.append(1); return real_write(fd, bytes(data[:7]))
            with patch.object(os, 'write', torn):
                try: book.reconcile(permit, TERMINATED, UNSENT, {}); raise AssertionError('accepted')
                except OSError: pass
            require((slot/'release.json').stat().st_size == 7 and book.snapshot()[1]['open_reservations'] == [permit['reservation_id']])
            row, _ = book.reconcile(permit, TERMINATED, UNSENT, {})
            require(row['kind'] == 'unknown' and row['reason'] == 'torn_marker' and row['torn_marker'] == 'release.json'
                    and row['marker_sha256'] == r6.sha(slot/'unknown.json') and r6.read_json(slot/'unknown.json')['kind'] == 'unknown')
            require(sorted(p.name for p in slot.iterdir()) == ['release.json', 'unknown.json'])
            refused(lambda: book.reserve('run-b', reservation_shape(), BIND, {}), 'campaign_transmissions_exhausted')
            refused(lambda: ledger.slot_open(slot), 'campaign_grant_slot_used')
        with tempfile.TemporaryDirectory() as d:  # torn marker, then the repair's own terminal append fails: the retry keeps the association
            book = temp_ledger(d); permit = reserve(book, 'run-a'); slot = book.slot(permit['reservation_id'])
            real_write = os.write; calls = []
            def torn(fd, data):
                if calls: raise OSError(5, 'synthetic I/O error after a partial marker write')
                calls.append(1); return real_write(fd, bytes(data[:7]))
            with patch.object(os, 'write', torn):
                try: book.reconcile(permit, TERMINATED, UNSENT, {}); raise AssertionError('accepted')
                except OSError: pass
            real_append = book._append
            def failing(rows, row):
                if row['kind'] in ledger.TERMINAL: raise OSError(5, 'synthetic append failure after the replacement marker')
                return real_append(rows, row)
            with patch.object(book, '_append', failing):
                try: book.reconcile(permit, TERMINATED, UNSENT, {}); raise AssertionError('accepted')
                except OSError: pass
            require(sorted(p.name for p in slot.iterdir()) == ['release.json', 'unknown.json'] and book.snapshot()[1]['open_reservations'] == [permit['reservation_id']])
            row, _ = book.reconcile(permit, TERMINATED, UNSENT, {})
            require(row['kind'] == 'unknown' and row['reason'] == 'completed_from_marker' and row['torn_marker'] == 'release.json'
                    and row['marker_sha256'] == r6.sha(slot/'unknown.json'))
        with tempfile.TemporaryDirectory() as d:  # a torn unknown marker is a safe stop for the operator, not an automatic recovery
            book = temp_ledger(d); permit = reserve(book, 'run-a'); slot = book.slot(permit['reservation_id'])
            (slot/'unknown.json').write_bytes(b'{"kind"')
            refused(lambda: book.reconcile(permit, None, None, {}), 'campaign_marker_torn_unrecoverable')
            refused(lambda: book.reserve('run-b', reservation_shape(), BIND, {}), 'campaign_reservation_open')
        return {'complete_marker': 'completed_from_marker, release', 'torn_release_marker': 'unknown with a valid receipt beside the torn bytes; consumed',
                'torn_release_repair_interrupted': 'retry completes from the valid marker and keeps torn_marker', 'torn_unknown_marker': 'safe stop; reservation stays open for the operator'}
    suite.case('marker_recovery_complete_and_torn', marker_recovery)

    def finalize_evidence():
        with tempfile.TemporaryDirectory() as d:
            run = Path(d)/'run'; run.mkdir(); nonce = credential.nonce()
            events.append(run, 'episode', 'episode_started', {'probe': True}, task_id=task.id)
            summary = {'proof_accepted': True, 'credential_use_accepted': True, 'ledger_reconciled': True, 'evidence_complete': False, 'failure_category': None}
            r6.write_json(run/'credential-summary.json', summary)
            accepted, _, _ = driver.finalize(run, credential.derive(nonce), nonce, summary, False)
            rows = events.read(run/'events.ndjson'); payload = rows[-1]['payload']
            require(accepted is False and rows[-1]['event'] == 'episode_rejected' and payload['evidence_complete'] is False and payload['proof_accepted'] is True
                    and r6.read_json(run/'seal.json')['accepted'] is False)
        with tempfile.TemporaryDirectory() as d:
            run = Path(d)/'run'; run.mkdir(); nonce = credential.nonce()
            events.append(run, 'episode', 'episode_started', {'probe': True}, task_id=task.id)
            summary = {'proof_accepted': True, 'credential_use_accepted': True, 'ledger_reconciled': False, 'evidence_complete': True, 'failure_category': None}
            r6.write_json(run/'credential-summary.json', summary)
            accepted, _, _ = driver.finalize(run, credential.derive(nonce), nonce, summary, False)
            require(accepted is False and events.read(run/'events.ndjson')[-1]['event'] == 'episode_rejected')
        return {'proof_true_evidence_incomplete': 'episode_rejected, accepted false', 'proof_true_ledger_unreconciled': 'episode_rejected'}
    suite.case('finalize_requires_complete_evidence', finalize_evidence)

    def pending():
        with tempfile.TemporaryDirectory() as d:
            run = Path(d)/'run'; run.mkdir(); nonce = credential.nonce()
            events.append(run, 'episode', 'episode_started', {'probe': True}, task_id=task.id)
            summary = {'proof_accepted': True, 'credential_use_accepted': True, 'ledger_reconciled': True, 'evidence_complete': True, 'failure_category': None}
            r6.write_json(run/'credential-summary.json', summary)
            accepted, _, _ = driver.finalize(run, credential.derive(nonce), nonce, summary, True)
            rows = events.read(run/'events.ndjson'); payload = rows[-1]['payload']
            require(accepted is False and rows[-1]['event'] == 'episode_finished' and payload['publication_accepted'] is None
                    and payload['publication_pending'] is True and payload['proof_accepted'] is True)
        return {'live': 'episode_finished with accepted=false until the operator scan is bound'}
    suite.case('live_publication_pending_not_accepted', pending)

    def counters():
        with tempfile.TemporaryDirectory() as d:
            http = actor_run(d).http
            for key in ('body_sends_started', 'body_sends_returned', 'header_sends_started', 'grant_committed', 'send_outcome', 'connection_attempts',
                        'grant_created_at_ns', 'grant_durable_at_ns'):
                require(key in http)
            require(http['send_outcome'] in ('not_started', 'unknown', 'returned'))
        source = (r6.ROOT/'campaign_episode.py').read_text()
        for key in ('transmissions_observed', 'transmissions_returned', 'grant_committed', 'send_outcome', 'ledger_outcome', 'allowance_consumed',
                    'transport_record_observed', 'ledger_reconciled', 'evidence_complete', 'reservation_state'):
            require("'"+key+"'" in source)
        require('live_model_cost_usd' not in source and 'live_transmissions_consumed' not in source, 'a second allowance field or a cost name exists')
        with tempfile.TemporaryDirectory() as d:  # unknown disposition stays unknown in every allowance field
            lifecycle = {'permit': {'reservation_id': 'r'}, 'reservation': {}, 'reconciliation': None, 'reconcile_error': 'x', 'reservation_state': 'reserved'}
            a = driver.accounting_for(Path(d), c, True, None, None, lifecycle)
            require(a['allowance_consumed'] is None and a['ledger_reconciled'] is False and a['transmissions_observed'] is None and a['live'] is True)
        return {'accounting_fields': ['transmissions_observed', 'transmissions_returned', 'grant_committed', 'send_outcome', 'ledger_outcome',
                                      'allowance_consumed', 'transport_record_observed', 'ledger_reconciled', 'live_usage_ceiling_usd']}
    suite.case('counters_separate', counters)

    def ca_pinned():
        path, described = contract.bundle()
        require(described['sha256'] == c['tls']['public_ca_bundle']['sha256'] and described['certificates'] > 0)
        require(c['tls']['verify_mode'] == 'CERT_REQUIRED' and c['tls']['check_hostname'] is True and c['tls']['minimum_version'] == 'TLSv1.2')
        return {'bundle': str(path), 'certificates': described['certificates'], 'sha256': described['sha256']}
    suite.case('ca_bundle_pinned', ca_pinned)

    def parser_guards(argv, contains):
        import argparse as ap
        saved, saved_argv = ap.ArgumentParser.error, sys.argv
        try:
            ap.ArgumentParser.error = lambda self, message: (_ for _ in ()).throw(ValueError(message))
            sys.argv = ['campaign_https.py', *argv]
            return rejected(actor.main, contains)
        finally:
            ap.ArgumentParser.error, sys.argv = saved, saved_argv
    base = ['--policy', '/p', '--arguments', '/a', '--credential-file', '/c', '--ca', '/ca', '--out', '/o', '--sources', '/s',
            '--permit', '/pm', '--ledger', '/l', '--request', '/r', '--episode', 'e', '--grant', '/g', '--commitment-nonce', 'n']
    suite.case('live_refuses_fixture', lambda: parser_guards(['--mode', 'live', *base, '--fixture', '/f'], 'refuses fixture'))
    suite.case('rehearsal_requires_fixture', lambda: parser_guards(['--mode', 'rehearsal', *base], 'requires --fixture'))

    def endpoint():
        require(c['endpoint'] == contract.ENDPOINT == {'scheme': 'https', 'host': 'api.openai.com', 'port': 443, 'path': '/v1/responses'})
        require(c['network']['egress_restriction_enforced_by_harness'] is False)
        return {'endpoint': c['endpoint'], 'enforced_by': 'actor endpoint check and audited command'}
    suite.case('endpoint_allowlist_exact', endpoint)
    suite.finish()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    units(args.output.resolve())
    print(json.dumps({'passed': True, 'cases': len(CASES)}, indent=1))


if __name__ == '__main__':
    main()
