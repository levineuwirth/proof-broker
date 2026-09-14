#!/usr/bin/env python3
"""R6-009 historical auditor over the canned cohort runs (revision population v1 or v2). Non-locked; read-only.

The R6-008 campaign auditor's case population, carried forward relationship by relationship and adapted to the cohort:
every run binds its own policy revision, lock, sources, the one frozen contract and the one campaign from its provenance;
the request is regenerated from the frozen task and the envelope recomputed under the contract; the entity bytes that were
actually serialized, sent and received are compared with that rendering and with each other across revisions; the
shared campaign ledger (activation, revision rows, (task, draw) slots) is read from the authoritative directory and from
every run's retained snapshots; disposition is derived from supervisor and grant evidence; the expected event order, the
authority mounts (ledger read-only, this reservation's slot writable, contract and instruction bytes), single process
receipts, the credential commitment, accounting recomputed with the driver's own helper, publication recomputed with the
frozen scanner, terminal commitments and complete finalization are all reconstructed from retained bytes. On top: the
cross-revision relationships (identical model input per task, distinct receipts, continuous accounting, consumed slots
persisting into a later revision's refusal) and a second task whose model input is distinct. After the v2 review: every
reservation amount is the price of the frozen limits and equals the rederived admission (committed money is derived from
those checked amounts); the sender's stage returned within the frozen resource limits; module mounts are bound to the
recorded repository layout and the driver's recorded roles; and every supervisor receipt payload is reconstructed from
the record it names and compared exactly, the credential receipt to the canary and the receiver's observation. After the v3
review: the whole sender command is rebuilt from the pinned runtime record and the recorded layout and compared exactly, and
every stage on the outcome's frozen path must have returned within its limits, not only the sender.

The case population is derived from the frozen run population and its declared outcomes; the audit fails unless exactly
that set of named cases was evaluated. Superseded revisions are audited under explicit version dispatch and reported as
superseded, never as invalid merely for being older.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import campaign_ledger as base
import campaign_network as network
import cohort_budget as budget
import cohort_contract as contract
import cohort_episode as driver
import cohort_ledger as ledger
import credential
import credential_episode as publication_driver
import envelope_proof_audit
import episode
import inspect
import events
import payload
import priced_payload_v2 as v2
import pricing_gate_v2 as gate2
import pricing_gate_v3 as gate
import provider_payload
import publication
import run as r6

D1, C8 = 'verinf-d1-70', 'c1-c8-2p18'
# Explicit version dispatch: the frozen run population of each revision and what its lock promised.
POPULATIONS = {
    'farkas_cohort_v1': {'runs': 'cohort-runs', 'lock': 'cohort-harness-v1.sha256.json', 'policy': 'farkas-cohort-v1.json',
                         'expected': {'r1-d1-draw1': ('proof', D1, 1, 1), 'r1-d1-draw2-format': ('release', D1, 2, 1),
                                      'r2-d1-draw1-refused': ('refused', D1, 1, 2), 'r2-d1-draw2': ('proof', D1, 2, 2), 'r2-d1-draw3': ('proof', D1, 3, 2)}},
    'farkas_cohort_v2': {'runs': 'cohort-runs-v2', 'lock': 'cohort-harness-v2.sha256.json', 'policy': 'farkas-cohort-v2.json',
                         'expected': {'r1-d1-draw1': ('proof', D1, 1, 1), 'r1-d1-draw2-format': ('release', D1, 2, 1), 'r1-c8-draw1': ('proof', C8, 1, 1),
                                      'r2-d1-draw1-refused': ('refused', D1, 1, 2), 'r2-d1-draw2': ('proof', D1, 2, 2), 'r2-c8-draw2': ('proof', C8, 2, 2)}},
    'farkas_cohort_v3': {'runs': 'cohort-runs-v3', 'lock': 'cohort-harness-v3.sha256.json', 'policy': 'farkas-cohort-v3.json',
                         'expected': {'r1-d1-draw1': ('proof', D1, 1, 1), 'r1-d1-draw2-format': ('release', D1, 2, 1), 'r1-c8-draw1': ('proof', C8, 1, 1),
                                      'r2-d1-draw1-refused': ('refused', D1, 1, 2), 'r2-d1-draw2': ('proof', D1, 2, 2), 'r2-c8-draw2': ('proof', C8, 2, 2)}}}
RULES = {'farkas_cohort_v1': {'task_join': False, 'grant_domain': 'r6-campaign-send-grant-2'},
         'farkas_cohort_v2': {'task_join': True, 'grant_domain': 'r6-campaign-send-grant-2'},
         'farkas_cohort_v3': {'task_join': True, 'grant_domain': 'r6-campaign-send-grant-2'}}
MODULE_MOUNTS = {'/adapter.py': 'cohort_https.py', '/cohort_ledger.py': 'cohort_ledger.py', '/campaign_ledger.py': 'campaign_ledger.py',
                 '/pricing_gate_v3.py': 'pricing_gate_v3.py', '/pricing_gate_v2.py': 'pricing_gate_v2.py', '/live_https.py': 'live_https.py'}
RESERVATION_STATUS = 'byte_ceiling_plus_framing_assumption'
COHORT_MODULES = ('cohort_budget', 'cohort_contract', 'cohort_ledger', 'cohort_episode', 'cohort_https', 'pricing_gate_v3')
# imported modules bound to the run's retained copy; file-only entries are frozen upstream sources the driver mounts or imports
MODULES = {'cohort_budget': ('cohort-harness', budget), 'cohort_contract': ('cohort-harness', contract), 'cohort_ledger': ('cohort-harness', ledger),
           'cohort_episode': ('cohort-harness', driver), 'cohort_https': ('cohort-harness', None), 'pricing_gate_v3': ('cohort-harness', gate),
           'campaign_ledger': ('campaign-harness', base), 'campaign_network': ('campaign-harness', None), 'campaign_budget': ('campaign-harness', None),
           'campaign_contract': ('campaign-harness', None), 'campaign_episode': ('campaign-harness', None), 'campaign_https': ('campaign-harness', None),
           'credential': ('credential-harness', credential), 'publication': ('credential-harness', publication),
           'credential_episode': ('credential-harness', publication_driver), 'envelope_proof_audit': ('envelope-harness', envelope_proof_audit),
           'episode': ('harness', episode), 'events': ('harness', events), 'payload': ('harness', payload), 'run': ('harness', r6), 'admission': ('harness', None),
           'priced_payload_v2': ('priced-v2-harness', v2), 'pricing_gate_v2': ('priced-v2-harness', gate2),
           'provider_payload': ('provider-harness', provider_payload), 'provider_episode': ('provider-harness', None),
           'live_https': ('live-harness', None), 'live_tls_fixture': ('live-harness', None)}
CANNED_EXPORTS = {D1: 'cd6081daac2fc64d718d28202d1742ff1e653e9862031fb19a5efeb7cd7d1812', C8: '67e53933b2185f0c65dc628a9e7d770d8e71638731fe7f4f20deb99cb53a68ae'}
COMMITMENT_DOMAIN = 'r6-campaign-credential-commitment-1'
TERMINAL_KIND = {'proof': 'send_grant', 'release': 'release'}

PREPARED = [('supervisor', 'episode', 'episode_started')] + [(s, st, e) for st in ('preparation-build', 'preparation', 'pipeline-prepare')
            for s, e in (('supervisor', 'stage_started'), ('supervisor', 'stage_finished'))] + [
            ('supervisor', 'payload', 'payload_validated'), ('supervisor', 'live-payload', 'payload_validated'),
            ('supervisor', 'proposal', 'recovery_started'), ('supervisor', 'campaign-ledger', 'reservation_attempted')]
PREFIX = PREPARED + [('supervisor', 'pricing-admission', 'pricing_admitted'), ('supervisor', 'campaign-ledger', 'request_reserved'),
                     ('supervisor', 'proposal-1', 'stage_started'), ('supervisor', 'proposal-1', 'stage_finished'),
                     ('supervisor', 'campaign-ledger', 'reservation_reconciled')]
OBSERVED = [('supervisor', 'proposal', 'https_observed'), ('supervisor', 'proposal', 'transport_validated')]
RECEIPT = [('supervisor', 'credential-receipt', 'credential_receipt_checked')]
CHILDREN = [('child_report', 'reconstruct', e) for e in ('reification_started', 'reification_finished', 'dispatch_started',
            'dispatch_received', 'certificate_verification_started', 'certificate_verification_finished',
            'reconstruction_started', 'residual_started', 'residual_finished', 'reconstruction_finished')]
PROOF = [('supervisor', 'assembly', 'stage_started'), ('supervisor', 'assembly', 'stage_finished'),
         ('supervisor', 'assembly', 'certificate_assembled'), ('supervisor', 'certificate-check', 'stage_started'),
         ('supervisor', 'certificate-check', 'stage_finished'), ('supervisor', 'certificate-check', 'independent_certificate_verdict'),
         ('supervisor', 'proposal', 'recovery_finished'), ('supervisor', 'capture-build', 'stage_started'),
         ('supervisor', 'capture-build', 'stage_finished'), ('supervisor', 'reconstruct', 'stage_started'), *CHILDREN,
         ('supervisor', 'reconstruct', 'stage_finished'), ('supervisor', 'reconstruct', 'context_validated'),
         ('supervisor', 'export', 'stage_started'), ('supervisor', 'export', 'stage_finished'),
         ('supervisor', 'validation-local', 'stage_started'), ('supervisor', 'validation-local', 'stage_finished'),
         ('supervisor', 'validation-local', 'kernel_verdict'), ('supervisor', 'validation-whole', 'stage_started'),
         ('supervisor', 'validation-whole', 'stage_finished'), ('supervisor', 'validation-whole', 'kernel_verdict'),
         ('supervisor', 'episode', 'proof_validated'), ('supervisor', 'episode', 'episode_finished')]
REJECTED = [('supervisor', 'episode', 'episode_rejected')]
STAGES = {'refused': ('preparation-build', 'preparation', 'pipeline-prepare'), 'release': ('preparation-build', 'preparation', 'pipeline-prepare', 'proposal-1'),
          'proof': ('preparation-build', 'preparation', 'pipeline-prepare', 'proposal-1', 'assembly', 'certificate-check', 'capture-build', 'reconstruct',
                    'export', 'validation-local', 'validation-whole')}
RUNTIME_PIN = 'campaign-runtime-v1'
SENDER_PREFIX = ['bwrap', *network.NAMESPACES, '--unshare-net', '--die-with-parent', '--new-session', '--cap-drop', 'ALL',
                 '--clearenv', '--setenv', 'PATH', '/no-programs', '--setenv', 'LEAN_ABORT_ON_PANIC', '1',
                 '--symlink', 'usr/lib', '/lib', '--symlink', 'usr/lib64', '/lib64',
                 '--proc', '/proc', '--dev', '/dev', '--tmpfs', '/tmp', '--dir', '/work', '--chdir', '/work']
EPHEMERAL = ('/credential', '/ca.pem', '/server.pem', '/server.key')
SEQUENCES = {'proof': PREFIX+OBSERVED+RECEIPT+PROOF, 'release': PREFIX+OBSERVED+RECEIPT+REJECTED,
             'refused': PREPARED+[('supervisor', 'campaign-ledger', 'reservation_refused')]+RECEIPT+REJECTED}


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
def load(path): return json.loads(Path(path).read_bytes())
def canonical(value): return events.canonical(value)


def expected_cases(population):
    """The complete named population, derived from the frozen runs and their declared outcomes: the audit must evaluate exactly these."""
    expected = population['expected']; tasks = sorted({t for (_, t, _, _) in expected.values()})
    names = ['population:exactly_expected_runs', 'tasks:manifests_bound', 'modules:bound_to_retained_copies', 'modules:cohort_revision',
             'campaign:single_identity', 'revisions:chained_distinct_policies_same_lock']
    names += [f'input:identical_model_bytes_across_revisions:{t}' for t in tasks]
    if len(tasks) > 1: names.append('input:distinct_model_bytes_across_tasks')
    names += ['receipts:distinct_across_runs', 'ledger:continuous_across_revisions', 'ledger:consumed_slots_persist', 'ledger:refusals_bound_to_earlier_consumption']
    for run, (kind, task, draw, revision) in expected.items():
        names += [f'{run}:versions:policy_lock_contract_campaign_bound', f'{run}:chain:valid', f'{run}:chain:expected_sequence',
                  f'{run}:request:regenerated_under_contract', f'{run}:envelope:recomputed_from_contract', f'{run}:pricing:host_admission_rederived',
                  f'{run}:seal:retained_hashes', f'{run}:publication:recomputed', f'{run}:terminal:commitments_bound',
                  f'{run}:summary:bound_to_audited_records', f'{run}:seal:chain_and_outcome', f'{run}:accounting:recomputed', f'{run}:credential_receipt:recorded',
                  f'{run}:receipts:payloads_bound_to_records', f'{run}:stages:every_stage_on_the_path_returned']
        if kind == 'refused':
            names += [f'{run}:refusal:slot_consumed_before_reservation']; continue
        names += [f'{run}:ledger:permit_and_reconciliation_bound', f'{run}:ledger:reservation_priced_from_contract_limits', f'{run}:ledger:disposition_derived',
                  f'{run}:slot:authoritative_matches_retained', f'{run}:mounts:authority_bound', f'{run}:command:reconstructed_from_pinned_runtime_and_layout',
                  f'{run}:receipts:single_pair_bound_to_process',
                  f'{run}:receipts:stage_returned_within_frozen_limits', f'{run}:grant:consistent_with_outcome',
                  f'{run}:pricing:actor_check_rederived', f'{run}:transport:record_consistent', f'{run}:transport:bodies_are_the_contract_rendering',
                  f'{run}:interpretation:reproduced', f'{run}:commitment:bound_to_mounted_canary', f'{run}:slot:identity_in_receipts_not_in_model_bytes']
        if kind == 'proof':
            names += [f'{run}:transport:local_send_and_remote_receipt', f'{run}:grant:ordered_before_first_header_byte', f'{run}:proof:response_bound',
                      f'{run}:proof:certificate_bound', f'{run}:proof:attribution_passed_through', f'{run}:proof:shared_checker', f'{run}:proof:export_expected']
        else:
            names += [f'{run}:failure:classified_and_finalized']
    if len(names) != len(set(names)): raise ValueError('duplicate expected case name')
    return tuple(names)


def retained(run, population):
    ph = run/'provenance/cohort-harness'
    policy_path = ph/'policies'/population['policy']; lock_path = ph/'policies'/population['lock']
    return ph, policy_path, lock_path, load(policy_path), load(lock_path)


def versions(a, run, name, kind, task, draw, revision, population, revision_name, contract_value, contract_digest):
    sp = load(run/'search-policy.json'); ph, policy_path, lock_path, policy, lock = retained(run, population)
    retained_contract = load(ph/'contracts/farkas-proposal-contract-v1.json'); files = tuple(lock)
    sources = {f: sha((ph/f).read_bytes()) for f in files}
    campaign = policy['campaign']['id']
    origin = sorted(p.name for p in (run/'pricing-origin').iterdir()); pinned = sorted(p.name for p in (run/'pricing-sources').iterdir())
    same_sources = origin == pinned and all((run/'pricing-origin'/f).read_bytes() == (run/'pricing-sources'/f).read_bytes() for f in origin)
    try: policy_ok = gate.check_policy(policy, contract_value) is None and gate.check_contract(retained_contract) == contract_digest
    except gate.Failure: policy_ok = False
    a.require(sp['config_sha256'] == sha(policy_path.read_bytes()) and sp['source_lock_sha256'] == sha(lock_path.read_bytes())
              and policy['source_lock_sha256'] == sha(lock_path.read_bytes())  # the frozen policy names this lock; mirrors agreeing is not that
              and sorted(lock) == sorted(contract.FILES) and all(lock[f] == sources[f] for f in files)
              and sp['name'] == policy['name'] == revision_name and sp['mode'] == 'rehearsal' and sp['task_id'] == task.id and sp['draw'] == draw
              and sp['revision'] == policy['revision'] == revision and sp['campaign_id'] == campaign
              and sp['contract_sha256'] == policy['contract_sha256'] == contract_digest == sha(canonical(retained_contract)+b'\n')
              and retained_contract == contract_value and sp['manifest_sha256'] == sha((task.path/'manifest.json').read_bytes())
              and policy['live_enabled'] is False and policy['authorization'] is None and policy['prompt_sha256'] == contract_value['instruction']['sha256']
              and policy_path.read_bytes() == canonical(policy)+b'\n' and policy['campaign']['rehearsal_authorization'] == contract.REHEARSAL_AUTHORIZATION
              and sp['ledger_path'] == f'ledgers/campaigns/{campaign}/rehearsal/ledger.ndjson' and sp['ledger_slots'] == f'ledgers/campaigns/{campaign}/rehearsal/slots'
              and policy_ok and same_sources and policy['pricing_gate_sha256'] == sha((ph/'pricing_gate_v3.py').read_bytes())
              and (kind == 'refused' or ((run/'transport-policy.json').read_bytes() == policy_path.read_bytes()
                                         and (run/'transport-contract.json').read_bytes() == canonical(retained_contract)+b'\n'
                                         and sha((run/'transport-instruction.txt').read_bytes()) == contract_value['instruction']['sha256'])),
              f'{name}:versions:policy_lock_contract_campaign_bound')
    return sp, policy


def modules(a, root, names, revision_name):
    """Frozen upstream modules must equal every run's retained copies; cohort modules only under the current revision."""
    current = revision_name == contract.NAME
    def same(run, m, folder):
        p = run/'provenance'/folder/(m+'.py'); source = ROOT/(m+'.py')
        return p.is_file() and source.is_file() and sha(source.read_bytes()) == sha(p.read_bytes())
    for m, (folder, module) in MODULES.items():
        if module is not None and Path(module.__file__).resolve() != (ROOT/(m+'.py')).resolve(): a.require(False, 'modules:bound_to_retained_copies', 'imported '+m+' from elsewhere')
    upstream = [f'{n}/{m}' for n in names for m, (folder, _) in MODULES.items() if m not in COHORT_MODULES and not same(root/n, m, folder)]
    a.require(not upstream, 'modules:bound_to_retained_copies', 'upstream modules differ from the retained copies: '+', '.join(upstream))
    cohort = [f'{n}/{m}' for n in names for m, (folder, _) in MODULES.items() if m in COHORT_MODULES and not same(root/n, m, folder)]
    if current:
        a.require(not cohort, 'modules:cohort_revision', 'current revision, yet cohort modules differ from the retained copies: '+', '.join(cohort))
        return {'revision': revision_name, 'superseded': False}
    a.require(revision_name in RULES, 'modules:cohort_revision', 'unknown cohort revision '+revision_name)
    return {'revision': revision_name, 'superseded': True, 'cohort_modules_differ_from_current': cohort,
            'qualification': 'auditor/source incompatibility for the cohort modules is recorded, not an invalidity verdict'}


def chain(a, run, name, kind, task):
    try: rows = events.read(run/'events.ndjson')
    except ValueError as error: a.require(False, f'{name}:chain:valid', str(error))
    a.require(all(r['task_id'] == task.id and r['run_id'] == rows[0]['run_id'] for r in rows), f'{name}:chain:valid')
    observed = [(r['source'], r['stage'], r['event']) for r in rows]
    a.require(observed == SEQUENCES[kind], f'{name}:chain:expected_sequence', f'{len(observed)} events')
    return rows


def request(a, run, name, kind, sp, task, contract_value, contract_digest):
    try: value = payload.strict_json(v2.request(task, load(run/'prepared.json')))
    except Exception as error: a.require(False, f'{name}:request:regenerated_under_contract', type(error).__name__+': '+str(error))
    value.pop('policy_sha256'); value['schema_version'] = gate.REQUEST_SCHEMA; value['contract_sha256'] = contract_digest
    request_bytes = (run/'live-request.json').read_bytes(); parsed = json.loads(request_bytes)
    try: gate.check_request_grammar(parsed); grammar = True
    except gate.Failure: grammar = False
    a.require(canonical(value)+b'\n' == request_bytes and 'policy_sha256' not in parsed and grammar
              and parsed['binding']['task_id'] == task.id and parsed['binding']['manifest_sha256'] == sp['manifest_sha256']
              and (kind == 'refused' or (run/'transport-request.json').read_bytes() == request_bytes), f'{name}:request:regenerated_under_contract')
    instruction = (run/'transport-instruction.txt').read_text() if kind != 'refused' else contract.PROMPT.read_text()
    expected = gate.render_arguments(contract_value, instruction, request_bytes)
    try: envelope = gate.check_envelope(contract_value, instruction, expected, request_bytes)
    except gate.Failure as error: a.require(False, f'{name}:envelope:recomputed_from_contract', error.code)
    arguments = load(run/'live-arguments.json')
    a.require(gate.same_json(arguments, expected) and canonical(arguments) == canonical(expected)
              and (kind == 'refused' or gate.same_json(load(run/'transport-arguments.json'), expected))
              and sha(instruction.encode()) == contract_value['instruction']['sha256'] and envelope['request_sha256'] == sha(request_bytes)
              and envelope['body_sha256'] == sha(gate2.entity_body(expected)) and sha((run/'prompt.txt').read_bytes()) == contract_value['instruction']['sha256'],
              f'{name}:envelope:recomputed_from_contract')
    return request_bytes, expected, instruction, gate2.entity_body(expected), envelope


def host_admission(a, run, name, kind, policy, contract_value, instruction, request_bytes, arguments):
    record = load(run/'host-pricing-admission.json')
    if kind == 'refused':
        a.require(record['accepted'] is False and record['failure_code'] == 'cohort_slot_consumed' and record['stage'] == 'cohort_ledger'
                  and record['reservation_state'] == 'not_reserved', f'{name}:pricing:host_admission_rederived')
        return record
    try: derived = gate.admission(policy, contract_value, instruction, run/'pricing-sources', arguments, request_bytes, record['evaluated_at_unix'])
    except gate.Failure as error: a.require(False, f'{name}:pricing:host_admission_rederived', error.code)
    a.require(record['accepted'] is True and derived == record and record['schema_version'] == 'r6-pricing-admission-3', f'{name}:pricing:host_admission_rederived')
    return record


def attempt_identity_bound(run, permit):
    value = permit.get('attempt_id'); receipts = [r['payload'].get('attempt_id') for r in events.read(run/'events.ndjson') if r['event'] == 'reservation_attempted']
    well_formed = isinstance(value, str) and len(value) == 64 and all(c in '0123456789abcdef' for c in value)
    return well_formed and receipts == [value]


def reconciliation_evidence(run, reconciliation):
    stage = run/'stages/proposal-1'; ev = reconciliation['evidence']
    markers = sorted(p.name for p in (stage/'grant').iterdir()) if (stage/'grant').is_dir() else []
    expected_markers = {'send_grant': ['send-grant.json'], 'release': ['release.json'], 'unknown': ['unknown.json']}[reconciliation['kind']]
    return (ev['process_sha256'] == sha((stage/'proposal-1.process.json').read_bytes())
            and ev['http_sha256'] == (sha((stage/'output/http.json').read_bytes()) if (stage/'output/http.json').exists() else None)
            and ev['grant_file_sha256'] == (sha((stage/'grant/send-grant.json').read_bytes()) if (stage/'grant/send-grant.json').exists() else None)
            and ev['launched'] is (stage/'command.json').exists() and markers == expected_markers and ev['record_read_failures'] == [])


def ledger_rows(a, run, name, kind, sp, task, draw, revision, rules, request_bytes, policy, admission, contract_digest):
    permit = load(run/'campaign-permit.json'); reconciliation = load(run/'campaign-reconciliation.json'); campaign = sp['campaign_id']
    try:
        before = ledger.parse((run/'transport-ledger.ndjson').read_bytes()); after = ledger.parse((run/'ledger-after.ndjson').read_bytes())
        s_before = ledger.state(before, campaign); s_after = ledger.state(after, campaign)
    except ledger.Failure as error: a.require(False, f'{name}:ledger:permit_and_reconciliation_bound', error.code)
    reservation = load(run/'reservation.json'); _, frozen = r6.frozen_task(task)
    if rules['task_join']: joined = permit['task_manifest_sha256'] == sha((task.path/'manifest.json').read_bytes()) and permit['challenge_sha256'] == frozen['challenge_sha256']
    else: joined = 'task_manifest_sha256' not in permit and 'challenge_sha256' not in permit  # older revision: explicit absence
    consistent_termination = reconciliation['kind'] != 'release' or reconciliation['termination_established'] or reconciliation.get('reason') == 'pre_launch_failure'
    a.require(reconciliation_evidence(run, reconciliation) and before[-1] == permit and after[-1] == reconciliation and after[:len(before)] == before
              and permit['kind'] == 'reservation' and permit['episode_id'] == name and permit['task_id'] == task.id and permit['draw'] == draw
              and permit['policy_sha256'] == sp['config_sha256'] == s_before['policy_sha256'] and s_before['revision'] == revision-1
              and permit['contract_sha256'] == contract_digest == s_before['contract_sha256']
              and permit['request_sha256'] == sha(request_bytes) and permit['arguments_sha256'] == sha(canonical(load(run/'live-arguments.json')))
              and permit['pricing_admission'] == admission and permit['reserved_micro_usd'] == permit['reservation']['reserved_micro_usd'] <= policy['limits']['total_micro_usd']
              and joined and reconciliation['kind'] == TERMINAL_KIND[kind] and reconciliation['reservation_id'] == permit['reservation_id']
              and reconciliation['task_id'] == task.id and reconciliation['draw'] == draw and reconciliation['episode_id'] == name
              and reservation == {**permit['reservation'], 'reservation_id': permit['reservation_id'], 'request_sha256': permit['request_sha256'],
                                  'arguments_sha256': permit['arguments_sha256'], 'policy_sha256': permit['policy_sha256'],
                                  'pricing_admission_sha256': sha((run/'host-pricing-admission.json').read_bytes()),
                                  'ledger_row_hash': permit['row_hash'], 'ledger_sha256': sha((run/'transport-ledger.ndjson').read_bytes())}
              and before[0]['kind'] == 'activation' and before[0]['campaign_id'] == campaign and before[0]['purpose'] == 'rehearsal'
              and before[0]['authorization'] == policy['campaign']['rehearsal_authorization'] and s_before['schedule'] == contract.REHEARSAL_SCHEDULE
              and s_before['open_reservations'] == [permit['reservation_id']] and s_after['open_reservations'] == []
              and consistent_termination and attempt_identity_bound(run, permit),
              f'{name}:ledger:permit_and_reconciliation_bound')
    return permit, reconciliation


def reservation_priced(a, run, name, policy, permit, admission, envelope):
    """The reservation amount is the price of the frozen token limits at the admitted rates, equal to the rederived admission's, not merely to
    its own mirrors; its size inputs are the recomputed envelope's."""
    limits = policy['limits']; rates = policy['pricing']['nano_usd_per_token']
    expected = {'reserved_micro_usd': gate.cost_micro(limits['input_tokens_reserved'], limits['output_tokens'], rates), 'message_utf8_bytes': envelope['message_utf8_bytes'],
                'input_tokens_reserved': limits['input_tokens_reserved'], 'output_tokens_reserved': limits['output_tokens'],
                'input_token_bound_status': RESERVATION_STATUS, 'billing_guarantee': False}
    reservation = load(run/'reservation.json'); check = load(run/'stages/proposal-1/output/pricing-check.json')
    a.require(permit['reservation'] == expected and permit['reserved_micro_usd'] == admission['reserved_micro_usd'] == check['reserved_micro_usd'] == expected['reserved_micro_usd']
              and admission['message_utf8_bytes'] == check['message_utf8_bytes'] == envelope['message_utf8_bytes'] <= limits['message_utf8_bytes']
              and admission['nano_usd_per_token'] == rates and all(reservation[k] == v for k, v in expected.items())
              and type(permit['reserved_micro_usd']) is int and expected['reserved_micro_usd'] > 0,
              f'{name}:ledger:reservation_priced_from_contract_limits', f"permit {permit['reserved_micro_usd']}, admission {admission['reserved_micro_usd']}, expected {expected['reserved_micro_usd']}")
    return expected['reserved_micro_usd']


def stage_records(run):
    stage = run/'stages/proposal-1'
    def record(path):
        if not path.exists(): return None
        try: value = json.loads(path.read_bytes())
        except (ValueError, OSError): return None
        return value if isinstance(value, dict) else None
    return record(stage/'proposal-1.process.json'), record(stage/'output/http.json'), (stage/'command.json').exists()


def read_grant(directory, permit, rules):
    """The ledger's grant reader, with the revision's grant domain."""
    final = Path(directory)/ledger.GRANT_FILE
    if not final.exists(): return None
    try: record = json.loads(final.read_bytes())
    except (ValueError, OSError): raise ledger.Failure('campaign_grant_unreadable')
    if not (isinstance(record, dict) and record.get('domain') == rules['grant_domain'] and record.get('reservation_id') == permit['reservation_id']
            and record.get('policy_sha256') == permit['policy_sha256'] and record.get('episode_id') == permit['episode_id']
            and record.get('request_sha256') == permit['request_sha256']): raise ledger.Failure('campaign_grant_binding')
    return record


def disposition(a, run, name, kind, rules, permit, reconciliation, book):
    """Termination and the expected row kind from the hash-bound evidence, not from the row's own flags."""
    process, http, launched = stage_records(run); slot = book.grant_slot(permit)
    try: grant_state = 'present' if read_grant(slot, permit, rules) is not None else 'absent'
    except ledger.Failure as error: grant_state = error.code
    terminated = ledger.termination_established(process)
    unsent = http is None or (http.get('body_sends_started') == 0 and http.get('header_sends_started') == 0)
    if grant_state == 'present': expected = 'send_grant'
    elif grant_state != 'absent': expected = 'unknown'
    elif not launched and process is None and http is None: expected = 'release'
    elif terminated and unsent: expected = 'release'
    else: expected = 'unknown'
    a.require(reconciliation['kind'] == expected == TERMINAL_KIND[kind] and reconciliation['termination_established'] is terminated and reconciliation['launched'] is launched,
              f'{name}:ledger:disposition_derived', f'derived {expected} (grant {grant_state}, terminated {terminated}, launched {launched}), recorded {reconciliation["kind"]}')


def slot_contents(a, run, name, rules, permit, reconciliation, book):
    """The authoritative slot beside the ledger: exactly the expected marker, bound to the reservation and the terminal row, equal to the run's copy."""
    slot = book.grant_slot(permit); retained_dir = run/'stages/proposal-1/grant'
    files = sorted(p.name for p in slot.iterdir()) if slot.is_dir() else None
    expected = {'send_grant': ['send-grant.json'], 'release': ['release.json'], 'unknown': ['unknown.json']}[reconciliation['kind']]
    if reconciliation.get('torn_marker'): expected = sorted(set(expected+[reconciliation['torn_marker']]))
    same = files == expected and all((retained_dir/f).is_file() and (retained_dir/f).read_bytes() == (slot/f).read_bytes() for f in expected)
    if reconciliation['kind'] == 'send_grant':
        try: bound = read_grant(slot, permit, rules) == reconciliation['grant']
        except ledger.Failure: bound = False
        bound = bound and reconciliation.get('marker_sha256') == sha((slot/ledger.GRANT_FILE).read_bytes())
    else:
        receipt_name = reconciliation['kind']+'.json'
        try: marker = load(slot/receipt_name) if same else None
        except ValueError: marker = None
        bound = same and isinstance(marker, dict) and marker.get('kind') == reconciliation['kind'] and marker.get('reservation_id') == permit['reservation_id'] \
                and isinstance(marker.get('reconciled_at_unix'), int) and reconciliation.get('marker_sha256') == sha((slot/receipt_name).read_bytes())
    a.require(same and bound and slot.parent == book.slot(permit['task_id'], permit['draw']), f'{name}:slot:authoritative_matches_retained',
              f'slot {files}, expected {expected}, bound {bound}')


def mounts(a, run, name, sp, task, draw, permit, book):
    """The sender's authority came from the campaign's ledger file (read-only), this reservation's slot (writable), the retained contract and instruction."""
    command = load(run/'stages/proposal-1/command.json'); argv = command['argv']
    def source(guest, flag):
        hits = [i for i, x in enumerate(argv) if x == guest and i >= 2 and argv[i-2] == flag]
        return argv[hits[0]-1] if len(hits) == 1 else None
    def option(flag):
        hits = [i for i, x in enumerate(argv) if x == flag]
        return argv[hits[0]+1] if len(hits) == 1 and hits[0]+1 < len(argv) else None
    ledger_src, grant_src = source('/ledger.ndjson', '--ro-bind'), source('/grant', '--bind')
    root = ledger_src[:-len(sp['ledger_path'])] if ledger_src and ledger_src.endswith(sp['ledger_path']) else None
    run_dir = command['run']
    # The recorded repository layout: the root is the directory whose campaign ledger the sender mounted; every module the sender ran came
    # from that root, the driver recorded the same files as its roles, and the retained provenance copies are those files (modules:*).
    roles = load(run/'provenance/roles.json')
    runtime = [i for i, x in enumerate(argv) if x == roles['runtime_path'] and i >= 1 and argv[i-1] == '--ro-bind']
    ok = (root is not None and grant_src == f"{root}{sp['ledger_slots']}/{task.id}/{draw}/{permit['reservation_id']}" and command['grant_slot'] == grant_src
          and Path(ledger_src).name == book.path.name and Path(grant_src).parent.parent.parent.name == book.slots.name
          and source('/policy.json', '--ro-bind') == run_dir+'/transport-policy.json' and source('/permit.json', '--ro-bind') == run_dir+'/campaign-permit.json'
          and source('/contract.json', '--ro-bind') == run_dir+'/transport-contract.json' and source('/instruction.txt', '--ro-bind') == run_dir+'/transport-instruction.txt'
          and source('/arguments.json', '--ro-bind') == run_dir+'/transport-arguments.json' and source('/request.json', '--ro-bind') == run_dir+'/transport-request.json'
          and source('/pricing-sources', '--ro-bind') == run_dir+'/transport-pricing-sources'
          and all(source(guest, '--ro-bind') == root+module for guest, module in MODULE_MOUNTS.items())
          and roles['actor_source'] == root+'cohort_https.py' and roles['ledger_module'] == root+'cohort_ledger.py' and roles['network_stage'] == root+'campaign_network.py'
          and roles['ledger_directory'] == root+'ledgers/campaigns' and roles['contract'] == root+'contracts/farkas-proposal-contract-v1.json'
          and len(runtime) == 1 and roles['python'] in argv and command['records'] == run_dir+'/stages/proposal-1'
          and source('/out', '--bind') == command['records']+'/output' and source('/grant', '--ro-bind') is None and source('/ledger.ndjson', '--bind') is None
          and argv.count('--bind') == 2 and option('--task') == task.id and option('--draw') == str(draw) and option('--episode') == name
          and option('--contract') == '/contract.json' and option('--instruction') == '/instruction.txt' and option('--permit') == '/permit.json'
          and option('--ledger') == '/ledger.ndjson' and option('--grant') == '/grant' and option('--mode') == 'rehearsal')
    a.require(ok, f'{name}:mounts:authority_bound', f'ledger {ledger_src}, grant {grant_src}')
    return root


def command_reconstructed(a, run, name, sp, policy, task, draw, permit, http, root):
    """The whole recorded sender command, rebuilt from the pinned runtime record, the recorded repository root and this run's own paths, compared
    exactly: every library mount is the pinned inventory's, the stdlib is the materialization of the pin under that root, the interpreter is the
    pinned one, the module and record mounts are the frozen population, the only unconstrained sources are the four ephemeral credential/TLS
    files, and nothing else is mounted. No original directory needs to exist."""
    command = load(run/'stages/proposal-1/command.json'); argv = command['argv']; run_dir = command['run']; roles = load(run/'provenance/roles.json')
    pin_path = run/'provenance/cohort-harness/policies'/(RUNTIME_PIN+'.json'); pin = load(pin_path)
    pinned = sha(pin_path.read_bytes()) == policy['runtime_lock_sha256'] and load(run/'provenance/python-runtime.json') == pin and roles['runtime_pin'] == RUNTIME_PIN \
             and load(run/'provenance/binaries.json').get(pin['python']) == pin['python_sha256'] and roles['python'] == pin['python']
    stdlib_source = f"{root}.cache/campaign-runtime/{policy['runtime_lock_sha256']}/stdlib"
    pinned = pinned and roles['runtime_path'] == stdlib_source
    libraries = [x for lib in sorted(pin['libraries'], key=lambda l: l['guest']) for x in ('--ro-bind', lib['host'], lib['guest'])]
    modules = [x for guest, module in (('/adapter.py', 'cohort_https.py'), ('/live_https.py', 'live_https.py'), ('/pricing_gate_v2.py', 'pricing_gate_v2.py'),
                                       ('/pricing_gate_v3.py', 'pricing_gate_v3.py'), ('/campaign_ledger.py', 'campaign_ledger.py'), ('/cohort_ledger.py', 'cohort_ledger.py'))
               for x in ('--ro-bind', root+module, guest)]
    records = [x for file, guest in (('transport-policy.json', '/policy.json'), ('transport-contract.json', '/contract.json'), ('transport-instruction.txt', '/instruction.txt'),
                                     ('transport-arguments.json', '/arguments.json'), ('transport-request.json', '/request.json'),
                                     ('transport-pricing-sources', '/pricing-sources'), ('campaign-permit.json', '/permit.json'))
               for x in ('--ro-bind', run_dir+'/'+file, guest)]
    # the four ephemeral sources are taken from the record itself, after checking they are the only unconstrained mounts and are well formed
    def source(guest):
        hits = [i for i, x in enumerate(argv) if x == guest and i >= 2 and argv[i-2] == '--ro-bind']
        return argv[hits[0]-1] if len(hits) == 1 else None
    ephemeral = {guest: source(guest) for guest in EPHEMERAL}
    tls = [ephemeral[g] for g in ('/ca.pem', '/server.pem', '/server.key')]
    ephemeral_ok = (all(isinstance(v, str) and v.startswith('/') for v in ephemeral.values())
                    and all(Path(v).name == g[1:] for g, v in ephemeral.items() if g != '/credential')
                    and len({str(Path(v).parent) for v in tls}) == 1 and not any(v.startswith((root, run_dir)) for v in ephemeral.values()))
    expected = (SENDER_PREFIX + libraries + ['--ro-bind', stdlib_source, pin['stdlib']] + modules + records
                + ['--ro-bind', root+sp['ledger_path'], '/ledger.ndjson', '--ro-bind', run_dir+'/canned-provider.json', '/fixture.json']
                + [x for g in EPHEMERAL for x in ('--ro-bind', ephemeral[g] or '', g)]
                + ['--ro-bind', pin['python'], '/runner/bin/program', '--bind', run_dir+'/stages/proposal-1/output', '/out',
                   '--bind', f"{root}{sp['ledger_slots']}/{task.id}/{draw}/{permit['reservation_id']}", '/grant', '/runner/bin/program',
                   '-I', '-S', '-B', '/adapter.py', '--mode', 'rehearsal', '--policy', '/policy.json', '--contract', '/contract.json', '--instruction', '/instruction.txt',
                   '--arguments', '/arguments.json', '--credential-file', '/credential', '--ca', '/ca.pem', '--out', '/out', '--request', '/request.json',
                   '--sources', '/pricing-sources', '--permit', '/permit.json', '--ledger', '/ledger.ndjson', '--episode', name, '--task', task.id, '--draw', str(draw),
                   '--grant', '/grant', '--commitment-nonce', http['commitment_nonce'], '--fixture', '/fixture.json', '--server-cert', '/server.pem', '--server-key', '/server.key'])
    first = next((i for i, (x, y) in enumerate(zip(argv, expected)) if x != y), min(len(argv), len(expected)) if len(argv) != len(expected) else None)
    a.require(pinned and ephemeral_ok and argv == expected, f'{name}:command:reconstructed_from_pinned_runtime_and_layout',
              f'pinned {pinned}, ephemeral {ephemeral_ok}, first difference at {first}: {argv[first:first+3] if first is not None else None}')


def receipts(a, run, name, rows, policy):
    started = [r['payload'] for r in rows if r['stage'] == 'proposal-1' and r['event'] == 'stage_started']
    finished = [r['payload'] for r in rows if r['stage'] == 'proposal-1' and r['event'] == 'stage_finished']
    process = load(run/'stages/proposal-1/proposal-1.process.json'); command = load(run/'stages/proposal-1/command.json')
    a.require(len(started) == 1 and len(finished) == 1 and finished[0] == process and started[0]['command_file'] == 'stages/proposal-1/command.json'
              and command['network_namespace'] == 'unshared' and '--unshare-net' in command['argv'] and '/grant' in command['argv'],
              f'{name}:receipts:single_pair_bound_to_process')
    # The driver continued past the sender only because the stage returned: zero exit, no exhaustion or violation, monitor and observation
    # succeeded, the workload was gone — under the frozen resource limits, which the command and the start receipt both name.
    limits = policy['limits']
    a.require(process['exit_code'] == 0 and process['resource_exhausted'] is None and process['resource_violations'] == [] and process['monitor_error'] is None
              and process['observation_error'] is None and process['workload_empty_after_cleanup'] is True and process['accounting_scope'] == 'sandbox_process_tree'
              and command['wall_seconds'] == limits['request_wall_seconds'] and command['cpu_seconds'] == limits['request_cpu_seconds']
              and command['memory_bytes'] == limits['request_memory_bytes'] and command['output_bytes'] == limits['request_output_bytes']
              and command['capture_events'] is False and command['stage'] == 'proposal-1' and process['output_bytes'] <= command['output_bytes']
              and started[0]['wall_limit_seconds'] == command['wall_seconds'] and started[0]['cpu_limit_seconds'] == command['cpu_seconds']
              and started[0]['memory_limit_bytes'] == command['memory_bytes'],
              f'{name}:receipts:stage_returned_within_frozen_limits', f"exit {process['exit_code']}, limits {started[0]}")


def stage_outcomes(a, run, name, kind, policy):
    """The driver reached this outcome only because every stage on its frozen path returned: the retained stage population is exactly the path's,
    and each process record shows a zero exit, no exhaustion or violation, monitor and observation success and an empty workload — under the
    sender's policy limits or the frozen build/replay defaults."""
    present = sorted(p.name for p in (run/'stages').iterdir() if p.is_dir()) if (run/'stages').is_dir() else []
    defaults = {k: v.default for k, v in inspect.signature(episode.stage).parameters.items() if k in ('wall', 'cpu', 'memory', 'output_limit')}
    limits = policy['limits']; problems = []
    if present != sorted(STAGES[kind]): problems.append(f'stages {present}')
    for stage in STAGES[kind]:
        if stage not in present: continue
        process = load(run/'stages'/stage/(stage+'.process.json')); cmd = load(run/'stages'/stage/'command.json')
        returned = (process['exit_code'] == 0 and process['resource_exhausted'] is None and process['resource_violations'] == [] and process['monitor_error'] is None
                    and process['observation_error'] is None and process['workload_empty_after_cleanup'] is True and process['accounting_scope'] == 'sandbox_process_tree'
                    and process['output_bytes'] <= cmd['output_bytes'] and cmd['stage'] == stage and cmd['records'] == cmd['run']+'/stages/'+stage)
        if stage == 'proposal-1':
            bounded = (cmd['wall_seconds'], cmd['cpu_seconds'], cmd['memory_bytes'], cmd['output_bytes']) == \
                      (limits['request_wall_seconds'], limits['request_cpu_seconds'], limits['request_memory_bytes'], limits['request_output_bytes']) and cmd['capture_events'] is False
        else:
            bounded = (cmd['wall_seconds'], cmd['cpu_seconds'], cmd['memory_bytes'], cmd['output_bytes']) == \
                      (defaults['wall'], defaults['cpu'], defaults['memory'], defaults['output_limit']) and cmd['capture_events'] is (stage == 'reconstruct')
        if not (returned and bounded): problems.append(f"{stage} exit {process['exit_code']} returned {returned} bounded {bounded}")
    a.require(not problems, f'{name}:stages:every_stage_on_the_path_returned', '; '.join(problems))


def payload_receipts(a, run, name, kind, rows, sp, task, permit, reconciliation, http, admission):
    """Every supervisor receipt in the chain is reconstructed from the record it names and compared exactly; presence and order are not meaning."""
    _, frozen = r6.frozen_task(task); nonce = load(run/'credential-canary.json')['nonce']; problems = []
    def expect(stage, event, value, drop=()):
        hits = [r['payload'] for r in rows if r['source'] == 'supervisor' and r['stage'] == stage and r['event'] == event]
        got = [{k: v for k, v in h.items() if k not in drop} for h in hits]
        if got != [value]: problems.append(f'{stage}/{event}')
    for stage in sorted(p.name for p in (run/'stages').iterdir() if p.is_dir()):
        cmd = load(run/'stages'/stage/'command.json')
        expect(stage, 'stage_started', {'command_file': f'stages/{stage}/command.json', 'cpu_limit_seconds': cmd['cpu_seconds'],
                                        'memory_limit_bytes': cmd['memory_bytes'], 'wall_limit_seconds': cmd['wall_seconds']}, drop=('cgroup',))
        expect(stage, 'stage_finished', load(run/'stages'/stage/(stage+'.process.json')))
    expect('episode', 'episode_started', {'policy_sha256': sha((run/'search-policy.json').read_bytes()), 'challenge_sha256': frozen['challenge_sha256'], 'nonce': nonce, 'mode': 'rehearsal'})
    expect('payload', 'payload_validated', {'client_arguments_sha256': sha((run/'client-arguments.json').read_bytes()), 'messages_sha256': sha((run/'messages.json').read_bytes()),
                                            'payload_audit_sha256': sha((run/'payload-audit.json').read_bytes()), 'prompt_sha256': sha((run/'prompt.txt').read_bytes()),
                                            'request_sha256': sha((run/'request.json').read_bytes())})
    expect('live-payload', 'payload_validated', {'arguments_sha256': sha((run/'live-arguments.json').read_bytes()), 'contract_sha256': sp['contract_sha256'],
                                                 'messages_sha256': sha((run/'live-messages.json').read_bytes()), 'policy_sha256': sp['config_sha256'],
                                                 'preparation_request_sha256': sha((run/'request.json').read_bytes()), 'prepared_sha256': sha((run/'prepared.json').read_bytes()),
                                                 'prompt_sha256': sha((run/'prompt.txt').read_bytes()), 'request_sha256': sha((run/'live-request.json').read_bytes())}, drop=('inner_binding',))
    expect('credential-receipt', 'credential_receipt_checked', load(run/'credential-receipt.json'))
    if kind == 'refused':
        attempts = [r['payload'] for r in rows if r['event'] == 'reservation_attempted']
        if not (len(attempts) == 1 and isinstance(attempts[0].get('attempt_id'), str) and len(attempts[0]['attempt_id']) == 64): problems.append('campaign-ledger/reservation_attempted')
        expect('campaign-ledger', 'reservation_refused', admission)
    else:
        out = run/'stages/proposal-1/output'
        expect('campaign-ledger', 'reservation_attempted', {'attempt_id': permit['attempt_id']})
        expect('pricing-admission', 'pricing_admitted', {'admission_sha256': sha((run/'host-pricing-admission.json').read_bytes())})
        expect('campaign-ledger', 'request_reserved', load(run/'reservation.json'))
        expect('campaign-ledger', 'reservation_reconciled', {'kind': reconciliation['kind'], 'reservation_id': reconciliation['reservation_id'], 'row_hash': reconciliation['row_hash'],
                                                             'send_outcome': reconciliation.get('send_outcome'), 'termination_established': reconciliation['termination_established'],
                                                             'record_read_failures': len(reconciliation['evidence']['record_read_failures']), 'evidence_write_failures': [],
                                                             'ledger_sha256': sha((run/'ledger-after.ndjson').read_bytes()), 'recovered': None})
        expect('proposal', 'https_observed', {'http_sha256': sha((out/'http.json').read_bytes()), 'server_sha256': sha((out/'server.json').read_bytes()),
                                              'pricing_check_sha256': sha((out/'pricing-check.json').read_bytes())})
        expect('proposal', 'transport_validated', load(run/'transport-validation.json'))
    if kind == 'proof':
        verdict = load(run/'verdict.json')
        expect('validation-local', 'kernel_verdict', verdict['final_validation']['local']); expect('validation-whole', 'kernel_verdict', verdict['final_validation']['whole'])
    a.require(not problems, f'{name}:receipts:payloads_bound_to_records', 'receipts differ from their records: '+', '.join(problems))


def seal(a, run, name):
    if not (run/'seal.json').exists(): a.require(False, f'{name}:seal:retained_hashes', 'run is not sealed')
    s = load(run/'seal.json')
    present = {str(p.relative_to(run)) for p in run.rglob('*') if p.is_file()}
    mismatched = [k for k, v in s['retained_sha256'].items() if not (run/k).is_file() or sha((run/k).read_bytes()) != v]
    unlisted = sorted(present-set(s['retained_sha256'])-set(s['ephemeral_sha256'])-{'seal.json'})
    a.require(not mismatched and s['retained_sha256'] and not unlisted, f'{name}:seal:retained_hashes', f'{len(mismatched)} differ; unlisted {unlisted[:3]}')
    return s


def publication_recomputed(a, run, name):
    """The frozen scanner over these bytes, not a flag: the retained report must be clean, describe these exact bytes
    (events.ndjson by its pre-terminal prefix), and be clean again now."""
    nonce = load(run/'credential-canary.json')['nonce']; canary = credential.derive(nonce)
    retained_report = load(run/'publication-scan.json'); final = load(run/'publication-final.json')
    fresh = publication.scan([run], canary, nonce)
    lines = (run/'events.ndjson').read_bytes().splitlines(True); prefix = b''.join(lines[:-1])
    entries = [e for e in retained_report['inventory'] if e['path']]
    paths = [e['path'] for e in entries]
    def describes(e):
        if e['path'] == 'events.ndjson': return e['sha256'] == sha(prefix) and e['bytes'] == len(prefix)
        p = run/e['path']; return p.is_file() and e['sha256'] == sha(p.read_bytes()) and e['bytes'] == p.stat().st_size
    fresh_streams = {e['path']: e['streams'] for e in fresh['inventory'] if e['path']}
    well_formed = all(e['scanned'] is True and e['error'] is None and e['findings'] == [] and 'raw' in e['streams']
                      and fresh_streams.get(e['path']) == e['streams'] for e in entries)
    a.require(retained_report['accepted'] is True and retained_report['disclosures'] == [] and retained_report['incompletely_scanned'] == []
              and retained_report['unreadable_directories'] == [] and retained_report['irregular_entries'] == []
              and len(paths) == len(set(paths)) == retained_report['files_scanned'] == len(retained_report['inventory'])
              and retained_report['gzip_streams_scanned'] == sum('gzip' in e['streams'] for e in entries)
              and retained_report['canary_nonce'] == nonce and well_formed and all(describes(e) for e in entries)
              and fresh['accepted'] is True and fresh['disclosures'] == []
              and {e['path'] for e in fresh['inventory'] if e['path']}-set(paths) <= {'publication-scan.json', 'publication-final.json', 'seal.json'}
              and final == publication.final_record(run/'publication-scan.json', canary, nonce),
              f'{name}:publication:recomputed')
    return retained_report, final


def terminal(a, run, name, kind, rows, report, final):
    summary = load(run/'credential-summary.json'); last = rows[-1]['payload']; acct = load(run/'accounting.json')
    publication_ok = bool(report['accepted'] and final['report_clean'])
    # evidence completion derived from the artifacts themselves, then every mirror compared with it
    if kind == 'refused':
        derived = (not (run/'campaign-permit.json').exists() and not (run/'campaign-reconciliation.json').exists() and not (run/'stages/proposal-1').exists()
                   and summary['reservation_state'] == 'not_reserved' and summary['ledger_reconciled'] is True)
    else:
        derived = ((run/'campaign-reconciliation.json').exists() and (run/'ledger-after.ndjson').exists() and (run/'stages/proposal-1/grant').is_dir()
                   and any(r['event'] == 'reservation_reconciled' for r in rows) and summary['reservation_state'] == 'reserved' and summary['ledger_reconciled'] is True)
    mirrors = (summary['evidence_complete'] is derived and acct['evidence_complete'] is derived and last['evidence_complete'] is derived
               and summary['reconciliation_evidence_complete'] is acct['reconciliation_evidence_complete']
               and summary['reservation_state'] == acct['reservation_state'] and summary['ledger_reconciled'] is acct['ledger_reconciled'])
    evidence_ok = derived and bool(summary['ledger_reconciled'])
    accepted = bool(summary['proof_accepted'] and summary['credential_use_accepted'] and publication_ok and evidence_ok)
    completed = summary['proof_accepted'] and summary['failure_category'] is None and publication_ok and evidence_ok
    a.require(mirrors and last['summary_sha256'] == sha((run/'credential-summary.json').read_bytes())
              and last['publication_scan_sha256'] == sha((run/'publication-scan.json').read_bytes())
              and last['publication_final_sha256'] == sha((run/'publication-final.json').read_bytes())
              and last['proof_accepted'] is bool(summary['proof_accepted']) and last['credential_use_accepted'] is bool(summary['credential_use_accepted'])
              and last['publication_accepted'] is publication_ok and last['publication_pending'] is False
              and last['ledger_reconciled'] is bool(summary['ledger_reconciled']) and last['accepted'] is accepted
              and rows[-1]['event'] == ('episode_finished' if completed else 'episode_rejected') and (kind == 'proof') == completed
              and publication.safe_record(last, driver.TERMINAL_KEYS),
              f'{name}:terminal:commitments_bound', 'evidence_complete mirrors disagree with the artifacts' if not mirrors else '')
    return accepted


def summary_bound(a, run, name, kind, task, draw, sp, contract_digest):
    """The summary is a mirror: its identity fields must name the task, draw, campaign, revision, contract and policy, and its embedded accounting must equal the audited file."""
    summary = load(run/'credential-summary.json'); acct = load(run/'accounting.json')
    a.require(summary['schema_version'] == 'r6-cohort-summary-1' and summary['task_id'] == task.id and summary['draw'] == draw
              and summary['campaign_id'] == sp['campaign_id'] and summary['revision'] == sp['revision'] and summary['contract_sha256'] == contract_digest
              and summary['search_policy'] == sp['name'] and summary['mode'] == sp['mode'] and summary['accounting'] == acct
              and summary['proof_accepted'] is (run/'verdict.json').exists() and summary['proof_accepted'] is (kind == 'proof')
              and summary['failure_category'] == {'proof': None, 'release': 'credential_format', 'refused': 'cohort_ledger'}[kind],
              f'{name}:summary:bound_to_audited_records', 'summary identity or embedded accounting differs from the audited records')


def chain_and_outcome(a, run, name, kind, rows, s, accepted):
    a.require(s['event_count'] == len(rows) and s['last_event_hash'] == rows[-1]['event_hash'] and s['accepted'] is accepted is (kind == 'proof'),
              f'{name}:seal:chain_and_outcome')


def grant(a, run, name, kind, permit, http, rules):
    slot = run/'stages/proposal-1/grant/send-grant.json'
    if kind == 'proof':
        try: g = read_grant(slot.parent, permit, rules)
        except ledger.Failure: g = None
        created, durable = http.get('grant_created_at_ns'), http.get('grant_durable_at_ns')
        a.require(g is not None and http['grant_committed'] is True and http['grant_id'] == g['grant_id'] and http['send_outcome'] == 'returned'
                  and created == g['at_ns'] and isinstance(durable, int) and http['grant_write_failed'] is False, f'{name}:grant:consistent_with_outcome',
                  'durable completion timestamp missing' if durable is None else '')
        a.require(http['tls_verified_at_ns'] < created <= durable < http['header_send_at_ns'] and http['connection_started_at_ns'] <= http['tls_verified_at_ns']
                  and http['permit_verified_at_ns'] < http['pricing_admitted_at_ns'] <= http['credential_read_at_ns'] < http['connection_started_at_ns'],
                  f'{name}:grant:ordered_before_first_header_byte')
    else:
        a.require(not slot.exists() and (http is None or (http['grant_committed'] is False and http['send_outcome'] == 'not_started'
                  and http['body_sends_started'] == 0 and http['header_sends_started'] == 0)), f'{name}:grant:consistent_with_outcome')


def actor_check(a, run, name, policy, contract_value, instruction, request_bytes, arguments, permit, body):
    out = run/'stages/proposal-1/output'; record = load(out/'pricing-check.json')
    try: derived = gate.admission(policy, contract_value, instruction, run/'transport-pricing-sources', arguments, request_bytes, record['evaluated_at_unix'])
    except gate.Failure as error: a.require(False, f'{name}:pricing:actor_check_rederived', error.code)
    a.require(record['accepted'] is True and {k: v for k, v in record.items() if k != 'admitted_at_ns'} == derived
              and record['reserved_micro_usd'] == permit['reserved_micro_usd'] == permit['reservation']['reserved_micro_usd']
              and record['body_sha256'] == sha((out/'serialized-body.json').read_bytes()) == sha(body)
              and 0 <= record['evaluated_at_unix']-permit['pricing_admission']['evaluated_at_unix'] <= policy['pricing_admission']['maximum_permit_age_seconds'],
              f'{name}:pricing:actor_check_rederived')


def transport(a, run, name, kind, policy, task, draw, permit, http, body, contract_digest):
    out = run/'stages/proposal-1/output'; serialized = (out/'serialized-body.json').read_bytes(); server = load(out/'server.json')
    # the bytes that were serialized, and where a send happened the bytes that left and the bytes the receiver captured, are the contract rendering
    sent = (out/'outbound-body.json').exists() or (out/'received-body.json').exists() or http['body_sends_started'] > 0
    a.require(serialized == body and (not sent or ((out/'outbound-body.json').read_bytes() == body and (out/'received-body.json').read_bytes() == body
                                                   and http['outbound_body_sha256'] == sha(body))) and sent is (kind == 'proof'),
              f'{name}:transport:bodies_are_the_contract_rendering')
    a.require(http['schema_version'] == 'r6-cohort-observation-1' and http['mode'] == 'rehearsal' and http['policy_sha256'] == sha((run/'transport-policy.json').read_bytes())
              and http['contract_sha256'] == contract_digest and http['task_id'] == task.id and http['draw'] == draw and http['slot'] == f'{task.id}/{draw}'
              and http['request_sha256'] == sha(serialized) and http['request_bytes'] == len(serialized) and http['retries'] == 0 and http['redirects_followed'] == 0
              and http['transport_scope'] == 'isolated_loopback_https_fixture' and http['endpoint'] == policy['endpoint']
              and http['reservation_id'] == permit['reservation_id'] and http['authorization_present_in_policy'] is None
              and http['maximum_response_bytes'] == policy['limits']['maximum_response_bytes'],
              f'{name}:transport:record_consistent')
    if kind == 'proof':
        nonce = load(run/'credential-canary.json')['nonce']; header = credential.header(credential.derive(nonce))
        a.require(http['http_status'] == 200 and http['body_sends_returned'] == 1 and http['body_sends_started'] == 1 and http['header_sends_started'] == 1
                  and len(server['requests']) == 1 and server['requests'][0]['body_sha256'] == sha(body)
                  and server['requests'][0]['authorization_sha256'] == sha(header.encode()) and server['server_names'] == [policy['endpoint']['host']]
                  and http['tls']['verified'] is True and http['tls']['server_hostname'] == policy['endpoint']['host']
                  and http['response_sha256'] == sha((out/'provider-response.json').read_bytes()),
                  f'{name}:transport:local_send_and_remote_receipt')
    return serialized


def commitment(a, run, name, http):
    nonce = load(run/'credential-canary.json')['nonce']; header = credential.header(credential.derive(nonce))
    expected = sha((COMMITMENT_DOMAIN+':'+http['commitment_nonce']+':'+header).encode())
    text = (run/'stages/proposal-1/output/http.json').read_text()
    if http['failure_category'] == 'credential_format':
        a.require(http['credential_commitment_sha256'] is None and 'Bearer' not in text, f'{name}:commitment:bound_to_mounted_canary')
    else:
        a.require(http['credential_commitment_sha256'] == expected and credential.derive(nonce) not in text, f'{name}:commitment:bound_to_mounted_canary')


def interpretation(a, run, name, request_bytes):
    out = run/'stages/proposal-1/output'
    proposed, text, metadata, validation, error = budget.interpret(out, request_bytes, False)
    same_text = (text is None and not (run/'response.json').exists()) or (text is not None and (run/'response.json').read_bytes() == text)
    a.require(validation == load(run/'transport-validation.json') and metadata == load(run/'provider-metadata.json') and same_text
              and (error is None) == (validation['failure_category'] is None), f'{name}:interpretation:reproduced')


def slot_identity(a, run, name, sp, task, draw, permit, http, body):
    text = body.decode()
    a.require(http['slot'] == f'{task.id}/{draw}' and http['task_id'] == task.id and http['draw'] == draw and http['reservation_id'] == permit['reservation_id']
              and not any(needle in text for needle in (permit['reservation_id'], permit['attempt_id'], sp['campaign_id'], sp['config_sha256'], http['commitment_nonce'],
                                                        http.get('grant_id') or 'grant_id', 'draw', 'slot', 'campaign', 'revision')),
              f'{name}:slot:identity_in_receipts_not_in_model_bytes')


def accounting(a, run, name, kind, policy, http, permit, reconciliation):
    acct = load(run/'accounting.json'); out = run/'stages/proposal-1/output'
    server = load(out/'server.json') if (out/'server.json').exists() else None
    if kind == 'refused':
        lifecycle = {'permit': None, 'reservation': None, 'reconciliation': None, 'reconcile_error': None, 'reservation_state': 'not_reserved', 'evidence_write_failures': []}
    else:
        lifecycle = {'permit': permit, 'reservation': load(run/'reservation.json'), 'reconciliation': reconciliation, 'reconcile_error': None,
                     'reservation_state': 'reserved', 'evidence_write_failures': []}
    expected = driver.accounting_for(run, policy, False, http, server, lifecycle)
    a.require(acct == expected and acct['allowance_consumed'] == {'proof': 1, 'release': 0, 'refused': None}[kind], f'{name}:accounting:recomputed')
    r = load(run/'credential-receipt.json'); nonce = load(run/'credential-canary.json')['nonce']
    expected_header = sha(credential.header(credential.derive(nonce)).encode())
    observed = server['requests'][0]['authorization_sha256'] if kind == 'proof' else None
    a.require(r['schema_version'] == 'r6-credential-receipt-1' and r['channel'] == 'private_read_only_file' and r['declared_case'] == 'rehearsal'
              and r['exact_receipt'] is (kind == 'proof') and r['transmissions'] == (len(server['requests']) if server else 0) == (1 if kind == 'proof' else 0)
              and r['authorization_present'] is (kind == 'proof') and r['expected_authorization_sha256'] == expected_header
              and r['observed_authorization_sha256'] == observed and (observed == expected_header) is (kind == 'proof'),
              f'{name}:credential_receipt:recorded')


def failure(a, run, name, http):
    summary = load(run/'credential-summary.json')
    stderr = (run/'stages/proposal-1/proposal-1.stderr').read_text(); process = load(run/'stages/proposal-1/proposal-1.process.json')
    a.require(summary['failure_category'] == 'credential_format' and summary['failure_phase'] == 'credential_delivery' and http['failure_category'] == 'credential_format'
              and process['exit_code'] == 0 and stderr == '' and http['connection_attempts'] == 0 and http['http_status'] is None
              and load(run/'stages/proposal-1/output/pricing-check.json')['accepted'] is True and not (run/'response.json').exists()
              and (run/'seal.json').exists(), f'{name}:failure:classified_and_finalized')


def refusal(a, run, name, rows, admission):
    """Refused before any reservation: the denial is the ledger's own code, the receipt mirrors it, and nothing downstream exists."""
    refused = [r['payload'] for r in rows if r['event'] == 'reservation_refused']
    a.require(len(refused) == 1 and refused[0] == admission and not (run/'campaign-permit.json').exists() and not (run/'reservation.json').exists()
              and not (run/'transport-ledger.ndjson').exists() and not (run/'ledger-after.ndjson').exists() and not (run/'stages/proposal-1').exists()
              and not (run/'campaign-reconciliation.json').exists() and not (run/'transport-request.json').exists()
              and load(run/'credential-summary.json')['error'] == 'Campaign ledger: cohort_slot_consumed',
              f'{name}:refusal:slot_consumed_before_reservation')


def proof(a, run, name, rows, task, sp, request_bytes):
    response, validated = load(run/'response.json'), load(run/'validated-response.json'); out = run/'stages/proposal-1/output'
    raw = load(out/'provider-response.json')
    text = [c['text'] for item in raw['output'] if item.get('type') == 'message' for c in item['content'] if c.get('type') == 'output_text']
    a.require(response == validated and json.loads(''.join(text)) == response and response['request_sha256'] == sha(request_bytes) and raw['status'] == 'completed',
              f'{name}:proof:response_bound')
    evidence, cert, verdict = load(run/'evidence.json'), load(run/'certificate-verdict.json'), load(run/'verdict.json')
    assembled = next(r['payload'] for r in rows if r['event'] == 'certificate_assembled')
    a.require(evidence['certificate']['payload']['witness_data'] == response['witness'] and cert['accepted'] is True and cert['reason']['kind'] == 'verified_farkas'
              and cert['certificate_hash'] == 'sha256:'+assembled['certificate_sha256'] and assembled['response_sha256'] == sha((run/'validated-response.json').read_bytes())
              and cert == next(r['payload'] for r in rows if r['event'] == 'independent_certificate_verdict') and verdict['certificate_validation'] == cert
              and verdict['request_sha256'] == sha(request_bytes) and load(run/'stages/assembly/output/evidence.json') == evidence
              and verdict['schema_version'] == 'r6-cohort-proof-1' and verdict['search_policy'] == sp['name'] and verdict['mode'] == 'rehearsal',
              f'{name}:proof:certificate_bound')
    named = {r['event']: (r['payload'].get('proposer', r['payload'].get('witness_proposer')), r['payload'].get('route'), r['payload'].get('consumer_route'))
             for r in rows if r['event'] in ('recovery_started', 'certificate_assembled', 'recovery_finished')}
    a.require(named == {'recovery_started': ('canned_provider_response', sp['name'], None),
                        'certificate_assembled': ('canned_provider_response', None, 'openai_responses_http_fixture_v1'),
                        'recovery_finished': ('canned_provider_response', sp['name'], 'openai_responses_http_fixture_v1')}
              and verdict['witness_proposer'] == 'canned_provider_response' and verdict['consumer_route'] == 'openai_responses_http_fixture_v1'
              and assembled['certificate_assembler'] == verdict['certificate_assembler'] == 'sdk_proposal_assembler_v1',
              f'{name}:proof:attribution_passed_through', str(named))
    def receipt(stage, event):
        hits = [r['payload'] for r in rows if r['source'] == 'supervisor' and r['stage'] == stage and r['event'] == event]
        if len(hits) != 1: raise ValueError(f'{stage}/{event}: {len(hits)} receipts')
        return hits[0]
    read = lambda n: load(run/n)
    try:
        _, expected = r6.frozen_task(task); challenge = json.loads(request_bytes)['binding']['challenge_sha256']
        context = read('stages/reconstruct/output/context.json')
        if not (context == read('stages/preparation/output/context.json') == load(task.path/'context/local-context.json')):
            raise ValueError('reconstruction context differs from the frozen context')
        validated_ctx = receipt('reconstruct', 'context_validated')
        if not (validated_ctx['captured_context_sha256'] == sha((run/'stages/reconstruct/output/context.json').read_bytes())
                and validated_ctx['frozen_context_sha256'] == sha((task.path/'context/local-context.json').read_bytes())):
            raise ValueError('context receipt does not name the captured and frozen context bytes')
        if verdict['task_id'] != task.id or verdict['manifest_sha256'] != sha((task.path/'manifest.json').read_bytes()) \
                or not (verdict['challenge_sha256'] == expected['challenge_sha256'] == challenge):
            raise ValueError('target identity differs (task, manifest or challenge)')
        envelope_proof_audit.audit(task, evidence, verdict, rows, lambda n: run/n, read, receipt)
    except (ValueError, AssertionError, KeyError, OSError, gzip.BadGzipFile, EOFError) as error:
        a.require(False, f'{name}:proof:shared_checker', str(error))
    a.require(True, f'{name}:proof:shared_checker')
    proved = next(r['payload'] for r in rows if r['event'] == 'proof_validated')
    a.require(proved['proof_accepted'] is True and proved['solution_sha256'] == verdict['solution_sha256'] == CANNED_EXPORTS[task.id]
              and proved['verdict_sha256'] == sha((run/'verdict.json').read_bytes()) and verdict['local_obligation_closed'] is True
              and verdict['whole_declaration_validated'] is True and verdict['axiom_delta'] and all(v == {'added': [], 'removed': []} for v in verdict['axiom_delta'].values()),
              f'{name}:proof:export_expected')


def cross_run(a, root, ledgers, expected, sp_by_run, policies, bodies, sent, identities, permits, reconciliations, admissions, priced, contract_digest):
    names = sorted(expected)
    campaign_ids = {sp['campaign_id'] for sp in sp_by_run.values()}
    a.require(len(campaign_ids) == 1, 'campaign:single_identity', str(campaign_ids))
    campaign = next(iter(campaign_ids))
    # revisions: distinct policy digests, chained by previous_policy_sha256, one lock, one contract, one campaign, one schedule
    revisions = sorted({r for (_, _, _, r) in expected.values()}); digests = {}
    for n in names:
        digests.setdefault(expected[n][3], set()).add(sp_by_run[n]['config_sha256'])
    ok = revisions == list(range(1, len(revisions)+1)) and len(revisions) >= 2 and all(len(digests[r]) == 1 for r in revisions)
    ordered = [next(iter(digests[r])) for r in revisions]; ok = ok and len(set(ordered)) == len(ordered)
    for r in revisions:
        p = policies[r]; q = policies[r-1] if r > 1 else None
        ok = ok and p['revision'] == r and (q is None or (p['previous_policy_sha256'] == ordered[r-2] and p['campaign']['id'] == q['campaign']['id']
                                                          and p['contract_sha256'] == q['contract_sha256'] and p['source_lock_sha256'] == q['source_lock_sha256']
                                                          and p['campaign']['schedule'] == q['campaign']['schedule'] and p['name'] == q['name']
                                                          and p['pricing_sources'] != q['pricing_sources']))
    a.require(ok, 'revisions:chained_distinct_policies_same_lock', str(digests))
    # identical model input per task across revisions: the serialized bytes of every run of the task, the sent bytes where a send happened,
    # and the contract rendering of the regenerated request are one byte string
    for task_id in sorted(bodies):
        group = bodies[task_id]; distinct = {sha(b) for b in group.values()} | {sha(b) for b in sent.get(task_id, {}).values()}
        spanned = {expected[n][3] for n in group}
        a.require(len(distinct) == 1 and len(spanned) >= 2 and len(sent.get(task_id, {})) >= 2, f'input:identical_model_bytes_across_revisions:{task_id}',
                  f'{len(distinct)} distinct entity bodies across {sorted(group)}; revisions {sorted(spanned)}')
    if len(bodies) > 1:
        per_task = {t: sha(next(iter(g.values()))) for t, g in bodies.items()}
        a.require(len(set(per_task.values())) == len(per_task), 'input:distinct_model_bytes_across_tasks', str(per_task))
    ids = [v['reservation_id'] for v in identities.values()]; grants = [v['grant_id'] for v in identities.values() if v['grant_id']]
    nonces = [v['nonce'] for v in identities.values()]; attempts = [v['attempt_id'] for v in identities.values()]
    canaries = [load(root/n/'credential-canary.json')['nonce'] for n in names]
    a.require(all(len(set(x)) == len(x) for x in (ids, grants, nonces, attempts, canaries)) and len(grants) == sum(k == 'proof' for (k, *_) in expected.values()),
              'receipts:distinct_across_runs')
    # the authoritative ledger: chained, headed, every run's snapshots are prefixes of it, revision rows in order, nothing beyond the population
    book = ledger.Ledger(ledgers/campaign/'rehearsal', campaign)
    try:
        if not book.head.exists() or not book.path.exists(): raise ledger.Failure('cohort_ledger_missing')
        head = load(book.head); raw = book.path.read_bytes(); rows = ledger.parse(raw); s = ledger.state(rows, campaign)
        if not (head['rows'] == len(rows) and rows[-1]['row_hash'] == head['last_hash'] and head['campaign_id'] == campaign): raise ledger.Failure('cohort_ledger_head')
    except ledger.Failure as error: a.require(False, 'ledger:continuous_across_revisions', error.code)
    prefixes = all(rows[:len(snap)] == snap for n in names if expected[n][0] != 'refused'
                   for snap in (ledger.parse((root/n/'transport-ledger.ndjson').read_bytes()), ledger.parse((root/n/'ledger-after.ndjson').read_bytes())))
    revision_rows = [r for r in rows if r['kind'] in ('activation', 'authorization_revision')]
    reservation_rows = [r for r in rows if r['kind'] == 'reservation']; terminal_rows = [r for r in rows if r['kind'] in ledger.TERMINAL]
    def current_at(index):
        return [r for r in rows[:index] if r['kind'] in ('activation', 'authorization_revision')][-1]['policy_sha256']
    a.require(prefixes and [r['policy_sha256'] for r in revision_rows] == ordered and s['revisions'] == ordered and s['revision'] == len(ordered)-1
              and s['contract_sha256'] == contract_digest and s['open_reservations'] == [] and s['purpose'] == 'rehearsal'
              and sorted(r['row_hash'] for r in reservation_rows) == sorted(p['row_hash'] for p in permits.values())
              and sorted(r['row_hash'] for r in terminal_rows) == sorted(r['row_hash'] for r in reconciliations.values())
              and all(r['policy_sha256'] == current_at(r['sequence']) for r in reservation_rows)
              and all(r['authorization'] == contract.REHEARSAL_AUTHORIZATION for r in revision_rows) and not (ledgers/campaign/'live').exists(),
              'ledger:continuous_across_revisions', str([r['kind'] for r in rows]))
    consumed = {f'{t}/{d}' for (k, t, d, _) in expected.values() if k == 'proof'}
    released = {f'{t}/{d}' for (k, t, d, _) in expected.values() if k == 'release'}
    committed = sum(priced[n] for n in priced if expected[n][0] == 'proof')  # from the reservations checked against the rederived price, not the rows' own amounts
    a.require({k for k, v in s['slots'].items() if v['consumed']} == consumed and s['transmissions_consumed'] == len(consumed)
              and all(s['slots'][k]['released'] == sum(1 for (kk, t, d, _) in expected.values() if kk == 'release' and f'{t}/{d}' == k) for k in released)
              and s['committed_micro_usd'] == committed and s['maximum_transmissions'] == sum(contract.REHEARSAL_SCHEDULE.values()),
              'ledger:consumed_slots_persist', str(s['slots']))
    # every refusal names a slot consumed by an earlier revision's proof run, reconciled before the refusal was evaluated
    ok = True; bound = {}
    for n, (k, t, d, r) in expected.items():
        if k != 'refused': continue
        consumers = [m for m, (kk, tt, dd, rr) in expected.items() if kk == 'proof' and (tt, dd) == (t, d) and rr < r]
        ok = ok and len(consumers) == 1 and reconciliations[consumers[0]]['reconciled_at_unix'] <= admissions[n]['evaluated_at_unix'] \
             and s['slots'][f'{t}/{d}']['consumed'] and admissions[n]['failure_code'] == 'cohort_slot_consumed'
        bound[n] = consumers
    a.require(ok and bool(bound), 'ledger:refusals_bound_to_earlier_consumption', str(bound))
    return {'campaign_id': campaign, 'revisions': ordered, 'rows': len(rows), 'kinds': [r['kind'] for r in rows],
            'state': {k: s[k] for k in ('revision', 'revisions', 'transmissions_consumed', 'slots', 'committed_micro_usd')}}


def audit(root, ledgers, revision_name):
    population = POPULATIONS[revision_name]; expected = population['expected']; rules = RULES[revision_name]
    a = Audit(); result = {'runs': {}}
    names = sorted(expected); present = sorted(p.name for p in root.iterdir())
    a.require(present == names and all((root/n).is_dir() for n in present), 'population:exactly_expected_runs', str(present))
    contract_value = load(ROOT/'contracts/farkas-proposal-contract-v1.json'); contract_digest = gate.check_contract(contract_value)
    tasks = {t: r6.get_task(t) for t in sorted({t for (_, t, _, _) in expected.values()})}
    a.require(all(load(root/n/'search-policy.json')['manifest_sha256'] == sha((tasks[expected[n][1]].path/'manifest.json').read_bytes()) for n in names), 'tasks:manifests_bound')
    result['modules'] = modules(a, root, names, revision_name)
    sp_by_run, policies, bodies, sent, identities, permits, reconciliations, admissions, priced = {}, {}, {}, {}, {}, {}, {}, {}, {}
    for name in names:
        run = root/name; kind, task_id, draw, revision = expected[name]; task = tasks[task_id]
        sp, policy = versions(a, run, name, kind, task, draw, revision, population, revision_name, contract_value, contract_digest)
        sp_by_run[name] = sp; policies[revision] = policy
        rows = chain(a, run, name, kind, task)
        request_bytes, arguments, instruction, body, envelope = request(a, run, name, kind, sp, task, contract_value, contract_digest)
        admission = host_admission(a, run, name, kind, policy, contract_value, instruction, request_bytes, arguments); admissions[name] = admission
        book = ledger.Ledger(ledgers/sp['campaign_id']/'rehearsal', sp['campaign_id'])
        permit = reconciliation = http = None
        if kind != 'refused':
            permit, reconciliation = ledger_rows(a, run, name, kind, sp, task, draw, revision, rules, request_bytes, policy, admission, contract_digest)
            permits[name], reconciliations[name] = permit, reconciliation
            priced[name] = reservation_priced(a, run, name, policy, permit, admission, envelope)
            disposition(a, run, name, kind, rules, permit, reconciliation, book); slot_contents(a, run, name, rules, permit, reconciliation, book)
            layout_root = mounts(a, run, name, sp, task, draw, permit, book)
            command_reconstructed(a, run, name, sp, policy, task, draw, permit, load(run/'stages/proposal-1/output/http.json'), layout_root)
            receipts(a, run, name, rows, policy)
        s = seal(a, run, name); report, final = publication_recomputed(a, run, name)
        accepted = terminal(a, run, name, kind, rows, report, final)
        summary_bound(a, run, name, kind, task, draw, sp, contract_digest); chain_and_outcome(a, run, name, kind, rows, s, accepted)
        out = run/'stages/proposal-1/output'; http = load(out/'http.json') if (out/'http.json').exists() else None
        if kind != 'refused':
            grant(a, run, name, kind, permit, http, rules)
            serialized = transport(a, run, name, kind, policy, task, draw, permit, http, body, contract_digest)
            actor_check(a, run, name, policy, contract_value, instruction, request_bytes, arguments, permit, body)
            interpretation(a, run, name, request_bytes); commitment(a, run, name, http); slot_identity(a, run, name, sp, task, draw, permit, http, body)
            bodies.setdefault(task_id, {})[name] = serialized
            if kind == 'proof': sent.setdefault(task_id, {})[name] = (out/'outbound-body.json').read_bytes()
            identities[name] = {'reservation_id': permit['reservation_id'], 'attempt_id': permit['attempt_id'], 'grant_id': http.get('grant_id'),
                                'commitment': http['credential_commitment_sha256'], 'nonce': http['commitment_nonce']}
        accounting(a, run, name, kind, policy, http, permit, reconciliation)
        payload_receipts(a, run, name, kind, rows, sp, task, permit, reconciliation, http, admission)
        stage_outcomes(a, run, name, kind, policy)
        if kind == 'proof': proof(a, run, name, rows, task, sp, request_bytes)
        elif kind == 'release': failure(a, run, name, http)
        else: refusal(a, run, name, rows, admission)
        result['runs'][name] = {'kind': kind, 'task': task_id, 'draw': draw, 'revision': revision, 'policy_sha256': sp['config_sha256'],
                                'ledger_outcome': reconciliation['kind'] if reconciliation else None, 'body_sha256': sha(body)}
    result['campaign'] = cross_run(a, root, ledgers, expected, sp_by_run, policies, bodies, sent, identities, permits, reconciliations, admissions, priced, contract_digest)
    cases = expected_cases(population)
    missing = sorted(set(cases)-set(a.cases)); extra = sorted(set(a.cases)-set(cases))
    if missing or extra or len(a.cases) != len(cases): raise Rejection('cases:population', f'missing {missing} extra {extra}')
    result.update(accepted=all(a.cases.values()) and len(a.cases) == len(cases), cases=a.cases, case_count=len(cases), revision=revision_name,
                  contract_sha256=contract_digest, entity_body_sha256={t: sha(next(iter(g.values()))) for t, g in bodies.items()}, identities=identities,
                  live_model_calls=0, credentials_read=0, program_sha256=sha(Path(__file__).read_bytes()),
                  scope='historical audit over retained bytes; no native execution or inference')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--revision', choices=sorted(POPULATIONS), default=contract.NAME)
    parser.add_argument('--runs', type=Path)
    parser.add_argument('--ledgers', type=Path, default=ROOT/'ledgers/campaigns')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    runs = args.runs or ROOT/POPULATIONS[args.revision]['runs']
    if args.output and args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    try: result = audit(runs.resolve(), args.ledgers.resolve(), args.revision)
    except Rejection as rejection:
        print(json.dumps({'accepted': False, 'rejected_case': rejection.case, 'detail': str(rejection)}, indent=1)); sys.exit(1)
    if args.output: r6.write_json(args.output, result)
    print(json.dumps({k: result[k] for k in ('accepted', 'case_count', 'revision', 'modules', 'entity_body_sha256', 'campaign')}, indent=1))
    sys.exit(0 if result['accepted'] else 1)


if __name__ == '__main__':
    main()
