#!/usr/bin/env python3
"""R6-008 historical auditor over the canned campaign runs (v1 or v2). Non-locked; read-only.

Same discipline as pilot_audit.py: every relationship is reconstructed from
retained bytes, each run binds its own policy, lock and sources from its
provenance, and the named cases are a fixed population. New relationships for
this policy: the shared rehearsal ledger (permit row and reconciliation row
present by hash, kinds as expected), the send grant (bound to the permit and
ordered between certificate verification and the first header byte), the
credential commitment (recomputed from the mounted canary), single supervisor
receipts bound to the process record, the split transport predicates, and
finalization of every failed run. After the second review: the retained policy
must name the retained lock; imported frozen modules must equal the run's
retained copies; publication is recomputed with the frozen scanner rather than
read from a flag; and every terminal commitment is bound to its file.
"""
import argparse
import copy
import gzip
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import campaign_budget as budget
import campaign_contract as contract
import campaign_episode as driver
import campaign_ledger as ledger
import credential
import envelope_proof_audit
import episode
import events
import payload
import priced_payload_v2 as v2
import pricing_gate_v2 as gate
import provider_payload
import publication
import run as r6

RUNS = ('rehearsal-1', 'rehearsal-2', 'rehearsal-3')
TASK = 'verinf-d1-70'
DOMAINS = ('r6-campaign-ledger-1', 'r6-campaign-ledger-2')
# Explicit version dispatch: what each frozen revision's ledger promised, so a superseded revision is audited
# against its own rules and reported as superseded, never as invalid merely for being older.
RULES = {'responses_campaign_v1': {'purpose': False, 'termination_flag': False, 'launched': False, 'slots': False, 'grant_domain': 'r6-campaign-send-grant-1',
                                   'accounting': 'v1', 'durability_timed': False, 'marker': 'row_hash', 'attempt_id': False},
         'responses_campaign_v2': {'purpose': True, 'termination_flag': True, 'launched': False, 'slots': True, 'grant_domain': 'r6-campaign-send-grant-2',
                                   'accounting': 'v1', 'durability_timed': True, 'marker': 'row_hash', 'attempt_id': False},
         'responses_campaign_v3': {'purpose': True, 'termination_flag': True, 'launched': True, 'slots': True, 'grant_domain': 'r6-campaign-send-grant-2',
                                   'accounting': 'v3', 'durability_timed': True, 'marker': 'row_hash', 'attempt_id': False},
         'responses_campaign_v4': {'purpose': True, 'termination_flag': True, 'launched': True, 'slots': True, 'grant_domain': 'r6-campaign-send-grant-2',
                                   'accounting': 'v4', 'durability_timed': True, 'marker': 'digest', 'attempt_id': True, 'evidence': False},
         'responses_campaign_v5': {'purpose': True, 'termination_flag': True, 'launched': True, 'slots': True, 'grant_domain': 'r6-campaign-send-grant-2',
                                   'accounting': 'v5', 'durability_timed': True, 'marker': 'digest', 'attempt_id': True, 'evidence': True},
         'responses_campaign_v6': {'purpose': True, 'termination_flag': True, 'launched': True, 'slots': True, 'grant_domain': 'r6-campaign-send-grant-2',
                                   'accounting': 'v5', 'durability_timed': True, 'marker': 'digest', 'attempt_id': True, 'evidence': True},
         'responses_campaign_v7': {'purpose': True, 'termination_flag': True, 'launched': True, 'slots': True, 'grant_domain': 'r6-campaign-send-grant-2',
                                   'accounting': 'v5', 'durability_timed': True, 'marker': 'digest', 'attempt_id': True, 'evidence': True}}
CAMPAIGN_MODULES = ('campaign_budget', 'campaign_contract', 'campaign_ledger', 'campaign_episode')
MODULES = {'campaign_budget': ('campaign-harness', budget), 'campaign_contract': ('campaign-harness', contract),
           'campaign_ledger': ('campaign-harness', ledger), 'campaign_episode': ('campaign-harness', driver), 'credential': ('credential-harness', credential),
           'publication': ('credential-harness', publication), 'envelope_proof_audit': ('envelope-harness', envelope_proof_audit),
           'episode': ('harness', episode), 'events': ('harness', events), 'payload': ('harness', payload),
           'priced_payload_v2': ('priced-v2-harness', v2), 'pricing_gate_v2': ('priced-v2-harness', gate),
           'provider_payload': ('provider-harness', provider_payload), 'run': ('harness', r6)}
CANNED_D1_EXPORT = 'cd6081daac2fc64d718d28202d1742ff1e653e9862031fb19a5efeb7cd7d1812'
COMMITMENT_DOMAIN = 'r6-campaign-credential-commitment-1'
EXPECT = {'rehearsal-1': ('credential_format', 'release'), 'rehearsal-2': ('stage_rejected', 'release'), 'rehearsal-3': ('proof', 'send_grant')}

PREFIX = [('supervisor', 'episode', 'episode_started')] + [(s, st, e) for st in ('preparation-build', 'preparation', 'pipeline-prepare')
          for s, e in (('supervisor', 'stage_started'), ('supervisor', 'stage_finished'))] + [
          ('supervisor', 'payload', 'payload_validated'), ('supervisor', 'live-payload', 'payload_validated'),
          ('supervisor', 'proposal', 'recovery_started'), ('supervisor', 'pricing-admission', 'pricing_admitted'),
          ('supervisor', 'campaign-ledger', 'request_reserved'), ('supervisor', 'proposal-1', 'stage_started'),
          ('supervisor', 'proposal-1', 'stage_finished'), ('supervisor', 'campaign-ledger', 'reservation_reconciled')]
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
SEQUENCES = {'rehearsal-1': PREFIX+OBSERVED+RECEIPT+[('supervisor', 'episode', 'episode_rejected')],
             'rehearsal-2': PREFIX+RECEIPT+[('supervisor', 'episode', 'episode_rejected')],
             'rehearsal-3': PREFIX+OBSERVED+RECEIPT+PROOF}


def parse_rows(raw):
    """events-style chain check tolerant of both ledger domains; v1 rows carry no purpose."""
    rows, previous = [], '0'*64
    for line in raw.splitlines():
        row = json.loads(line); recorded = row.pop('row_hash')
        if not (row.get('domain') in DOMAINS and row.get('sequence') == len(rows) and row.get('previous_hash') == previous
                and row.get('kind') in ledger.KINDS and ledger.digest(row) == recorded): raise ledger.Failure('campaign_ledger_chain')
        row['row_hash'] = recorded; rows.append(row); previous = recorded
    if not rows or rows[0]['kind'] != 'activation': raise ledger.Failure('campaign_ledger_not_activated')
    return rows


def ledger_state(rows, policy_sha256):
    activation = rows[0]
    if activation['policy_sha256'] != policy_sha256: raise ledger.Failure('campaign_ledger_policy_mismatch')
    reservations, terminal = {}, {}
    for row in rows[1:]:
        if row['kind'] == 'reservation': reservations[row['reservation_id']] = row
        else: terminal[row['reservation_id']] = row
    return {'purpose': activation.get('purpose', 'rehearsal'), 'authorization': activation['authorization'],
            'reservations': len(reservations), 'transmissions_consumed': sum(t['kind'] in ('send_grant', 'unknown') for t in terminal.values()),
            'presend_attempts_used': sum(t['kind'] == 'release' for t in terminal.values()),
            'unknown_outcomes': sum(t['kind'] == 'unknown' for t in terminal.values()),
            'open_reservations': [r for r in reservations if r not in terminal]}


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


def expected_cases():
    names = ['population:exactly_three_runs', 'task:manifest_bound', 'modules:bound_to_retained_copies', 'modules:campaign_revision',
             'shared_ledger:rows_present_and_consistent']
    for run in RUNS:
        kind = EXPECT[run][0]
        names += [f'{run}:versions:policy_lock_sources_bound', f'{run}:chain:valid', f'{run}:chain:expected_sequence',
                  f'{run}:request:regenerated', f'{run}:pricing:host_admission_rederived', f'{run}:ledger:permit_and_reconciliation_bound',
                  f'{run}:ledger:disposition_derived', f'{run}:slot:authoritative_matches_retained', f'{run}:mounts:authority_bound',
                  f'{run}:receipts:single_pair_bound_to_process', f'{run}:seal:retained_hashes', f'{run}:publication:recomputed',
                  f'{run}:terminal:commitments_bound', f'{run}:summary:bound_to_audited_records', f'{run}:seal:chain_and_outcome',
                  f'{run}:grant:consistent_with_outcome', f'{run}:accounting:recomputed', f'{run}:credential_receipt:recorded']
        if kind != 'stage_rejected':
            names += [f'{run}:pricing:actor_check_rederived', f'{run}:transport:record_consistent', f'{run}:interpretation:reproduced',
                      f'{run}:commitment:bound_to_mounted_canary']
        if kind == 'proof':
            names += [f'{run}:transport:local_send_and_remote_receipt', f'{run}:grant:ordered_before_first_header_byte',
                      f'{run}:proof:response_bound', f'{run}:proof:certificate_bound', f'{run}:proof:attribution_passed_through',
                      f'{run}:proof:shared_checker', f'{run}:proof:export_expected']
        else:
            names += [f'{run}:failure:classified_and_finalized']
    return tuple(names)


CASES = expected_cases()


def retained(run):
    ph = run/'provenance/campaign-harness'
    policy_path = next(ph.glob('policies/responses-campaign-v*.json')); lock_path = next(ph.glob('policies/campaign-harness-v*.sha256.json'))
    return ph, policy_path, lock_path, load(policy_path), load(lock_path)


def versions(a, run, name):
    sp = load(run/'search-policy.json'); ph, policy_path, lock_path, policy, lock = retained(run)
    version = policy['name'][-1]; files = tuple(lock)
    sources = {f: sha((ph/f).read_bytes()) for f in files}
    a.require(sp['config_sha256'] == sha(policy_path.read_bytes()) and sp['source_lock_sha256'] == sha(lock_path.read_bytes())
              and policy['source_lock_sha256'] == sha(lock_path.read_bytes())  # the frozen policy names this lock; mirrors agreeing is not that
              and sorted(lock) == sorted(contract.FILES) and all(lock[f] == sources[f] for f in files)
              and sp['task_id'] == TASK and sp['name'] == policy['name'] == 'responses_campaign_v'+version and sp['mode'] == 'rehearsal'
              and policy['live_enabled'] is False and policy['authorization'] is None
              and policy_path.read_bytes() == canonical(policy)+b'\n' and (run/'transport-policy.json').read_bytes() == policy_path.read_bytes()
              and sp['ledger_path'] == 'ledgers/rehearsal/'+sp['config_sha256']+'.ndjson',
              f'{name}:versions:policy_lock_sources_bound')
    return sp, policy


def modules(a, run):
    """Upstream frozen modules must equal the retained copies for every revision; campaign modules only for the current one."""
    revision = load(run/'search-policy.json')['name']; current = revision == contract.NAME
    def same(m, folder, module):
        p = run/'provenance'/folder/(m+'.py')
        return p.is_file() and sha(Path(module.__file__).read_bytes()) == sha(p.read_bytes())
    upstream = [m for m, (folder, module) in MODULES.items() if m not in CAMPAIGN_MODULES and not same(m, folder, module)]
    a.require(not upstream, 'modules:bound_to_retained_copies', 'imported upstream modules differ from the retained copies: '+', '.join(upstream))
    campaign = [m for m, (folder, module) in MODULES.items() if m in CAMPAIGN_MODULES and not same(m, folder, module)]
    if current:
        a.require(not campaign, 'modules:campaign_revision', 'current revision, yet imported campaign modules differ from the retained copies: '+', '.join(campaign))
        return {'revision': revision, 'superseded': False}
    a.require(revision in RULES, 'modules:campaign_revision', 'unknown campaign revision '+revision)
    # Superseded: the run's campaign modules are bound to its own lock (versions); the audit applies that revision's rules.
    return {'revision': revision, 'superseded': True, 'campaign_modules_differ_from_current': campaign,
            'qualification': 'auditor/source incompatibility for the campaign modules is recorded, not an invalidity verdict'}


def chain(a, run, name):
    try: rows = events.read(run/'events.ndjson')
    except ValueError as error: a.require(False, f'{name}:chain:valid', str(error))
    a.require(all(r['task_id'] == TASK and r['run_id'] == rows[0]['run_id'] for r in rows), f'{name}:chain:valid')
    observed = [(r['source'], r['stage'], r['event']) for r in rows]
    expected = SEQUENCES[name]
    if RULES[load(run/'search-policy.json')['name']]['attempt_id']:  # from v4 the attempt receipt precedes any ledger effect: mandatory, once, in place
        i = expected.index(('supervisor', 'pricing-admission', 'pricing_admitted'))
        expected = expected[:i]+[('supervisor', 'campaign-ledger', 'reservation_attempted')]+expected[i:]
    a.require(observed == expected, f'{name}:chain:expected_sequence', f'{len(observed)} events')
    return rows


def request(a, run, name, sp, policy, task):
    try: value = payload.strict_json(v2.request(task, load(run/'prepared.json')))
    except Exception as error: a.require(False, f'{name}:request:regenerated', type(error).__name__+': '+str(error))
    value['schema_version'] = 'r6-farkas-request-8'; value['policy_sha256'] = sp['config_sha256']  # both campaign revisions
    retained = (run/'live-request.json').read_bytes()
    prompt = (run/'prompt.txt').read_text(); opts = copy.deepcopy(policy['request'])
    opts['input'] = [{'role': 'system', 'content': prompt}, {'role': 'user', 'content': v2.previous.PREFIX+sha(retained)+v2.previous.SEPARATOR+retained.decode()}]
    a.require(canonical(value)+b'\n' == retained and sha(prompt.encode()) == policy['prompt_sha256'] and load(run/'live-arguments.json') == opts
              and (run/'transport-request.json').read_bytes() == retained and load(run/'transport-arguments.json') == opts,
              f'{name}:request:regenerated')
    return retained, opts


def host_admission(a, run, name, policy, request_bytes, arguments):
    record = load(run/'host-pricing-admission.json')
    derived = gate.admission(policy, run/'pricing-sources', arguments, request_bytes, record['evaluated_at_unix'])
    a.require(record['accepted'] is True and derived == record, f'{name}:pricing:host_admission_rederived')
    return record


def ledger_rows(a, run, name, sp, request_bytes, policy, admission, kind):
    permit = load(run/'campaign-permit.json'); reconciliation = load(run/'campaign-reconciliation.json')
    before = parse_rows((run/'transport-ledger.ndjson').read_bytes()); after = parse_rows((run/'ledger-after.ndjson').read_bytes())
    reservation = load(run/'reservation.json'); v2 = 'purpose' in before[0]
    consistent_termination = (not v2) or reconciliation['kind'] != 'release' or reconciliation['termination_established'] or reconciliation.get('reason') == 'pre_launch_failure'
    a.require(reconciliation_evidence(run, reconciliation) and before[-1] == permit and after[-1] == reconciliation and after[:len(before)] == before
              and permit['kind'] == 'reservation' and permit['episode_id'] == name and permit['policy_sha256'] == sp['config_sha256']
              and permit['request_sha256'] == sha(request_bytes) and permit['arguments_sha256'] == sha(canonical(load(run/'live-arguments.json')))
              and permit['pricing_admission'] == admission and permit['reserved_micro_usd'] == permit['reservation']['reserved_micro_usd'] <= policy['limits']['total_micro_usd']
              and reconciliation['kind'] == EXPECT[name][1] and reconciliation['reservation_id'] == permit['reservation_id']
              and reservation == {**permit['reservation'], 'reservation_id': permit['reservation_id'], 'request_sha256': permit['request_sha256'],
                                  'arguments_sha256': permit['arguments_sha256'], 'policy_sha256': permit['policy_sha256'],
                                  'pricing_admission_sha256': sha((run/'host-pricing-admission.json').read_bytes()),
                                  'ledger_row_hash': permit['row_hash'], 'ledger_sha256': sha((run/'transport-ledger.ndjson').read_bytes())}
              and before[0]['kind'] == 'activation' and before[0]['policy_sha256'] == sp['config_sha256']
              and (not v2 or (before[0]['purpose'] == 'rehearsal' and before[0]['authorization'] == policy['ledger']['rehearsal_authorization']))
              and consistent_termination and ledger_state(after, sp['config_sha256'])['open_reservations'] == []
              and attempt_identity_bound(run, permit),
              f'{name}:ledger:permit_and_reconciliation_bound')
    return permit, reconciliation


def attempt_identity_bound(run, permit):
    rules = RULES[load(run/'search-policy.json')['name']]
    if not rules['attempt_id']: return 'attempt_id' not in permit  # older revisions: explicit absence
    value = permit.get('attempt_id'); receipts = [r['payload'].get('attempt_id') for r in events.read(run/'events.ndjson') if r['event'] == 'reservation_attempted']
    well_formed = isinstance(value, str) and len(value) == 64 and all(c in '0123456789abcdef' for c in value)
    return well_formed and receipts == [value]


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


def disposition(a, run, name, rules, permit, reconciliation, book):
    """Termination and the expected row kind from the hash-bound evidence, not from the row's own flags."""
    process, http, launched = stage_records(run)
    slot = book.slot(permit['reservation_id']) if rules['slots'] else run/'stages/proposal-1/grant'
    grant_state = 'absent'
    try: grant_state = 'present' if read_grant(slot, permit, rules) is not None else 'absent'
    except ledger.Failure as error: grant_state = error.code
    terminated = ledger.termination_established(process) if rules['termination_flag'] else process is not None
    unsent = http is None or (http.get('body_sends_started') == 0 and http.get('header_sends_started') == 0)
    if grant_state == 'present': expected = 'send_grant'
    elif grant_state != 'absent': expected = 'unknown'
    elif rules['launched'] and not launched and process is None and http is None: expected = 'release'
    elif terminated and unsent: expected = 'release'
    else: expected = 'unknown'
    flag_ok = (not rules['termination_flag']) or reconciliation['termination_established'] is (ledger.termination_established(process))
    launched_ok = (not rules['launched']) or reconciliation['launched'] is launched
    a.require(reconciliation['kind'] == expected == EXPECT[name][1] and flag_ok and launched_ok, f'{name}:ledger:disposition_derived',
              f'derived {expected} (grant {grant_state}, terminated {terminated}, launched {launched}), recorded {reconciliation["kind"]}')


def slot_contents(a, run, name, rules, permit, reconciliation, book):
    """The authoritative slot beside the ledger: exactly the expected marker, bound to the reservation and the terminal row, equal to the run's copy."""
    if not rules['slots']:
        a.require(True, f'{name}:slot:authoritative_matches_retained'); return
    slot = book.slot(permit['reservation_id']); retained = run/'stages/proposal-1/grant'
    files = sorted(p.name for p in slot.iterdir()) if slot.is_dir() else None
    expected = {'send_grant': ['send-grant.json'], 'release': ['release.json'], 'unknown': ['unknown.json']}[reconciliation['kind']]
    if reconciliation.get('torn_marker'): expected = sorted(set(expected+[reconciliation['torn_marker']]))  # torn bytes stay beside the valid receipt, across retries
    same = files == expected and all((retained/f).is_file() and (retained/f).read_bytes() == (slot/f).read_bytes() for f in expected)
    if reconciliation['kind'] == 'send_grant':
        try: bound = read_grant(slot, permit, rules) == reconciliation['grant']
        except ledger.Failure: bound = False
        if rules['marker'] == 'digest': bound = bound and reconciliation.get('marker_sha256') == sha((slot/ledger.GRANT_FILE).read_bytes())
    elif rules['marker'] == 'digest':  # the marker precedes the row and the row names the marker's bytes; a torn marker is never the receipt
        receipt_name = reconciliation['kind']+'.json'
        try: marker = load(slot/receipt_name) if same else None
        except ValueError: marker = None
        bound = same and isinstance(marker, dict) and marker.get('kind') == reconciliation['kind'] and marker.get('reservation_id') == permit['reservation_id'] \
                and isinstance(marker.get('reconciled_at_unix'), int) and reconciliation.get('marker_sha256') == sha((slot/receipt_name).read_bytes())
    else:
        bound = load(slot/expected[0]) == {'row_hash': reconciliation['row_hash'], 'kind': reconciliation['kind']} if same else False
    a.require(same and bound, f'{name}:slot:authoritative_matches_retained', f'slot {files}, expected {expected}, bound {bound}')


def mounts(a, run, name, rules, sp, permit, book):
    """The sender's authority came from the policy-derived ledger file (read-only) and this reservation's slot (writable)."""
    command = load(run/'stages/proposal-1/command.json'); argv = command['argv']
    def source(guest, flag):
        hits = [i for i, x in enumerate(argv) if x == guest and i >= 2 and argv[i-2] == flag]
        return argv[hits[0]-1] if len(hits) == 1 else None
    if not rules['slots']:
        a.require(source('/grant', '--bind') is not None and source('/ledger.ndjson', '--ro-bind') is not None, f'{name}:mounts:authority_bound'); return
    ledger_src, grant_src = source('/ledger.ndjson', '--ro-bind'), source('/grant', '--bind')
    root = ledger_src[:-len(sp['ledger_path'])] if ledger_src and ledger_src.endswith(sp['ledger_path']) else None
    run_dir = command['run']
    ok = (root is not None and grant_src == root+sp['ledger_slots']+'/'+permit['reservation_id'] and command['grant_slot'] == grant_src
          and Path(ledger_src).name == book.path.name and Path(grant_src).parent.name == book.slots.name
          and source('/policy.json', '--ro-bind') == run_dir+'/transport-policy.json' and source('/permit.json', '--ro-bind') == run_dir+'/campaign-permit.json'
          and source('/arguments.json', '--ro-bind') == run_dir+'/transport-arguments.json' and source('/request.json', '--ro-bind') == run_dir+'/transport-request.json'
          and source('/out', '--bind') == command['records']+'/output' and source('/grant', '--ro-bind') is None and source('/ledger.ndjson', '--bind') is None
          and argv.count('--bind') == 2)
    a.require(ok, f'{name}:mounts:authority_bound', f'ledger {ledger_src}, grant {grant_src}')


def reconciliation_evidence(run, reconciliation):
    stage = run/'stages/proposal-1'; ev = reconciliation['evidence']
    markers = sorted(p.name for p in (stage/'grant').iterdir()) if (stage/'grant').is_dir() else []
    expected_markers = {'send_grant': ['send-grant.json'], 'release': ['release.json'], 'unknown': ['unknown.json']}[reconciliation['kind']]
    v2 = 'termination_established' in reconciliation
    return (ev['process_sha256'] == sha((stage/'proposal-1.process.json').read_bytes())
            and ev['http_sha256'] == (sha((stage/'output/http.json').read_bytes()) if (stage/'output/http.json').exists() else None)
            and ev['grant_file_sha256'] == (sha((stage/'grant/send-grant.json').read_bytes()) if (stage/'grant/send-grant.json').exists() else None)
            and (not v2 or (markers == expected_markers and ev['record_read_failures'] == [])))
    return permit, reconciliation


def receipts(a, run, name, rows):
    started = [r['payload'] for r in rows if r['stage'] == 'proposal-1' and r['event'] == 'stage_started']
    finished = [r['payload'] for r in rows if r['stage'] == 'proposal-1' and r['event'] == 'stage_finished']
    process = load(run/'stages/proposal-1/proposal-1.process.json'); command = load(run/'stages/proposal-1/command.json')
    a.require(len(started) == 1 and len(finished) == 1 and finished[0] == process and started[0]['command_file'] == 'stages/proposal-1/command.json'
              and command['network_namespace'] == 'unshared' and '--unshare-net' in command['argv'] and '/grant' in command['argv'],
              f'{name}:receipts:single_pair_bound_to_process')


def seal(a, run, name, rows, kind):
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
                      and fresh_streams.get(e['path']) == e['streams'] for e in entries)  # the streams actually scanned, not a self-consistent total
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


def terminal(a, run, name, rows, kind, report, final):
    summary = load(run/'credential-summary.json'); payload = rows[-1]['payload']; acct = load(run/'accounting.json')
    rules = RULES[load(run/'search-policy.json')['name']]
    publication_ok = bool(report['accepted'] and final['report_clean'])
    if rules.get('evidence'):
        # evidence completion derived from the artifacts themselves, then every mirror compared with it
        derived = ((run/'campaign-reconciliation.json').exists() and (run/'ledger-after.ndjson').exists() and (run/'stages/proposal-1/grant').is_dir()
                   and any(r['event'] == 'reservation_reconciled' for r in rows) and summary['reservation_state'] == 'reserved' and summary['ledger_reconciled'] is True)
        mirrors = (summary['evidence_complete'] is derived and acct['evidence_complete'] is derived and payload['evidence_complete'] is derived
                   and summary['reconciliation_evidence_complete'] is acct['reconciliation_evidence_complete']
                   and summary['reservation_state'] == acct['reservation_state'] and summary['ledger_reconciled'] is acct['ledger_reconciled'])
        a.require(mirrors, f'{name}:terminal:commitments_bound', 'evidence_complete mirrors disagree with the artifacts')
        evidence_ok = derived and bool(summary['ledger_reconciled'])
        accepted = bool(summary['proof_accepted'] and summary['credential_use_accepted'] and publication_ok and evidence_ok)
        completed = summary['proof_accepted'] and summary['failure_category'] is None and publication_ok and evidence_ok
        a.cases.pop(f'{name}:terminal:commitments_bound')
    else:
        accepted = bool(summary['proof_accepted'] and summary['credential_use_accepted'] and publication_ok)
        completed = summary['proof_accepted'] and summary['failure_category'] is None and publication_ok
    a.require(payload['summary_sha256'] == sha((run/'credential-summary.json').read_bytes())
              and payload['publication_scan_sha256'] == sha((run/'publication-scan.json').read_bytes())
              and payload['publication_final_sha256'] == sha((run/'publication-final.json').read_bytes())
              and payload['proof_accepted'] is bool(summary['proof_accepted']) and payload['credential_use_accepted'] is bool(summary['credential_use_accepted'])
              and payload['publication_accepted'] is publication_ok and payload['publication_pending'] is False
              and payload['ledger_reconciled'] is bool(summary['ledger_reconciled']) and payload['accepted'] is accepted
              and rows[-1]['event'] == ('episode_finished' if completed else 'episode_rejected') and (kind == 'proof') == completed,
              f'{name}:terminal:commitments_bound')
    return accepted


def summary_bound(a, run, name, task, sp):
    """The summary is a mirror: its identity fields must name the task and policy, and its embedded accounting must equal the audited file."""
    summary = load(run/'credential-summary.json'); acct = load(run/'accounting.json')
    a.require(summary['task_id'] == task.id and summary['search_policy'] == sp['name'] and summary['mode'] == sp['mode']
              and summary['accounting'] == acct and summary['failure_category'] == acct.get('failure_category', summary['failure_category'])
              and (summary['proof_accepted'] is (run/'verdict.json').exists()),
              f'{name}:summary:bound_to_audited_records', 'summary identity or embedded accounting differs from the audited records')


def chain_and_outcome(a, run, name, rows, kind, s, accepted):
    a.require(s['event_count'] == len(rows) and s['last_event_hash'] == rows[-1]['event_hash'] and s['accepted'] is accepted is (kind == 'proof'),
              f'{name}:seal:chain_and_outcome')


def grant(a, run, name, kind, permit, http, rules):
    slot = run/'stages/proposal-1/grant/send-grant.json'
    if kind == 'proof':
        try: g = read_grant(slot.parent, permit, rules)
        except ledger.Failure: g = None
        created = http.get('grant_created_at_ns', http.get('grant_committed_at_ns')); durable = http.get('grant_durable_at_ns')
        if not rules['durability_timed']: durable = created  # v1 timed creation only; the qualification stays explicit
        a.require(g is not None and http['grant_committed'] is True and http['grant_id'] == g['grant_id'] and http['send_outcome'] == 'returned'
                  and created == g['at_ns'] and isinstance(durable, int), f'{name}:grant:consistent_with_outcome',
                  'durable completion timestamp missing' if durable is None else '')
        a.require(http['tls_verified_at_ns'] < created <= durable < http['header_send_at_ns'] and http['connection_started_at_ns'] <= http['tls_verified_at_ns'],
                  f'{name}:grant:ordered_before_first_header_byte')
    else:
        a.require(not slot.exists() and (http is None or (http['grant_committed'] is False and http['send_outcome'] == 'not_started'
                  and http['body_sends_started'] == 0 and http['header_sends_started'] == 0)), f'{name}:grant:consistent_with_outcome')


def actor_check(a, run, name, policy, request_bytes, arguments, permit):
    out = run/'stages/proposal-1/output'; record = load(out/'pricing-check.json')
    derived = gate.admission(policy, run/'transport-pricing-sources', arguments, request_bytes, record['evaluated_at_unix'])
    a.require(record['accepted'] is True and {k: v for k, v in record.items() if k != 'admitted_at_ns'} == derived
              and record['body_sha256'] == sha((out/'serialized-body.json').read_bytes())
              and 0 <= record['evaluated_at_unix']-permit['pricing_admission']['evaluated_at_unix'] <= policy['pricing_admission']['maximum_permit_age_seconds'],
              f'{name}:pricing:actor_check_rederived')


def transport(a, run, name, policy, kind, http):
    out = run/'stages/proposal-1/output'; body = (out/'serialized-body.json').read_bytes(); server = load(out/'server.json')
    a.require(http['mode'] == 'rehearsal' and http['policy_sha256'] == sha((run/'transport-policy.json').read_bytes())
              and http['request_sha256'] == sha(body) and http['request_bytes'] == len(body) and http['retries'] == 0 and http['redirects_followed'] == 0
              and http['transport_scope'] == 'isolated_loopback_https_fixture' and http['endpoint'] == policy['endpoint']
              and http['reservation_id'] is not None and http['authorization_present_in_policy'] is None,
              f'{name}:transport:record_consistent')
    if kind == 'proof':
        nonce = load(run/'credential-canary.json')['nonce']; header = credential.header(credential.derive(nonce))
        a.require(http['http_status'] == 200 and http['body_sends_returned'] == 1 and (out/'outbound-body.json').read_bytes() == body
                  and http['outbound_body_sha256'] == sha(body) and (out/'received-body.json').read_bytes() == body
                  and len(server['requests']) == 1 and server['requests'][0]['body_sha256'] == sha(body)
                  and server['requests'][0]['authorization_sha256'] == sha(header.encode()) and server['server_names'] == [policy['endpoint']['host']]
                  and http['tls']['verified'] is True and http['tls']['server_hostname'] == policy['endpoint']['host'],
                  f'{name}:transport:local_send_and_remote_receipt')


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


def accounting(a, run, name, policy, http, permit, reconciliation, kind, rules):
    acct = load(run/'accounting.json'); out = run/'stages/proposal-1/output'
    server = load(out/'server.json') if (out/'server.json').exists() else None
    if rules['accounting'] in ('v4', 'v5'):
        lifecycle = {'permit': permit, 'reservation': load(run/'reservation.json'), 'reconciliation': reconciliation, 'reconcile_error': None,
                     'reservation_state': 'reserved', 'evidence_write_failures': []}
        expected = driver.accounting_for(run, policy, False, http, server, lifecycle)
        if rules['accounting'] == 'v4':  # v4's shape, reproduced from the current helper's output
            expected.pop('reconciliation_evidence_complete', None)
    else:
        usage = provider_payload.usage({}); status = 'unreported'
        if (out/'provider-response.json').exists(): usage = provider_payload.usage(load(out/'provider-response.json')); status = usage['status']
        rates = policy['pricing']['nano_usd_per_token']
        estimate = None if usage['input_tokens'] is None else gate.cost_micro(usage['input_tokens'], usage['output_tokens'], rates)
        h = http or {}
        if rules['accounting'] == 'v3':  # reproduced as that revision computed it
            observed = http is not None
            grant_committed = reconciliation['kind'] == 'send_grant'
            send_outcome = (reconciliation.get('send_outcome') if reconciliation['kind'] == 'send_grant'
                            else ('not_started' if reconciliation['kind'] == 'release' else (h.get('send_outcome') if observed else None)))
            consumed = 1 if reconciliation['kind'] in ('send_grant', 'unknown') else 0
            expected = {'attempts_reserved': 1, 'reservation': load(run/'reservation.json'), 'reservation_id': permit['reservation_id'],
                        'transport_record_observed': observed,
                        'connection_attempts': h['connection_attempts'] if observed else None, 'headers_started': h['header_sends_started'] if observed else None,
                        'transmissions_observed': h['body_sends_started'] if observed else None, 'transmissions_returned': h['body_sends_returned'] if observed else None,
                        'grant_committed': grant_committed, 'send_outcome': send_outcome, 'ledger_outcome': reconciliation['kind'], 'ledger_reconciled': True,
                        'allowance_consumed': consumed, 'endpoint_receipts': len(server['requests']) if server else None,
                        'usage': usage, 'usage_status': status, 'priced_usage_ceiling_micro_usd': estimate, 'live_transmissions_consumed': 0,
                        'live_usage_ceiling_usd': None, 'scope': acct['scope']}
        else:
            server = server or {'requests': []}
            expected = {'attempts_reserved': 1, 'reservation': load(run/'reservation.json'), 'reservation_id': permit['reservation_id'],
                        'connection_attempts': h.get('connection_attempts', 0), 'headers_started': h.get('header_sends_started', 0),
                        'transmissions_started': h.get('body_sends_started', 0), 'transmissions_returned': h.get('body_sends_returned', 0),
                        'grant_committed': h.get('grant_committed', False), 'send_outcome': h.get('send_outcome', 'not_started'),
                        'ledger_outcome': reconciliation['kind'], 'endpoint_receipts': len(server['requests']), 'usage': usage, 'usage_status': status,
                        'priced_usage_ceiling_micro_usd': estimate, 'live_transmissions_consumed': 0, 'live_usage_ceiling_usd': None, 'scope': acct['scope']}
    a.require(acct == expected, f'{name}:accounting:recomputed')
    r = load(run/'credential-receipt.json')
    a.require(r['channel'] == 'private_read_only_file' and r['exact_receipt'] is (kind == 'proof'), f'{name}:credential_receipt:recorded')


def failure(a, run, name, rows, kind, http):
    summary = load(run/'credential-summary.json')
    if kind == 'credential_format':
        stderr = (run/'stages/proposal-1/proposal-1.stderr').read_text(); process = load(run/'stages/proposal-1/proposal-1.process.json')
        a.require(summary['failure_category'] == 'credential_format' and http['failure_category'] == 'credential_format' and process['exit_code'] == 0
                  and stderr == '' and http['connection_attempts'] == 0 and load(run/'stages/proposal-1/output/pricing-check.json')['accepted'] is True
                  and (run/'seal.json').exists(), f'{name}:failure:classified_and_finalized')
    else:
        process = load(run/'stages/proposal-1/proposal-1.process.json')
        a.require(summary['failure_category'] == 'stage_rejected' and http is None and process['exit_code'] != 0
                  and not (run/'stages/proposal-1/output/http.json').exists() and (run/'seal.json').exists(), f'{name}:failure:classified_and_finalized')


def proof(a, run, name, rows, task, request_bytes):
    response, validated = load(run/'response.json'), load(run/'validated-response.json'); out = run/'stages/proposal-1/output'
    raw = load(out/'provider-response.json')
    text = [c['text'] for item in raw['output'] if item.get('type') == 'message' for c in item['content'] if c.get('type') == 'output_text']
    a.require(response == validated and json.loads(''.join(text)) == response and response['request_sha256'] == sha(request_bytes), f'{name}:proof:response_bound')
    evidence, cert, verdict = load(run/'evidence.json'), load(run/'certificate-verdict.json'), load(run/'verdict.json')
    assembled = next(r['payload'] for r in rows if r['event'] == 'certificate_assembled')
    a.require(evidence['certificate']['payload']['witness_data'] == response['witness'] and cert['accepted'] is True and cert['reason']['kind'] == 'verified_farkas'
              and cert['certificate_hash'] == 'sha256:'+assembled['certificate_sha256'] and assembled['response_sha256'] == sha((run/'validated-response.json').read_bytes())
              and cert == next(r['payload'] for r in rows if r['event'] == 'independent_certificate_verdict') and verdict['certificate_validation'] == cert
              and verdict['request_sha256'] == sha(request_bytes) and load(run/'stages/assembly/output/evidence.json') == evidence, f'{name}:proof:certificate_bound')
    named = {r['event']: (r['payload'].get('proposer', r['payload'].get('witness_proposer')), r['payload'].get('route'), r['payload'].get('consumer_route'))
             for r in rows if r['event'] in ('recovery_started', 'certificate_assembled', 'recovery_finished')}
    route = load(run/'search-policy.json')['name']
    a.require(named == {'recovery_started': ('canned_provider_response', route, None),
                        'certificate_assembled': ('canned_provider_response', None, 'openai_responses_http_fixture_v1'),
                        'recovery_finished': ('canned_provider_response', route, 'openai_responses_http_fixture_v1')}
              and verdict['witness_proposer'] == 'canned_provider_response' and verdict['consumer_route'] == 'openai_responses_http_fixture_v1',
              f'{name}:proof:attribution_passed_through', str(named))
    def receipt(stage, event):
        hits = [r['payload'] for r in rows if r['source'] == 'supervisor' and r['stage'] == stage and r['event'] == event]
        if len(hits) != 1: raise ValueError(f'{stage}/{event}: {len(hits)} receipts')
        return hits[0]
    read = lambda n: load(run/n)
    try:
        _, expected = r6.frozen_task(task); challenge = json.loads(request_bytes)['binding']['challenge_sha256']
        if not (read('stages/reconstruct/output/context.json') == read('stages/preparation/output/context.json') == load(task.path/'context/local-context.json')):
            raise ValueError('reconstruction context differs from the frozen context')
        if verdict['task_id'] != task.id or verdict['manifest_sha256'] != sha((task.path/'manifest.json').read_bytes()) \
                or not (verdict['challenge_sha256'] == expected['challenge_sha256'] == challenge):
            raise ValueError('target identity differs (task, manifest or challenge)')
        envelope_proof_audit.audit(task, evidence, verdict, rows, lambda n: run/n, read, receipt)
    except (ValueError, AssertionError, KeyError, OSError, gzip.BadGzipFile, EOFError) as error:
        a.require(False, f'{name}:proof:shared_checker', str(error))
    a.require(True, f'{name}:proof:shared_checker')
    proved = next(r['payload'] for r in rows if r['event'] == 'proof_validated')
    a.require(proved['proof_accepted'] is True and proved['solution_sha256'] == verdict['solution_sha256'] == CANNED_D1_EXPORT
              and proved['verdict_sha256'] == sha((run/'verdict.json').read_bytes()) and verdict['local_obligation_closed'] is True, f'{name}:proof:export_expected')


def shared_ledger(a, root, ledger_dir, permits, reconciliations):
    digests = {load(root/n/'search-policy.json')['config_sha256'] for n in RUNS}
    if len(digests) != 1: a.require(False, 'shared_ledger:rows_present_and_consistent', 'runs under different policies')
    book = ledger.Ledger(ledger_dir/'rehearsal', next(iter(digests)))
    try:
        if not book.head.exists() or not book.path.exists(): raise ledger.Failure('campaign_ledger_missing_after_activation')
        head = load(book.head); rows = parse_rows(book.path.read_bytes())
        if not (len(rows) >= head['rows'] and rows[head['rows']-1]['row_hash'] == head['last_hash']): raise ledger.Failure('campaign_ledger_truncated')
        s = ledger_state(rows, next(iter(digests)))
    except ledger.Failure as error: a.require(False, 'shared_ledger:rows_present_and_consistent', error.code)
    hashes = {r['row_hash'] for r in rows}
    slots_closed = all(any((book.slot(p['reservation_id'])/m).exists() for m in ledger.MARKERS) for p in permits.values()) if 'purpose' in rows[0] else True
    a.require(all(p['row_hash'] in hashes for p in permits.values()) and all(r['row_hash'] in hashes for r in reconciliations.values())
              and s['open_reservations'] == [] and s['transmissions_consumed'] == 1 and s['presend_attempts_used'] == 2
              and rows[0]['authorization']['approved_by'] == 'rehearsal' and s['purpose'] == 'rehearsal' and slots_closed,
              'shared_ledger:rows_present_and_consistent')
    return {'path': str(book.path), 'rows': len(rows), 'state': {k: s[k] for k in ('reservations', 'transmissions_consumed', 'presend_attempts_used', 'unknown_outcomes')}}


def audit(root, ledger_dir):
    a = Audit(); result = {'runs': {}}
    entries = sorted(p.name for p in root.iterdir())
    a.require(entries == sorted(RUNS) and all((root/n).is_dir() for n in entries), 'population:exactly_three_runs', str(entries))
    task = r6.get_task(TASK)
    a.require(all(load(root/n/'search-policy.json')['manifest_sha256'] == sha((task.path/'manifest.json').read_bytes()) for n in RUNS), 'task:manifest_bound')
    result['modules'] = modules(a, root/'rehearsal-3'); rules = RULES[result['modules']['revision']]
    permits, reconciliations = {}, {}
    for name in RUNS:
        run = root/name; kind = EXPECT[name][0]
        sp, policy = versions(a, run, name); rows = chain(a, run, name)
        request_bytes, arguments = request(a, run, name, sp, policy, task)
        admission = host_admission(a, run, name, policy, request_bytes, arguments)
        permit, reconciliation = ledger_rows(a, run, name, sp, request_bytes, policy, admission, kind)
        permits[name], reconciliations[name] = permit, reconciliation
        book = ledger.Ledger(ledger_dir/'rehearsal', sp['config_sha256'])
        disposition(a, run, name, rules, permit, reconciliation, book); slot_contents(a, run, name, rules, permit, reconciliation, book)
        mounts(a, run, name, rules, sp, permit, book)
        receipts(a, run, name, rows); s = seal(a, run, name, rows, kind)
        report, final = publication_recomputed(a, run, name); accepted = terminal(a, run, name, rows, kind, report, final)
        summary_bound(a, run, name, task, sp); chain_and_outcome(a, run, name, rows, kind, s, accepted)
        out = run/'stages/proposal-1/output'; http = load(out/'http.json') if (out/'http.json').exists() else None
        grant(a, run, name, kind, permit, http, rules)
        if kind != 'stage_rejected':
            actor_check(a, run, name, policy, request_bytes, arguments, permit); transport(a, run, name, policy, kind, http)
            interpretation(a, run, name, request_bytes); commitment(a, run, name, http)
        accounting(a, run, name, policy, http, permit, reconciliation, kind, rules)
        if kind == 'proof': result['runs'][name] = {'kind': kind, 'proof': proof(a, run, name, rows, task, request_bytes) or 'accepted'}
        else: failure(a, run, name, rows, kind, http); result['runs'][name] = {'kind': kind, 'ledger_outcome': reconciliation['kind']}
    result['shared_ledger'] = shared_ledger(a, root, ledger_dir, permits, reconciliations)
    missing = sorted(set(CASES)-set(a.cases)); extra = sorted(set(a.cases)-set(CASES))
    if missing or extra: raise Rejection('cases:population', f'missing {missing} extra {extra}')
    result.update(accepted=all(a.cases.values()), cases=a.cases, case_count=len(CASES), live_model_calls=0, credentials_read=0,
                  program_sha256=sha(Path(__file__).read_bytes()), scope='historical audit over retained bytes; no native execution or inference')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runs', type=Path, default=ROOT/'campaign-runs-v2')
    parser.add_argument('--ledgers', type=Path, default=ROOT/'ledgers')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output and args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    try: result = audit(args.runs.resolve(), args.ledgers.resolve())
    except Rejection as rejection:
        print(json.dumps({'accepted': False, 'rejected_case': rejection.case, 'detail': str(rejection)}, indent=1)); sys.exit(1)
    if args.output: r6.write_json(args.output, result)
    print(json.dumps({'accepted': result['accepted'], 'case_count': result['case_count'], 'shared_ledger': result['shared_ledger']}, indent=1))
    sys.exit(0 if result['accepted'] else 1)


if __name__ == '__main__' and '--live-run' not in sys.argv:
    main()


# ---------------------------------------------------------------------------------------------------------------------
# Live-run audit: one signed transmission under a campaign policy, reconstructed like the rehearsals, with the live
# relationships in place of the loopback ones: signed policy and live ledger bound to the authorization, shared network
# stage with the public bundle and the operator's file, credential *use* (not receipt), publication pending until the
# operator scan is bound to the run's commitment and seal.
# ---------------------------------------------------------------------------------------------------------------------
LIVE_EXPORTS = {'f4c179f39dc8b5f2': 'deterministic golden export (2·hZ + neg_goal)', '862f16b9d9efc5de': 'pilot live-2 export (hwidth + 32769·neg_goal)'}
LIVE_SEQUENCE = (PREFIX[:10]+[('supervisor', 'campaign-ledger', 'reservation_attempted'), ('supervisor', 'pricing-admission', 'pricing_admitted'),
                 ('supervisor', 'campaign-ledger', 'request_reserved'), ('supervisor', 'proposal', 'live_transport_authorized'),
                 ('supervisor', 'proposal-1', 'stage_started'), ('supervisor', 'proposal-1', 'stage_finished'),
                 ('supervisor', 'campaign-ledger', 'reservation_reconciled')]+OBSERVED+[('supervisor', 'credential-receipt', 'credential_use_checked')]+PROOF)
LIVE_CASES = tuple(['live:versions:signed_policy_and_lock_bound', 'live:ledger:activation_serves_authorization', 'live:chain:valid',
                    'live:chain:expected_sequence', 'live:request:regenerated', 'live:pricing:host_admission_rederived', 'live:pricing:actor_check_rederived',
                    'live:ledger:permit_and_reconciliation_bound', 'live:ledger:disposition_derived', 'live:slot:authoritative_matches_retained',
                    'live:mounts:authority_and_network_bound', 'live:receipts:single_pair_bound_to_process', 'live:transport:record_consistent',
                    'live:transport:local_send_checked_remote_unobservable', 'live:grant:ordered_before_first_header_byte',
                    'live:credential_use:recorded_not_exact_receipt', 'live:interpretation:reproduced', 'live:accounting:recomputed',
                    'live:proof:response_bound', 'live:proof:witness_contradiction', 'live:proof:certificate_bound', 'live:proof:attribution_live',
                    'live:proof:shared_checker', 'live:proof:export_recorded', 'live:provider:reported_fields', 'live:seal:retained_hashes',
                    'live:publication:structural_scan_recomputed', 'live:terminal:pending_and_commitments_bound', 'live:summary:bound_to_audited_records',
                    'live:seal:chain_and_outcome', 'live:operator_scan:bound_to_commitment_and_seal', 'live:campaign:one_transmission_under_signed_authorization'])


def live_audit(run, ledger_dir, scan_summary, checkpoint):
    a = Audit(); task = r6.get_task(TASK); name = 'live'
    sp = load(run/'search-policy.json'); ph, policy_path, lock_path, policy, lock = retained(run)
    rules = RULES[policy['name']]; files = tuple(lock); sources = {f: sha((ph/f).read_bytes()) for f in files}
    disabled = load(checkpoint)  # the disabled bytes the signature was applied to: same policy minus the signature fields
    unsigned_view = {k: v for k, v in policy.items() if k not in ('live_enabled', 'authorization', 'live_model_calls_authorized', 'signed_from_checkpoint_sha256')}
    checkpoint_ok = (sha(checkpoint.read_bytes()) == policy['signed_from_checkpoint_sha256'] and disabled['live_enabled'] is False and disabled['authorization'] is None
                     and {k: v for k, v in disabled.items() if k not in ('live_enabled', 'authorization', 'live_model_calls_authorized')} == unsigned_view)
    a.require(sp['config_sha256'] == sha(policy_path.read_bytes()) and sp['source_lock_sha256'] == sha(lock_path.read_bytes())
              and policy['source_lock_sha256'] == sha(lock_path.read_bytes()) and all(lock[f] == sources[f] for f in files)
              and sp['mode'] == 'live' and policy['live_enabled'] is True and policy['authorization'] is not None
              and policy_path.read_bytes() == canonical(policy)+b'\n' and (run/'transport-policy.json').read_bytes() == policy_path.read_bytes()
              and sp['ledger_path'] == 'ledgers/live/'+sp['config_sha256']+'.ndjson' and checkpoint_ok,
              'live:versions:signed_policy_and_lock_bound')
    try: ledger.authorization_scope(policy)
    except ledger.Failure as error: a.require(False, 'live:ledger:activation_serves_authorization', error.code)
    book = ledger.Ledger(ledger_dir/'live', sp['config_sha256'])
    raw_ledger, s = book.snapshot(); rows_ledger = ledger.parse(raw_ledger)
    try: ledger.check_activation(s, policy, True)
    except ledger.Failure as error: a.require(False, 'live:ledger:activation_serves_authorization', error.code)
    a.require(s['purpose'] == 'live' and s['authorization'] == policy['authorization'], 'live:ledger:activation_serves_authorization')
    rows = events.read(run/'events.ndjson')
    a.require(all(r['task_id'] == TASK and r['run_id'] == rows[0]['run_id'] for r in rows), 'live:chain:valid')
    a.require([(r['source'], r['stage'], r['event']) for r in rows] == LIVE_SEQUENCE, 'live:chain:expected_sequence', f'{len(rows)} events')
    # request/admission, as for rehearsals
    value = payload.strict_json(v2.request(task, load(run/'prepared.json'))); value['schema_version'] = 'r6-farkas-request-8'; value['policy_sha256'] = sp['config_sha256']
    request_bytes = (run/'live-request.json').read_bytes(); prompt = (run/'prompt.txt').read_text(); opts = copy.deepcopy(policy['request'])
    opts['input'] = [{'role': 'system', 'content': prompt}, {'role': 'user', 'content': v2.previous.PREFIX+sha(request_bytes)+v2.previous.SEPARATOR+request_bytes.decode()}]
    a.require(canonical(value)+b'\n' == request_bytes and sha(prompt.encode()) == policy['prompt_sha256'] and load(run/'live-arguments.json') == opts
              and (run/'transport-request.json').read_bytes() == request_bytes and load(run/'transport-arguments.json') == opts, 'live:request:regenerated')
    admission = load(run/'host-pricing-admission.json')
    a.require(admission['accepted'] is True and gate.admission(policy, run/'pricing-sources', opts, request_bytes, admission['evaluated_at_unix']) == admission,
              'live:pricing:host_admission_rederived')
    out = run/'stages/proposal-1/output'; record = load(out/'pricing-check.json'); permit = load(run/'campaign-permit.json')
    derived = gate.admission(policy, run/'transport-pricing-sources', opts, request_bytes, record['evaluated_at_unix'])
    a.require(record['accepted'] is True and {k: v for k, v in record.items() if k != 'admitted_at_ns'} == derived
              and record['body_sha256'] == sha((out/'serialized-body.json').read_bytes())
              and 0 <= record['evaluated_at_unix']-permit['pricing_admission']['evaluated_at_unix'] <= policy['pricing_admission']['maximum_permit_age_seconds'],
              'live:pricing:actor_check_rederived')
    # ledger rows: permit is the reservation row, reconciliation is the terminal row, both in the live ledger
    reconciliation = load(run/'campaign-reconciliation.json'); before = parse_rows((run/'transport-ledger.ndjson').read_bytes()); after = parse_rows((run/'ledger-after.ndjson').read_bytes())
    reservation = load(run/'reservation.json'); hashes = {r['row_hash'] for r in rows_ledger}
    a.require(reconciliation_evidence(run, reconciliation) and before[-1] == permit and after[-1] == reconciliation and after[:len(before)] == before
              and permit['row_hash'] in hashes and reconciliation['row_hash'] in hashes and permit['kind'] == 'reservation' and permit['episode_id'] == run.name
              and permit['policy_sha256'] == sp['config_sha256'] and permit['request_sha256'] == sha(request_bytes) and permit['pricing_admission'] == admission
              and reconciliation['kind'] == 'send_grant' and reconciliation['reservation_id'] == permit['reservation_id']
              and reservation == {**permit['reservation'], 'reservation_id': permit['reservation_id'], 'request_sha256': permit['request_sha256'],
                                  'arguments_sha256': permit['arguments_sha256'], 'policy_sha256': permit['policy_sha256'],
                                  'pricing_admission_sha256': sha((run/'host-pricing-admission.json').read_bytes()),
                                  'ledger_row_hash': permit['row_hash'], 'ledger_sha256': sha((run/'transport-ledger.ndjson').read_bytes())}
              and before[0]['kind'] == 'activation' and before[0]['purpose'] == 'live' and before[0]['authorization'] == policy['authorization']
              and attempt_identity_bound(run, permit) and s['open_reservations'] == [],
              'live:ledger:permit_and_reconciliation_bound')
    process, http, launched = stage_records(run)
    try: grant_state = 'present' if read_grant(book.slot(permit['reservation_id']), permit, rules) is not None else 'absent'
    except ledger.Failure as error: grant_state = error.code
    a.require(grant_state == 'present' and reconciliation['termination_established'] is ledger.termination_established(process) and reconciliation['launched'] is launched
              and reconciliation['send_outcome'] == 'returned' and http is not None and http['send_outcome'] == 'returned', 'live:ledger:disposition_derived')
    slot_contents(a, run, 'live', rules, permit, reconciliation, book)
    a.cases['live:slot:authoritative_matches_retained'] = a.cases.pop('live:slot:authoritative_matches_retained')
    # mounts: authority as for rehearsals, plus the shared network, the resolver, the public bundle and the operator's file
    command = load(run/'stages/proposal-1/command.json'); argv = command['argv']
    def source(guest, flag):
        hits = [i for i, x in enumerate(argv) if x == guest and i >= 2 and argv[i-2] == flag]
        return argv[hits[0]-1] if len(hits) == 1 else None
    ledger_src, grant_src = source('/ledger.ndjson', '--ro-bind'), source('/grant', '--bind')
    root = ledger_src[:-len(sp['ledger_path'])] if ledger_src and ledger_src.endswith(sp['ledger_path']) else None
    a.require(root is not None and grant_src == root+sp['ledger_slots']+'/'+permit['reservation_id'] and command['grant_slot'] == grant_src
              and Path(ledger_src).name == book.path.name and command['network_namespace'] == 'shared_with_host' and '--unshare-net' not in argv
              and source('/etc/resolv.conf', '--ro-bind') == '/etc/resolv.conf' and source('/ca.pem', '--ro-bind') == policy['tls']['public_ca_bundle']['path']
              and source('/credential', '--ro-bind') is not None and source('/credential', '--ro-bind') not in str(run)
              and source('/policy.json', '--ro-bind') == command['run']+'/transport-policy.json' and argv.count('--bind') == 2
              and all(ns in argv for ns in ('--unshare-user', '--unshare-ipc', '--unshare-pid', '--unshare-uts', '--unshare-cgroup')),
              'live:mounts:authority_and_network_bound')
    started = [r['payload'] for r in rows if r['stage'] == 'proposal-1' and r['event'] == 'stage_started']
    finished = [r['payload'] for r in rows if r['stage'] == 'proposal-1' and r['event'] == 'stage_finished']
    a.require(len(started) == 1 and len(finished) == 1 and finished[0] == process, 'live:receipts:single_pair_bound_to_process')
    body = (out/'serialized-body.json').read_bytes(); server = load(out/'server.json')
    a.require(http['mode'] == 'live' and http['policy_sha256'] == sp['config_sha256'] and http['request_sha256'] == sha(body) and http['request_bytes'] == len(body)
              and http['retries'] == 0 and http['redirects_followed'] == 0 and http['transport_scope'] == 'provider_request' and http['endpoint'] == policy['endpoint']
              and http['ca_bundle_sha256'] == policy['tls']['public_ca_bundle']['sha256'] and http['authorization_present_in_policy'] is True
              and http['fixture_tcp_port'] is None and server['requests'] == [] and http['http_status'] == 200 and http['body_sends_returned'] == 1
              and http['response_sha256'] == sha((out/'provider-response.json').read_bytes()) and http['response_bytes'] == len((out/'provider-response.json').read_bytes())
              and http['tls']['verified'] is True and http['tls']['server_hostname'] == policy['endpoint']['host'] and http['tls']['version'] in ('TLSv1.2', 'TLSv1.3'),
              'live:transport:record_consistent')
    a.require((out/'outbound-body.json').read_bytes() == body and http['outbound_body_sha256'] == sha(body) and not (out/'received-body.json').exists(),
              'live:transport:local_send_checked_remote_unobservable')
    g = read_grant(book.slot(permit['reservation_id']), permit, rules)
    a.require(http['grant_committed'] is True and http['grant_id'] == g['grant_id'] and http['grant_created_at_ns'] == g['at_ns']
              and http['connection_started_at_ns'] <= http['tls_verified_at_ns'] < http['grant_created_at_ns'] < http['grant_durable_at_ns'] < http['header_send_at_ns'],
              'live:grant:ordered_before_first_header_byte')
    receipt = load(run/'credential-receipt.json')
    a.require(receipt['channel'] == 'operator_credential_file' and receipt['http_status'] == 200 and receipt['credential_use_accepted'] is True
              and receipt['exact_receipt'] is None and receipt['credential_commitment_sha256'] == http['credential_commitment_sha256']
              and receipt['commitment_nonce'] == http['commitment_nonce'] and len(http['credential_commitment_sha256']) == 64
              and 'Bearer' not in (out/'http.json').read_text(), 'live:credential_use:recorded_not_exact_receipt')
    proposed, text, metadata, validation, error = budget.interpret(out, request_bytes, True)
    a.require(error is None and validation == load(run/'transport-validation.json') and metadata == load(run/'provider-metadata.json')
              and (run/'response.json').read_bytes() == text and validation['remote_receipt']['checked'] is False and validation['local_send_consistency']['accepted'] is True,
              'live:interpretation:reproduced')
    lifecycle = {'permit': permit, 'reservation': reservation, 'reconciliation': reconciliation, 'reconcile_error': None, 'reservation_state': 'reserved', 'evidence_write_failures': []}
    acct = load(run/'accounting.json')
    a.require(acct == driver.accounting_for(run, policy, True, http, server, lifecycle) and acct['allowance_consumed'] == 1 and acct['live'] is True
              and acct['transmissions_observed'] == 1, 'live:accounting:recomputed')
    # proof
    response = load(run/'response.json'); validated = load(run/'validated-response.json'); raw = load(out/'provider-response.json')
    texts = [c['text'] for item in raw['output'] if item.get('type') == 'message' for c in item['content'] if c.get('type') == 'output_text']
    a.require(response == validated and json.loads(''.join(texts)) == response and response['request_sha256'] == sha(request_bytes), 'live:proof:response_bound')
    problem = json.loads(request_bytes)['problem']; residual, constant = None, None
    rowsp = {row['name']: row for row in problem['rows']}; terms = {}; constant = 0; ok = True
    for entry in response['witness']['coefficients']:
        row, m = rowsp[entry['hypothesis']], int(entry['coefficient']); ok = ok and (row['relation'] == 'eq' or m >= 0)
        constant += m*int(row['constant'])
        for term in row['terms']: terms[term['variable']] = terms.get(term['variable'], 0)+m*int(term['coefficient'])
    residual = {v: c for v, c in terms.items() if c}
    a.require(ok and residual == {} and constant > 0, 'live:proof:witness_contradiction')
    evidence, cert, verdict = load(run/'evidence.json'), load(run/'certificate-verdict.json'), load(run/'verdict.json')
    assembled = next(r['payload'] for r in rows if r['event'] == 'certificate_assembled')
    a.require(evidence['certificate']['payload']['witness_data'] == response['witness'] and cert['accepted'] is True and cert['reason']['kind'] == 'verified_farkas'
              and cert['certificate_hash'] == 'sha256:'+assembled['certificate_sha256'] and assembled['response_sha256'] == sha((run/'validated-response.json').read_bytes())
              and verdict['certificate_validation'] == cert and verdict['request_sha256'] == sha(request_bytes), 'live:proof:certificate_bound')
    named = {r['event']: (r['payload'].get('proposer', r['payload'].get('witness_proposer')), r['payload'].get('route'), r['payload'].get('consumer_route'))
             for r in rows if r['event'] in ('recovery_started', 'certificate_assembled', 'recovery_finished')}
    a.require(named == {'recovery_started': ('live_model_response', sp['name'], None), 'certificate_assembled': ('live_model_response', None, 'openai_responses_http_fixture_v1'),
                        'recovery_finished': ('live_model_response', sp['name'], 'openai_responses_http_fixture_v1')} and verdict['witness_proposer'] == 'live_model_response',
              'live:proof:attribution_live', str(named))
    def receipt_of(stage, event):
        hits = [r['payload'] for r in rows if r['source'] == 'supervisor' and r['stage'] == stage and r['event'] == event]
        if len(hits) != 1: raise ValueError(f'{stage}/{event}: {len(hits)} receipts')
        return hits[0]
    read = lambda n: load(run/n)
    try:
        _, expected = r6.frozen_task(task); challenge = json.loads(request_bytes)['binding']['challenge_sha256']
        if not (read('stages/reconstruct/output/context.json') == read('stages/preparation/output/context.json') == load(task.path/'context/local-context.json')): raise ValueError('context differs')
        if verdict['task_id'] != task.id or verdict['manifest_sha256'] != sha((task.path/'manifest.json').read_bytes()) or not (verdict['challenge_sha256'] == expected['challenge_sha256'] == challenge):
            raise ValueError('target identity differs')
        envelope_proof_audit.audit(task, evidence, verdict, rows, lambda n: run/n, read, receipt_of)
    except (ValueError, AssertionError, KeyError, OSError, gzip.BadGzipFile, EOFError) as error:
        a.require(False, 'live:proof:shared_checker', str(error))
    a.require(True, 'live:proof:shared_checker')
    proved = next(r['payload'] for r in rows if r['event'] == 'proof_validated')
    a.require(proved['proof_accepted'] is True and proved['solution_sha256'] == verdict['solution_sha256'] and proved['verdict_sha256'] == sha((run/'verdict.json').read_bytes())
              and verdict['local_obligation_closed'] is True, 'live:proof:export_recorded')
    a.require(raw['model'] in policy['model']['allowed_response_ids'] and raw['status'] == 'completed', 'live:provider:reported_fields')
    seal_record = seal(a, run, 'live', rows, 'proof'); a.cases['live:seal:retained_hashes'] = a.cases.pop('live:seal:retained_hashes')
    # publication: in live mode the synthetic scan is structural (the canary was never mounted); recompute it and require the terminal to say pending
    nonce = load(run/'credential-canary.json')['nonce']; canary = credential.derive(nonce)
    retained_report = load(run/'publication-scan.json'); final = load(run/'publication-final.json'); fresh = publication.scan([run], canary, nonce)
    a.require(retained_report['accepted'] is True and retained_report['disclosures'] == [] and fresh['accepted'] is True
              and final == publication.final_record(run/'publication-scan.json', canary, nonce), 'live:publication:structural_scan_recomputed')
    summary = load(run/'credential-summary.json'); payload_t = rows[-1]['payload']
    derived_evidence = ((run/'campaign-reconciliation.json').exists() and (run/'ledger-after.ndjson').exists() and (run/'stages/proposal-1/grant').is_dir()
                        and any(r['event'] == 'reservation_reconciled' for r in rows) and summary['reservation_state'] == 'reserved' and summary['ledger_reconciled'] is True)
    a.require(rows[-1]['event'] == 'episode_finished' and payload_t['accepted'] is False and payload_t['publication_pending'] is True and payload_t['publication_accepted'] is None
              and payload_t['proof_accepted'] is True and payload_t['credential_use_accepted'] is True and payload_t['evidence_complete'] is derived_evidence is True
              and payload_t['summary_sha256'] == sha((run/'credential-summary.json').read_bytes())
              and payload_t['publication_scan_sha256'] == sha((run/'publication-scan.json').read_bytes())
              and payload_t['publication_final_sha256'] == sha((run/'publication-final.json').read_bytes())
              and summary['evidence_complete'] is True and acct['evidence_complete'] is True, 'live:terminal:pending_and_commitments_bound')
    a.require(summary['task_id'] == task.id and summary['search_policy'] == sp['name'] and summary['mode'] == 'live' and summary['accounting'] == acct
              and summary['proof_accepted'] is True and summary['credential_use_accepted'] is True and summary['failure_category'] is None, 'live:summary:bound_to_audited_records')
    a.require(seal_record['event_count'] == len(rows) and seal_record['last_event_hash'] == rows[-1]['event_hash'] and seal_record['accepted'] is False,
              'live:seal:chain_and_outcome')
    # the operator scan: the run's commitment and seal, bound by the operator's receipt
    receipts = scan_summary['operator_scan']['run_receipts']; mine = [x for x in receipts if x['run'].get('name') == run.name or x['run']['name_sha256'] == sha(run.name.encode())]
    a.require(scan_summary['accepted'] is True and scan_summary['disclosures'] == [] and scan_summary['incompletely_scanned'] == [] and len(mine) == 1
              and mine[0]['covered_by_scan'] is True and mine[0]['sealed_and_intact'] is True and mine[0]['commitment_record_sealed'] is True and mine[0]['commitment_bound'] is True
              and mine[0]['recorded_commitment_sha256'] == http['credential_commitment_sha256'] and mine[0]['commitment_nonce'] == http['commitment_nonce']
              and mine[0]['seal_sha256'] == sha((run/'seal.json').read_bytes()) and mine[0]['http_sha256'] == sha((out/'http.json').read_bytes())
              and mine[0]['read_failures'] == 0, 'live:operator_scan:bound_to_commitment_and_seal')
    a.require(s['reservations'] == 1 and s['transmissions_consumed'] == 1 and s['maximum_transmissions'] == policy['authorization']['maximum_transmissions'] == 1
              and [r['kind'] for r in rows_ledger] == ['activation', 'reservation', 'send_grant'], 'live:campaign:one_transmission_under_signed_authorization')
    missing = sorted(set(LIVE_CASES)-set(a.cases)); extra = sorted(set(a.cases)-set(LIVE_CASES))
    if missing or extra: raise Rejection('cases:population', f'missing {missing} extra {extra}')
    export = verdict['solution_sha256']
    return {'accepted_with_operator_scan': all(a.cases.values()), 'cases': a.cases, 'case_count': len(LIVE_CASES),
            'witness': response['witness'], 'positive_constant': str(constant), 'proof_export_sha256': export,
            'export_identity': LIVE_EXPORTS.get(export[:16], 'not a previously recorded export'),
            'provider_reported': {'model': raw['model'], 'status': raw['status'], 'id': raw['id'], 'service_tier': raw.get('service_tier'), 'usage': raw['usage']},
            'priced_ceiling_micro_usd': acct['priced_usage_ceiling_micro_usd'], 'grant_durable_before_header_ns': http['header_send_at_ns']-http['grant_durable_at_ns'],
            'live_ledger': {k: s[k] for k in ('purpose', 'reservations', 'transmissions_consumed', 'open_reservations', 'committed_micro_usd')},
            'operator_scan_report_sha256': scan_summary['full_report_sha256'], 'policy_sha256': sp['config_sha256'], 'source_lock_sha256': sp['source_lock_sha256'],
            'program_sha256': sha(Path(__file__).read_bytes()), 'live_model_calls': 0, 'credentials_read': 0,
            'scope': 'historical audit of one signed transmission over retained bytes; no native execution, verifier run or inference; provider fields are provider claims'}


def live_main(argv):
    parser = argparse.ArgumentParser(description='Audit one signed live run')
    parser.add_argument('--live-run', type=Path, required=True)
    parser.add_argument('--ledgers', type=Path, default=ROOT/'ledgers')
    parser.add_argument('--operator-scan-summary', type=Path, required=True)
    parser.add_argument('--checkpoint', type=Path, default=ROOT/'policies/responses-campaign-v7.checkpoint.json', help='the disabled policy bytes the signature was applied to')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args(argv)
    if args.output and args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    try: result = live_audit(args.live_run.resolve(), args.ledgers.resolve(), load(args.operator_scan_summary), args.checkpoint.resolve())
    except Rejection as rejection:
        print(json.dumps({'accepted_with_operator_scan': False, 'rejected_case': rejection.case, 'detail': str(rejection)}, indent=1)); sys.exit(1)
    if args.output: r6.write_json(args.output, result)
    print(json.dumps({k: result[k] for k in ('accepted_with_operator_scan', 'case_count', 'witness', 'proof_export_sha256', 'export_identity', 'priced_ceiling_micro_usd', 'live_ledger')}, indent=1))
    sys.exit(0 if result['accepted_with_operator_scan'] else 1)


if __name__ == '__main__' and '--live-run' in sys.argv:
    live_main(sys.argv[1:])
