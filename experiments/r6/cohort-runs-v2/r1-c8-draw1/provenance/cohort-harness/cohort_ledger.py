"""Campaign ledger with a stable identity: one directory per campaign, many authorization revisions.

R6-008's ledger was keyed by policy digest, so a pricing refresh — a new policy
file — would have started a fresh allocation. Here the key is a campaign
identity chosen at first activation and carried into every revision. Each
signed or refreshed policy is *registered* as an authorization revision bound
to that identity; reservations are admitted only under the latest registered
revision; consumed (task, draw) slots stay consumed across revisions; the
scientific contract is pinned at activation and may not change. Distinct
campaigns may share a contract and are distinct directories.

The allowance is a finite schedule of (task, draw) slots with a global money
cap and a per-slot pre-send retry limit. Grants, releases, unknown outcomes,
markers, torn-marker repair and termination evidence are R6-008's, imported.
This module has no harness imports so that the actor can verify its permit
inside the sandbox with the same code.
"""
import json
import os
from pathlib import Path
import time
import uuid

import campaign_ledger as base

Failure, require, canonical, sha, digest = base.Failure, base.require, base.canonical, base.sha, base.digest
fsync_directory, write_exclusive, write_all = base.fsync_directory, base.write_exclusive, base.write_all
grant_record, commit_grant, read_grant, slot_open, termination_established = base.grant_record, base.commit_grant, base.read_grant, base.slot_open, base.termination_established
GRANT_FILE, MARKERS, TERMINAL, PURPOSES = base.GRANT_FILE, base.MARKERS, base.TERMINAL, base.PURPOSES
DOMAIN = 'r6-cohort-ledger-1'
KINDS = ('activation', 'authorization_revision', 'reservation', 'send_grant', 'release', 'unknown')
AUTHORIZATION_KEYS = ('approved_by', 'approved_utc', 'scope', 'model_id', 'schedule', 'maximum_micro_usd', 'maximum_presend_attempts')
ZERO = '0'*64


def authorization_scope(policy):
    """The complete scope, enforced identically by host and actor. The schedule is the allowance."""
    require(policy.get('live_enabled') is True, 'cohort_live_disabled')
    record = policy.get('authorization')
    require(isinstance(record, dict) and tuple(sorted(record)) == tuple(sorted(AUTHORIZATION_KEYS)), 'cohort_authorization_absent')
    require(isinstance(record['approved_by'], str) and record['approved_by'].strip() != '', 'cohort_authorization_approver')
    require(isinstance(record['approved_utc'], str) and record['approved_utc'].endswith('Z') and len(record['approved_utc']) == 20, 'cohort_authorization_timestamp')
    require(isinstance(record['scope'], str) and record['scope'].strip() != '', 'cohort_authorization_scope_text')
    require(record['model_id'] == policy['model']['requested_id'], 'cohort_authorization_subject')
    schedule = record['schedule']
    require(isinstance(schedule, dict) and schedule and all(isinstance(t, str) and t and isinstance(n, int) and not isinstance(n, bool) and n >= 1
                                                            for t, n in schedule.items()), 'cohort_authorization_schedule')
    for key in ('maximum_micro_usd', 'maximum_presend_attempts'):
        require(isinstance(record[key], int) and not isinstance(record[key], bool) and record[key] >= 1, 'cohort_authorization_'+key)
    require(record['schedule'] == policy['campaign']['schedule'], 'cohort_authorization_schedule_binding')
    require(record['maximum_micro_usd'] == policy['limits']['total_micro_usd'], 'cohort_authorization_money')
    require(record['maximum_presend_attempts'] == policy['limits']['maximum_presend_attempts'], 'cohort_authorization_presend')
    return record


def expected_activation(policy, live):
    if live: return 'live', authorization_scope(policy)
    return 'rehearsal', policy['campaign']['rehearsal_authorization']


def parse(raw):
    require(raw.endswith(b'\n') or raw == b'', 'cohort_ledger_partial_append')
    rows, previous = [], ZERO
    for line in raw.splitlines():
        row = json.loads(line); recorded = row.pop('row_hash')
        require(row.get('domain') == DOMAIN and row.get('sequence') == len(rows) and row.get('previous_hash') == previous
                and row.get('kind') in KINDS and digest(row) == recorded, 'cohort_ledger_chain')
        row['row_hash'] = recorded; rows.append(row); previous = recorded
    require(bool(rows) and rows[0]['kind'] == 'activation' and rows[0].get('purpose') in PURPOSES, 'cohort_ledger_not_activated')
    return rows


def state(rows, campaign_id):
    activation = rows[0]
    require(activation['campaign_id'] == campaign_id, 'cohort_ledger_campaign_mismatch')
    revisions = [activation]+[r for r in rows[1:] if r['kind'] == 'authorization_revision']
    current = revisions[-1]
    reservations, terminal = {}, {}
    for row in rows[1:]:
        if row['kind'] == 'reservation':
            require(row['reservation_id'] not in reservations, 'cohort_ledger_duplicate_reservation'); reservations[row['reservation_id']] = row
        elif row['kind'] in TERMINAL:
            require(row['reservation_id'] in reservations and row['reservation_id'] not in terminal, 'cohort_ledger_orphan_terminal'); terminal[row['reservation_id']] = row
    slots = {}
    for rid, res in reservations.items():
        key = (res['task_id'], res['draw']); slot = slots.setdefault(key, {'consumed': False, 'released': 0, 'open': None, 'reservations': 0})
        slot['reservations'] += 1; t = terminal.get(rid)
        if t is None: slot['open'] = rid
        elif t['kind'] in ('send_grant', 'unknown'): slot['consumed'] = True
        else: slot['released'] += 1
    consumed = sum(1 for s in slots.values() if s['consumed'])
    committed = sum(reservations[r]['reserved_micro_usd'] for r in reservations if r not in terminal or terminal[r]['kind'] != 'release')
    return {'campaign_id': campaign_id, 'purpose': activation['purpose'], 'contract_sha256': activation['contract_sha256'],
            'schedule': current['schedule'], 'authorization': current['authorization'], 'policy_sha256': current['policy_sha256'],
            'revision': len(revisions)-1, 'revisions': [r['policy_sha256'] for r in revisions],
            'maximum_micro_usd': current['maximum_micro_usd'], 'maximum_presend_attempts': current['maximum_presend_attempts'],
            'slots': {f'{t}/{d}': v for (t, d), v in slots.items()}, 'transmissions_consumed': consumed,
            'maximum_transmissions': sum(current['schedule'].values()), 'committed_micro_usd': committed,
            'open_reservations': [rid for rid in reservations if rid not in terminal], 'rows': len(rows), 'last_hash': rows[-1]['row_hash']}


def check_activation(s, policy, live):
    """The ledger serves this policy: same campaign, same contract, this policy registered as the current revision, purpose by mode."""
    purpose, authorization = expected_activation(policy, live)
    require(s['purpose'] == purpose, 'cohort_activation_purpose')
    require(s['contract_sha256'] == policy['contract_sha256'], 'cohort_activation_contract')
    require(s['campaign_id'] == policy['campaign']['id'], 'cohort_activation_campaign')
    require(s['policy_sha256'] == sha(canonical(policy)+b'\n'), 'cohort_revision_not_current')
    require(s['authorization'] == authorization and s['schedule'] == authorization['schedule'], 'cohort_activation_authorization')


def verify_permit(permit, raw, policy, live, episode_id, task_id, draw):
    rows = parse(raw); s = state(rows, policy['campaign']['id']); check_activation(s, policy, live)
    last = rows[-1]
    require(permit == last and last['kind'] == 'reservation', 'cohort_permit_not_last_row')
    require(last['episode_id'] == episode_id and last['policy_sha256'] == s['policy_sha256'] and last['task_id'] == task_id and last['draw'] == draw,
            'cohort_permit_binding')
    require(s['open_reservations'] == [last['reservation_id']], 'cohort_permit_not_open')
    slot = s['slots'][f'{task_id}/{draw}']
    require(not slot['consumed'], 'cohort_slot_consumed')
    require(s['committed_micro_usd'] <= s['maximum_micro_usd'], 'cohort_money_exhausted')
    return s


class Ledger:
    """Host side. `directory` is the campaign directory; identity lives in the rows, not the path."""

    def __init__(self, directory, campaign_id):
        self.directory = Path(directory); self.campaign_id = campaign_id
        self.path = self.directory/'ledger.ndjson'; self.head = self.directory/'head.json'; self.lock_path = self.directory/'ledger.lock'
        self.slots = self.directory/'slots'

    def slot(self, task_id, draw): return self.slots/task_id/str(draw)

    _Lock = base.Ledger._Lock

    def _locked(self):
        self.directory.mkdir(parents=True, exist_ok=True)
        return self._Lock(self.lock_path)

    def _write_head(self, rows, last_hash):
        temp = self.head.with_suffix('.json.tmp')
        temp.write_bytes(canonical({'campaign_id': self.campaign_id, 'rows': rows, 'last_hash': last_hash})+b'\n')
        fd = os.open(temp, os.O_RDONLY)
        try: os.fsync(fd)
        finally: os.close(fd)
        os.replace(temp, self.head); fsync_directory(self.directory)

    def activate(self, policy, live, activated_at_unix=None):
        purpose, authorization = expected_activation(policy, live)
        require(not self.path.exists() and not self.head.exists(), 'cohort_ledger_already_activated')
        row = {'domain': DOMAIN, 'sequence': 0, 'previous_hash': ZERO, 'kind': 'activation', 'purpose': purpose, 'campaign_id': self.campaign_id,
               'contract_sha256': policy['contract_sha256'], 'policy_sha256': sha(canonical(policy)+b'\n'), 'authorization': dict(authorization),
               'schedule': dict(authorization['schedule']), 'maximum_micro_usd': authorization['maximum_micro_usd'],
               'maximum_presend_attempts': authorization['maximum_presend_attempts'],
               'activated_at_unix': int(time.time()) if activated_at_unix is None else activated_at_unix}
        row['row_hash'] = digest(row)
        with self._locked():
            self.slots.mkdir(exist_ok=True); write_exclusive(self.path, canonical(row)+b'\n'); self._write_head(1, row['row_hash'])
        return row

    def _rows(self):
        require(self.head.exists(), 'cohort_ledger_not_activated')
        head = json.loads(self.head.read_bytes())
        require(self.path.exists(), 'cohort_ledger_missing_after_activation')
        raw = self.path.read_bytes()
        if raw and not raw.endswith(b'\n'):
            complete = raw[:raw.rfind(b'\n')+1]; rows = parse(complete)
            require(len(rows) >= head['rows'] and rows[head['rows']-1]['row_hash'] == head['last_hash'], 'cohort_ledger_truncated')
            fd = os.open(self.path, os.O_WRONLY)
            try: os.ftruncate(fd, len(complete)); os.fsync(fd)
            finally: os.close(fd)
            self.recovered_partial_append = True; raw = complete
        rows = parse(raw)
        require(len(rows) >= head['rows'] and rows[head['rows']-1]['row_hash'] == head['last_hash'], 'cohort_ledger_truncated')
        return rows

    def _append(self, rows, row):
        row = {**row, 'domain': DOMAIN, 'sequence': len(rows), 'previous_hash': rows[-1]['row_hash']}; row['row_hash'] = digest(row)
        fd = os.open(self.path, os.O_WRONLY | os.O_APPEND)
        try: write_all(fd, canonical(row)+b'\n'); os.fsync(fd)
        finally: os.close(fd)
        self._write_head(len(rows)+1, row['row_hash'])
        return row

    def snapshot(self):
        with self._locked():
            rows = self._rows(); return self.path.read_bytes(), state(rows, self.campaign_id)

    def register_revision(self, policy, live):
        """A refreshed or re-signed policy joins the campaign: same identity, same contract, same purpose, same or larger schedule; consumed slots stay."""
        purpose, authorization = expected_activation(policy, live)
        with self._locked():
            rows = self._rows(); s = state(rows, self.campaign_id)
            require(s['purpose'] == purpose and s['contract_sha256'] == policy['contract_sha256'] and policy['campaign']['id'] == self.campaign_id, 'cohort_revision_identity')
            require(s['open_reservations'] == [], 'cohort_revision_while_open')
            new = sha(canonical(policy)+b'\n')
            require(new not in s['revisions'], 'cohort_revision_already_registered')
            for task, n in s['schedule'].items():
                require(authorization['schedule'].get(task, 0) >= n, 'cohort_revision_schedule_shrunk')
            require(authorization['maximum_micro_usd'] >= s['committed_micro_usd'], 'cohort_revision_money_below_committed')
            return self._append(rows, {'kind': 'authorization_revision', 'policy_sha256': new, 'authorization': dict(authorization),
                                       'schedule': dict(authorization['schedule']), 'maximum_micro_usd': authorization['maximum_micro_usd'],
                                       'maximum_presend_attempts': authorization['maximum_presend_attempts'], 'registered_at_unix': int(time.time())})

    def find_open(self, attempt_id):
        with self._locked():
            rows = self._rows(); s = state(rows, self.campaign_id)
            hits = [r for r in rows if r['kind'] == 'reservation' and r.get('attempt_id') == attempt_id]
            require(len(hits) <= 1, 'cohort_ledger_duplicate_attempt')
            if not hits: return None
            require(hits[0]['reservation_id'] in s['open_reservations'], 'cohort_reservation_not_open')
            return hits[0]

    def find_terminal(self, reservation_id):
        with self._locked():
            rows = self._rows(); hits = [r for r in rows if r['kind'] in TERMINAL and r['reservation_id'] == reservation_id]
            return hits[0] if hits else None

    def reserve(self, episode_id, policy, task_id, draw, reservation, bindings, pricing_admission, attempt_id=None):
        """One (task, draw) slot under the current revision: not consumed, retries within the pre-send limit, money within the cap."""
        require(isinstance(episode_id, str) and episode_id != '', 'cohort_missing_episode_identity')
        attempt_id = attempt_id or uuid.uuid4().hex
        with self._locked():
            rows = self._rows(); s = state(rows, self.campaign_id)
            require(s['policy_sha256'] == sha(canonical(policy)+b'\n'), 'cohort_revision_not_current')
            require(s['open_reservations'] == [], 'cohort_reservation_open')
            require(task_id in s['schedule'] and isinstance(draw, int) and 1 <= draw <= s['schedule'][task_id], 'cohort_slot_not_scheduled')
            slot = s['slots'].get(f'{task_id}/{draw}', {'consumed': False, 'released': 0})
            require(not slot['consumed'], 'cohort_slot_consumed')
            require(slot['released'] < s['maximum_presend_attempts'], 'cohort_presend_attempts_exhausted')
            require(s['committed_micro_usd']+reservation['reserved_micro_usd'] <= s['maximum_micro_usd'], 'cohort_money_exhausted')
            reservation_id = uuid.uuid4().hex
            # Every newly created path component is made durable, child before parent, before the reservation can authorize a sender.
            task_dir = self.slots/task_id; draw_dir = task_dir/str(draw); attempt_dir = draw_dir/reservation_id
            created = []
            for path, parent in ((task_dir, self.slots), (draw_dir, task_dir), (attempt_dir, draw_dir)):
                if not path.exists(): path.mkdir(exist_ok=False); created.append((path, parent))
            for path, parent in reversed(created): fsync_directory(path); fsync_directory(parent)  # deepest first, each parent after its child
            row = self._append(rows, {'kind': 'reservation', 'reservation_id': reservation_id, 'attempt_id': attempt_id, 'episode_id': episode_id,
                                      'task_id': task_id, 'draw': draw, 'slot_attempt': slot['released']+1, 'policy_sha256': s['policy_sha256'],
                                      **bindings, 'reserved_micro_usd': reservation['reserved_micro_usd'], 'reservation': reservation,
                                      'pricing_admission': pricing_admission, 'reserved_at_unix': int(time.time())})
            return row, self.path.read_bytes()

    def grant_slot(self, permit):
        """Each reservation attempt has its own authoritative slot directory under the (task, draw) slot."""
        return self.slot(permit['task_id'], permit['draw'])/permit['reservation_id']

    def reconcile(self, permit, process_record, http_record, evidence, launched=True):
        """R6-008's disposition rules over the attempt's authoritative slot."""
        with self._locked():
            rows = self._rows(); s = state(rows, self.campaign_id)
            require(permit['reservation_id'] in s['open_reservations'], 'cohort_reservation_not_open')
            slot = self.grant_slot(permit)
            base_row = {'reservation_id': permit['reservation_id'], 'episode_id': permit['episode_id'], 'task_id': permit['task_id'], 'draw': permit['draw'],
                        'evidence': evidence, 'launched': bool(launched), 'termination_established': termination_established(process_record),
                        'reconciled_at_unix': int(time.time())}
            existing = [m for m in ('release.json', 'unknown.json') if (slot/m).exists()]
            valid, torn = [], []
            for m in existing:
                try:
                    value = json.loads((slot/m).read_bytes())
                    bound = (isinstance(value, dict) and value.get('kind') == m[:-5] and value.get('reservation_id') == permit['reservation_id']
                             and isinstance(value.get('reconciled_at_unix'), int))
                except (ValueError, OSError): bound = False
                (valid if bound else torn).append(m)
            try: grant = read_grant(slot, permit)
            except Failure as unreadable: grant, base_row = None, {**base_row, 'grant_state': unreadable.code}
            if grant is not None:
                outcome = (http_record or {}).get('send_outcome')
                row = {**base_row, 'kind': 'send_grant', 'grant': grant, 'send_outcome': outcome if outcome in ('returned', 'unknown') else 'unknown'}; marker = None
            elif valid:
                row = {**base_row, 'kind': valid[0][:-5], 'reason': 'completed_from_marker', 'recovered': True}; marker = valid[0]
                if torn: row['torn_marker'] = torn[0]
            elif torn:
                require('unknown.json' not in torn, 'cohort_marker_torn_unrecoverable')
                row = {**base_row, 'kind': 'unknown', 'reason': 'torn_marker', 'torn_marker': torn[0], 'recovered': True}; marker = 'unknown.json'; existing = []
            elif 'grant_state' in base_row:
                row = {**base_row, 'kind': 'unknown', 'reason': 'grant file present but unreadable or unbound'}; marker = 'unknown.json'
            elif not launched and process_record is None and http_record is None:
                row = {**base_row, 'kind': 'release', 'reason': 'pre_launch_failure', 'failure_category': None, 'transport_record_present': False}; marker = 'release.json'
            elif base_row['termination_established'] and (http_record is None or (http_record.get('body_sends_started') == 0 and http_record.get('header_sends_started') == 0)):
                row = {**base_row, 'kind': 'release', 'reason': 'pre_send_failure_with_established_termination',
                       'failure_category': None if http_record is None else http_record.get('failure_category'),
                       'transport_record_present': http_record is not None}; marker = 'release.json'
            else:
                row = {**base_row, 'kind': 'unknown', 'reason': 'no grant, but termination is not established or the counters contradict the missing grant'}; marker = 'unknown.json'
            if marker is not None and not existing:
                write_exclusive(slot/marker, canonical({'kind': row['kind'], 'reservation_id': permit['reservation_id'], 'reconciled_at_unix': base_row['reconciled_at_unix']})+b'\n')
            row['marker_sha256'] = sha((slot/(marker or GRANT_FILE)).read_bytes())
            row = self._append(rows, row)
            return row, self.path.read_bytes()
