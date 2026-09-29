"""Authorization-scoped campaign ledger: one file per approved policy digest.

The digest names the final approved policy bytes, authorization scope included,
so a changed policy is a different ledger with no activation and no spending
authority. Every run under the same authorization resolves to the same file.
Rows form a hash chain. The allowance counts *transmissions*: a reservation
holds money and a slot; a durable single-use send grant, written by the sender
into the reservation's authoritative slot immediately before the first header
byte, consumes the slot; a release returns it only when no grant exists and the
sender's termination is established by validated supervisor evidence. Any
other outcome is `unknown` and stays consumed.

Authority lives here, not in run directories: the slot for a reservation is a
directory beside the ledger, created at reservation time, mounted into the
sender, and closed by a terminal marker at reconciliation. A replayed permit,
a stale snapshot or a fresh run directory therefore cannot obtain a second
grant. Activation records its purpose and the exact authorization it serves,
and a permit is admissible only to a sender whose policy carries that same
authorization. This module has no harness imports so that the actor can run
the same checks inside the sandbox. It protects against harness errors within
trusted local state; it does not resist an operator rolling that state back.
"""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import time
import uuid

DOMAIN = 'r6-campaign-ledger-2'
GRANT_DOMAIN = 'r6-campaign-send-grant-2'
KINDS = ('activation', 'reservation', 'send_grant', 'release', 'unknown')
TERMINAL = ('send_grant', 'release', 'unknown')
PURPOSES = ('live', 'rehearsal')
AUTHORIZATION_KEYS = ('approved_by', 'approved_utc', 'scope', 'model_id', 'maximum_transmissions',
                      'maximum_micro_usd', 'maximum_presend_attempts')
GRANT_FILE, MARKERS = 'send-grant.json', ('send-grant.json', 'release.json', 'unknown.json')
ZERO = '0'*64


class Failure(ValueError):
    def __init__(self, code):
        super().__init__(code); self.code = code


def require(ok, code):
    if not ok: raise Failure(code)


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode()


def sha(data): return hashlib.sha256(data).hexdigest()
def digest(row): return sha(canonical(row))


def fsync_directory(path):
    fd = os.open(path, os.O_RDONLY)
    try: os.fsync(fd)
    finally: os.close(fd)


def write_all(fd, data):
    """Every byte or an exception: short writes are completed, a stalled write is refused."""
    view, written = memoryview(data), 0
    while written < len(data):
        progress = os.write(fd, view[written:])
        require(isinstance(progress, int) and progress > 0, 'campaign_write_stalled')
        written += progress
    return written


def write_exclusive(path, data):
    """Create-or-fail, write every byte, then fsync file and directory.

    Once the name exists it stays: a failure after a partial write leaves a marker that reconciliation treats as
    an unreadable grant, so the uncertainty is consumed rather than released."""
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        written = write_all(fd, data); os.fsync(fd)
    finally:
        os.close(fd)
    fsync_directory(Path(path).parent)
    return written


def authorization_scope(policy):
    """The complete scope, enforced identically by host and actor."""
    require(policy.get('live_enabled') is True, 'campaign_live_disabled')
    record = policy.get('authorization')
    require(isinstance(record, dict) and tuple(sorted(record)) == tuple(sorted(AUTHORIZATION_KEYS)), 'campaign_authorization_absent')
    require(isinstance(record['approved_by'], str) and record['approved_by'].strip() != '', 'campaign_authorization_approver')
    require(isinstance(record['approved_utc'], str) and record['approved_utc'].endswith('Z') and len(record['approved_utc']) == 20,
            'campaign_authorization_timestamp')
    require(isinstance(record['scope'], str) and record['scope'].strip() != '', 'campaign_authorization_scope_text')
    require(record['model_id'] == policy['model']['requested_id'], 'campaign_authorization_subject')
    limits = policy['limits']
    for key in ('maximum_transmissions', 'maximum_micro_usd', 'maximum_presend_attempts'):
        require(isinstance(record[key], int) and not isinstance(record[key], bool) and record[key] >= 1, 'campaign_authorization_'+key)
    require(record['maximum_transmissions'] == limits['maximum_transmissions'], 'campaign_authorization_transmissions')
    require(record['maximum_micro_usd'] == limits['total_micro_usd'], 'campaign_authorization_money')
    require(record['maximum_presend_attempts'] == limits['maximum_presend_attempts'], 'campaign_authorization_presend')
    return record


def expected_activation(policy, live):
    """What a ledger's activation must serve for this policy and mode."""
    if live: return 'live', authorization_scope(policy)
    return 'rehearsal', policy['ledger']['rehearsal_authorization']


def parse(raw):
    require(raw.endswith(b'\n') or raw == b'', 'campaign_ledger_partial_append')
    rows, previous = [], ZERO
    for line in raw.splitlines():
        row = json.loads(line)
        recorded = row.pop('row_hash')
        require(row.get('domain') == DOMAIN and row.get('sequence') == len(rows) and row.get('previous_hash') == previous
                and row.get('kind') in KINDS and digest(row) == recorded, 'campaign_ledger_chain')
        row['row_hash'] = recorded; rows.append(row); previous = recorded
    require(bool(rows) and rows[0]['kind'] == 'activation' and rows[0].get('purpose') in PURPOSES, 'campaign_ledger_not_activated')
    return rows


def state(rows, policy_sha256):
    activation = rows[0]
    require(activation['policy_sha256'] == policy_sha256, 'campaign_ledger_policy_mismatch')
    reservations, terminal = {}, {}
    for row in rows[1:]:
        if row['kind'] == 'reservation':
            require(row['reservation_id'] not in reservations, 'campaign_ledger_duplicate_reservation')
            reservations[row['reservation_id']] = row
        else:
            require(row['reservation_id'] in reservations and row['reservation_id'] not in terminal, 'campaign_ledger_orphan_terminal')
            terminal[row['reservation_id']] = row
    consumed = [r for r, t in terminal.items() if t['kind'] in ('send_grant', 'unknown')]
    released = [r for r, t in terminal.items() if t['kind'] == 'release']
    open_ = [r for r in reservations if r not in terminal]
    committed = sum(reservations[r]['reserved_micro_usd'] for r in reservations if r not in released)
    return {'policy_sha256': policy_sha256, 'purpose': activation['purpose'], 'authorization': activation['authorization'],
            'maximum_transmissions': activation['maximum_transmissions'], 'maximum_micro_usd': activation['maximum_micro_usd'],
            'maximum_presend_attempts': activation['maximum_presend_attempts'],
            'reservations': len(reservations), 'transmissions_consumed': len(consumed), 'presend_attempts_used': len(released),
            'unknown_outcomes': sum(1 for t in terminal.values() if t['kind'] == 'unknown'),
            'committed_micro_usd': committed, 'open_reservations': open_, 'rows': len(rows), 'last_hash': rows[-1]['row_hash']}


def check_activation(s, policy, live):
    """The activation serves exactly this policy's authorization for this mode; a directory name is not a binding."""
    purpose, authorization = expected_activation(policy, live)
    require(s['purpose'] == purpose, 'campaign_activation_purpose')
    require(s['authorization'] == authorization, 'campaign_activation_authorization')
    require(s['maximum_transmissions'] == authorization['maximum_transmissions'] and s['maximum_micro_usd'] == authorization['maximum_micro_usd']
            and s['maximum_presend_attempts'] == authorization['maximum_presend_attempts'], 'campaign_activation_limits')


def verify_permit(permit, raw, policy_sha256, episode_id, policy, live):
    """Actor side: the permit is the ledger's open last row for this episode, under an activation bound to the policy."""
    rows = parse(raw)
    s = state(rows, policy_sha256)
    check_activation(s, policy, live)
    last = rows[-1]
    require(permit == last and last['kind'] == 'reservation', 'campaign_permit_not_last_row')
    require(last['episode_id'] == episode_id and last['policy_sha256'] == policy_sha256, 'campaign_permit_binding')
    require(s['open_reservations'] == [last['reservation_id']], 'campaign_permit_not_open')
    require(s['transmissions_consumed'] < s['maximum_transmissions'], 'campaign_transmissions_exhausted')
    require(s['committed_micro_usd'] <= s['maximum_micro_usd'], 'campaign_money_exhausted')
    return s


def slot_open(directory):
    """A slot with any marker is closed; a missing slot is not a slot."""
    directory = Path(directory)
    require(directory.is_dir(), 'campaign_grant_slot_missing')
    require(not any((directory/m).exists() for m in MARKERS) and not any(p.name.endswith('.tmp') for p in directory.iterdir()),
            'campaign_grant_slot_used')


def grant_record(permit, at_ns):
    return {'domain': GRANT_DOMAIN, 'reservation_id': permit['reservation_id'], 'grant_id': uuid.uuid4().hex,
            'policy_sha256': permit['policy_sha256'], 'request_sha256': permit['request_sha256'],
            'episode_id': permit['episode_id'], 'at_ns': at_ns}


def commit_grant(directory, record):
    """Exactly one creator: O_EXCL on the final name, every byte written, then fsync of file and directory."""
    slot_open(directory)
    data = canonical(record)+b'\n'
    try:
        written = write_exclusive(Path(directory)/GRANT_FILE, data)
    except FileExistsError:
        raise Failure('campaign_grant_slot_used')
    require(written == len(data), 'campaign_grant_incomplete')
    return time.monotonic_ns()


def read_grant(directory, permit):
    """None if absent; the record if present and bound; a Failure if present but unreadable or unbound."""
    final = Path(directory)/GRANT_FILE
    if not final.exists(): return None
    try: record = json.loads(final.read_bytes())
    except (ValueError, OSError): raise Failure('campaign_grant_unreadable')
    require(isinstance(record, dict) and record.get('domain') == GRANT_DOMAIN and record.get('reservation_id') == permit['reservation_id']
            and record.get('policy_sha256') == permit['policy_sha256'] and record.get('episode_id') == permit['episode_id']
            and record.get('request_sha256') == permit['request_sha256'], 'campaign_grant_binding')
    return record


def termination_established(process):
    """Validated supervisor evidence that the whole sandbox workload ended; a filename or exit code alone is not it."""
    return (isinstance(process, dict) and isinstance(process.get('exit_code'), int) and not isinstance(process.get('exit_code'), bool)
            and process.get('workload_empty_after_cleanup') is True and process.get('monitor_error') is None
            and process.get('observation_error') is None and process.get('accounting_scope') == 'sandbox_process_tree')


class Ledger:
    """Host side. One process at a time: every read-modify-write holds an exclusive lock."""

    def __init__(self, directory, policy_sha256):
        self.directory = Path(directory); self.policy_sha256 = policy_sha256
        self.path = self.directory/(policy_sha256+'.ndjson')
        self.head = self.directory/(policy_sha256+'.head.json')
        self.lock_path = self.directory/(policy_sha256+'.lock')
        self.slots = self.directory/(policy_sha256+'.slots')

    def slot(self, reservation_id):
        return self.slots/reservation_id

    class _Lock:
        def __init__(self, path): self.path = path; self.fd = None
        def __enter__(self):
            self.fd = os.open(self.path, os.O_RDWR | os.O_CREAT, 0o600); fcntl.flock(self.fd, fcntl.LOCK_EX); return self
        def __exit__(self, *unused):
            fcntl.flock(self.fd, fcntl.LOCK_UN); os.close(self.fd)

    def _locked(self):
        self.directory.mkdir(parents=True, exist_ok=True)
        return self._Lock(self.lock_path)

    def _write_head(self, rows, last_hash):
        temp = self.head.with_suffix('.json.tmp')
        temp.write_bytes(canonical({'policy_sha256': self.policy_sha256, 'rows': rows, 'last_hash': last_hash})+b'\n')
        fd = os.open(temp, os.O_RDONLY)
        try: os.fsync(fd)
        finally: os.close(fd)
        os.replace(temp, self.head)
        fsync_directory(self.directory)

    def activate(self, authorization, purpose, activated_at_unix=None):
        require(purpose in PURPOSES, 'campaign_activation_purpose')
        require(not self.path.exists() and not self.head.exists(), 'campaign_ledger_already_activated')
        row = {'domain': DOMAIN, 'sequence': 0, 'previous_hash': ZERO, 'kind': 'activation', 'purpose': purpose,
               'policy_sha256': self.policy_sha256, 'authorization': dict(authorization),
               'maximum_transmissions': authorization['maximum_transmissions'], 'maximum_micro_usd': authorization['maximum_micro_usd'],
               'maximum_presend_attempts': authorization['maximum_presend_attempts'],
               'activated_at_unix': int(time.time()) if activated_at_unix is None else activated_at_unix}
        row['row_hash'] = digest(row)
        with self._locked():
            self.slots.mkdir(exist_ok=True)
            write_exclusive(self.path, canonical(row)+b'\n')
            self._write_head(1, row['row_hash'])
        return row

    def _rows(self):
        """The head is a floor: rows beyond it are appends whose head write did not complete; a partial trailing line is an
        append that never completed and is discarded, since the head only advances after a complete, fsynced append."""
        require(self.head.exists(), 'campaign_ledger_not_activated')
        head = json.loads(self.head.read_bytes())
        require(self.path.exists(), 'campaign_ledger_missing_after_activation')
        raw = self.path.read_bytes()
        if raw and not raw.endswith(b'\n'):
            complete = raw[:raw.rfind(b'\n')+1]
            rows = parse(complete)
            require(len(rows) >= head['rows'] and rows[head['rows']-1]['row_hash'] == head['last_hash'], 'campaign_ledger_truncated')
            fd = os.open(self.path, os.O_WRONLY)
            try: os.ftruncate(fd, len(complete)); os.fsync(fd)
            finally: os.close(fd)
            self.recovered_partial_append = True
            raw = complete
        rows = parse(raw)
        require(len(rows) >= head['rows'] and rows[head['rows']-1]['row_hash'] == head['last_hash'], 'campaign_ledger_truncated')
        return rows  # a head behind the rows is caught up by the next append; reading never writes the head (it may truncate a partial tail)

    def _append(self, rows, row):
        row = {**row, 'domain': DOMAIN, 'sequence': len(rows), 'previous_hash': rows[-1]['row_hash']}
        row['row_hash'] = digest(row)
        fd = os.open(self.path, os.O_WRONLY | os.O_APPEND)
        try: write_all(fd, canonical(row)+b'\n'); os.fsync(fd)
        finally: os.close(fd)
        self._write_head(len(rows)+1, row['row_hash'])  # only after the complete, durable append
        return row

    def find_open(self, attempt_id):
        """Recovery after an uncertain reserve(): the open reservation carrying this attempt identity, if the append committed."""
        with self._locked():
            rows = self._rows(); s = state(rows, self.policy_sha256)
            hits = [r for r in rows if r['kind'] == 'reservation' and r.get('attempt_id') == attempt_id]
            require(len(hits) <= 1, 'campaign_ledger_duplicate_attempt')
            if not hits: return None
            require(hits[0]['reservation_id'] in s['open_reservations'], 'campaign_reservation_not_open')
            return hits[0]

    def find_terminal(self, reservation_id):
        """Recovery after an uncertain reconcile(): the terminal row for this reservation, if the append committed."""
        with self._locked():
            rows = self._rows()
            hits = [r for r in rows if r['kind'] in TERMINAL and r['reservation_id'] == reservation_id]
            return hits[0] if hits else None

    def snapshot(self):
        with self._locked():
            rows = self._rows()
            return self.path.read_bytes(), state(rows, self.policy_sha256)

    def reserve(self, episode_id, reservation, bindings, pricing_admission, attempt_id=None):
        """Atomic: slot directory, slot and money together, or nothing. `attempt_id` is the caller's transaction identity,
        chosen before any effect, so an uncertain return can be resolved with find_open()."""
        require(isinstance(episode_id, str) and episode_id != '', 'campaign_missing_episode_identity')
        attempt_id = attempt_id or uuid.uuid4().hex
        with self._locked():
            rows = self._rows(); s = state(rows, self.policy_sha256)
            require(s['open_reservations'] == [], 'campaign_reservation_open')
            require(s['transmissions_consumed'] < s['maximum_transmissions'], 'campaign_transmissions_exhausted')
            require(s['presend_attempts_used'] < s['maximum_presend_attempts'], 'campaign_presend_attempts_exhausted')
            require(s['committed_micro_usd']+reservation['reserved_micro_usd'] <= s['maximum_micro_usd'], 'campaign_money_exhausted')
            reservation_id = uuid.uuid4().hex
            slot = self.slot(reservation_id); slot.mkdir(parents=True, exist_ok=False); fsync_directory(self.slots)
            row = self._append(rows, {'kind': 'reservation', 'reservation_id': reservation_id, 'attempt_id': attempt_id, 'episode_id': episode_id,
                                      'policy_sha256': self.policy_sha256, **bindings, 'reserved_micro_usd': reservation['reserved_micro_usd'],
                                      'reservation': reservation, 'pricing_admission': pricing_admission,
                                      'reserved_at_unix': int(time.time())})
            return row, self.path.read_bytes()

    def reconcile(self, permit, process_record, http_record, evidence, launched=True):
        """The authoritative slot decides. Release needs established termination, or proof that no sender was ever launched;
        everything else stays consumed. The slot is closed by its marker *before* the row is appended, so no sender can act
        between the two; a marker without a row is completed on the next call."""
        with self._locked():
            rows = self._rows(); s = state(rows, self.policy_sha256)
            require(permit['reservation_id'] in s['open_reservations'], 'campaign_reservation_not_open')
            slot = self.slot(permit['reservation_id'])
            base = {'reservation_id': permit['reservation_id'], 'episode_id': permit['episode_id'], 'evidence': evidence,
                    'launched': bool(launched), 'termination_established': termination_established(process_record),
                    'reconciled_at_unix': int(time.time())}
            existing = [m for m in ('release.json', 'unknown.json') if (slot/m).exists()]
            valid, torn = [], []
            for m in existing:  # a marker is a receipt only if it parses and binds; torn bytes are not the declared receipt
                try:
                    value = json.loads((slot/m).read_bytes())
                    bound = (isinstance(value, dict) and value.get('kind') == m[:-5] and value.get('reservation_id') == permit['reservation_id']
                             and isinstance(value.get('reconciled_at_unix'), int))
                except (ValueError, OSError): bound = False
                (valid if bound else torn).append(m)
            try: grant = read_grant(slot, permit)
            except Failure as unreadable:
                grant, base = None, {**base, 'grant_state': unreadable.code}
            if grant is not None:
                outcome = (http_record or {}).get('send_outcome')
                row = {**base, 'kind': 'send_grant', 'grant': grant, 'send_outcome': outcome if outcome in ('returned', 'unknown') else 'unknown'}
                marker = None
            elif valid:
                # A prior reconciliation closed the slot but its row never committed: complete it with the validated marker's kind.
                # A torn marker left beside it by an earlier interrupted repair stays associated with the row.
                kind = valid[0][:-5]
                row = {**base, 'kind': kind, 'reason': 'completed_from_marker', 'recovered': True}; marker = valid[0]
                if torn: row['torn_marker'] = torn[0]
            elif torn:
                # The slot is closed by bytes that are not a receipt: consumed, with a valid unknown marker written beside them.
                require('unknown.json' not in torn, 'campaign_marker_torn_unrecoverable')
                row = {**base, 'kind': 'unknown', 'reason': 'torn_marker', 'torn_marker': torn[0], 'recovered': True}; marker = 'unknown.json'
                existing = []
            elif 'grant_state' in base:
                row = {**base, 'kind': 'unknown', 'reason': 'grant file present but unreadable or unbound'}; marker = 'unknown.json'
            elif not launched and process_record is None and http_record is None:
                row = {**base, 'kind': 'release', 'reason': 'pre_launch_failure', 'failure_category': None,
                       'transport_record_present': False}; marker = 'release.json'
            elif base['termination_established'] and (http_record is None or (http_record.get('body_sends_started') == 0
                                                                              and http_record.get('header_sends_started') == 0)):
                row = {**base, 'kind': 'release', 'reason': 'pre_send_failure_with_established_termination',
                       'failure_category': None if http_record is None else http_record.get('failure_category'),
                       'transport_record_present': http_record is not None}; marker = 'release.json'
            else:
                row = {**base, 'kind': 'unknown',
                       'reason': 'no grant, but termination is not established or the counters contradict the missing grant'}; marker = 'unknown.json'
            if marker is not None and not existing:
                write_exclusive(slot/marker, canonical({'kind': row['kind'], 'reservation_id': permit['reservation_id'],
                                                        'reconciled_at_unix': base['reconciled_at_unix']})+b'\n')
                # write_exclusive raises after a partial write: the torn marker stays, the row is not appended, and the next
                # call takes the torn-marker branch above.
            row['marker_sha256'] = sha((slot/(marker or GRANT_FILE)).read_bytes())
            row = self._append(rows, row)
            return row, self.path.read_bytes()
