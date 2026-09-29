"""Supervisor-owned, append-only receipt log. Hashes detect artifact changes;
they do not authenticate a hostile host or attest model computation.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import time

VERSION = "r6-event-1"
ZERO = "0" * 64
TERMINAL_EVENTS = {'episode_finished', 'episode_failed', 'tests_finished'}


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()


def digest(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def read(path):
    rows = []
    previous = ZERO
    for line in Path(path).read_bytes().splitlines():
        row = json.loads(line)
        recorded = row.pop("event_hash")
        if row["sequence"] != len(rows) or row["previous_hash"] != previous or digest(row) != recorded:
            raise ValueError("Event sequence or hash chain is invalid")
        if rows and (row['run_id'] != rows[0]['run_id'] or row['receipt_monotonic_ns'] < rows[-1]['receipt_monotonic_ns']):
            raise ValueError("Event run identity or receipt clock changed")
        row["event_hash"] = recorded
        rows.append(row)
        previous = recorded
    return rows


def append(run, stage, event, payload, source="supervisor"):
    run = Path(run)
    path = run / "events.ndjson"
    rows = read(path) if path.exists() else []
    if rows and rows[-1]['source'] == 'supervisor' and rows[-1]['event'] in TERMINAL_EVENTS:
        raise ValueError("Episode is already closed")
    if source == 'child_report' and event in TERMINAL_EVENTS:
        raise ValueError("A child observation cannot close the supervisor's log")
    row = {"schema_version": VERSION, "run_id": run.name, "task_id": "verinf-d1-70",
           "sequence": len(rows), "previous_hash": rows[-1]['event_hash'] if rows else ZERO,
           "receipt_monotonic_ns": time.monotonic_ns(),
           "receipt_utc": datetime.now(timezone.utc).isoformat(),
           "stage": stage, "event": event, "source": source, "payload": payload}
    row['event_hash'] = digest(row)
    fd = os.open(path, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    try:
        data = canonical(row) + b'\n'
        while data:
            data = data[os.write(fd, data):]
        os.fsync(fd)
    finally:
        os.close(fd)
    return row
