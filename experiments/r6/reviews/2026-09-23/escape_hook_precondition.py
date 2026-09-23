#!/usr/bin/env python3
"""R6-014 revision 4 precondition for the scan-boundary controls: the sentinel-read hook the controls use (`reads_of_sentinel`) does detect
reads, shown by running the same escape mutations against the v9 auditor as committed at ac546085 (before the boundary repair), which
accepts each and reads the sentinel. Read-only; the committed auditor is extracted to a temporary sibling file and removed afterwards."""
import argparse, importlib.util, json, subprocess, sys, tempfile
from pathlib import Path
HERE = Path(__file__).resolve().parent; ROOT = HERE.parents[1]
parser = argparse.ArgumentParser(); parser.add_argument('--output', type=Path, required=True); args = parser.parse_args()
if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
old_path = HERE/'_escape_precondition_v9_ac546085.py'
old_path.write_bytes(subprocess.run(['git', '-C', str(ROOT), 'show', 'ac546085:experiments/r6/reviews/2026-09-23/cohort_v9_audit.py'], capture_output=True, check=True).stdout)
try:
    spec = importlib.util.spec_from_file_location('controls', HERE/'cohort_v9_audit_controls.py'); c = importlib.util.module_from_spec(spec); spec.loader.exec_module(c)
    spec = importlib.util.spec_from_file_location('previous', old_path); old = importlib.util.module_from_spec(spec); spec.loader.exec_module(old)
    c.audit = old; c.base.audit = old; result = {}
    for name in c.ESCAPES:
        with tempfile.TemporaryDirectory() as t:
            f = c.live_paths(Path(t)); assert c.run_live(f)['accepted']; c.mutate_live(name, f)
            observed, reads = c.reads_of_sentinel(lambda: c.run_live(f))
            result[name] = {'previous_auditor_accepted': observed['accepted'], 'sentinel_reads': len(reads)}
            assert observed['accepted'] is True and len(reads) >= 1, (name, observed, reads)
finally: old_path.unlink()
json.dump({'passed': True, 'previous_auditor': 'ac546085:reviews/2026-09-23/cohort_v9_audit.py', 'results': result}, args.output.open('x'), indent=1)
print(json.dumps(result, indent=1))
