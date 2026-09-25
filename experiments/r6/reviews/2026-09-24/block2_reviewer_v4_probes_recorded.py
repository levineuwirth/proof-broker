#!/usr/bin/env python3
"""The block 2 runner revision 4 review's reproducer (`block2_runner_v4_review_probes.py`, retained unchanged), run against the current runner
with its assertion that each probe *continues* replaced by recording the observed decision. The reproducer is copied to a temporary sibling
(it locates the runner and controls relative to itself) and removed afterwards; it writes --output itself."""
import argparse, subprocess, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(); parser.add_argument('--output', type=Path, required=True); args = parser.parse_args()
if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
src = (HERE/'block2_runner_v4_review_probes.py').read_text()
old = "  assert results[name][mode]['observed']=='continued',(name,mode,results[name][mode])"
assert src.count(old) == 1; src = src.replace(old, "  pass")
copy = HERE/'_block2_reviewer_v4_probes_recording.py'; copy.write_text(src)
try: sys.exit(subprocess.run([sys.executable, str(copy), '--output', str(args.output)], stdout=subprocess.DEVNULL).returncode)
finally: copy.unlink()
