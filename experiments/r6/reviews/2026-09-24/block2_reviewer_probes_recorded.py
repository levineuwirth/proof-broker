#!/usr/bin/env python3
"""The block 2 runner revision 2 review's reproducer (`block2_runner_v2_review_probes.py`, retained unchanged), run against the current
runner with its assertions that each probe *continues* replaced by recording the observed decision, and a pause caught where the reproducer
expected none. The reproducer is copied to a temporary sibling (it locates the runner relative to itself) and removed afterwards."""
import argparse, subprocess, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(); parser.add_argument('--output', type=Path, required=True); args = parser.parse_args()
src = (HERE/'block2_runner_v2_review_probes.py').read_text()
for old, new in (("  assert out[name][mode]['observed']=='continued',(name,mode,out[name][mode])", "  pass"),
                 ("   except c.NextLaunch:result='continued'", "   except c.NextLaunch:result='continued'\n   except SystemExit as e:result='paused' if str(e).startswith('PAUSE') else str(e)[:40]"),
                 ("  assert result=='continued'", "  pass"),
                 ("'decision':json.loads(log.getvalue().splitlines()[0])}", "'decision':(log.getvalue().splitlines() or ['{}'])[0]}"),
                 ("print(json.dumps({'unexpected_continuations':14,", "print(json.dumps({'recorded':True,")):
    assert src.count(old) == 1, old; src = src.replace(old, new)
copy = HERE/'_block2_reviewer_probes_recording.py'; copy.write_text(src)
try: sys.exit(subprocess.run([sys.executable, str(copy), '--output', str(args.output)]).returncode)
finally: copy.unlink()
