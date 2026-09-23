#!/usr/bin/env python3
"""R6-013 reviewed library inventory for the v6 site stage commands. Non-locked; read-only over committed bytes.

For every non-sender stage, the (host, guest) library pairs of its command, read from the commit that recorded the v6 runs (`ANCHOR`), not
from the working tree. Every run's block for a stage must agree, and the head and tail around it must be the command `site_stage.stage`
builds (the auditor's own rebuild). As independent evidence, the dependency closure of the pinned binaries is recomputed on this host
exactly as `site_stage.stage` computes it (`episode.libraries`, compiler-owned libraries skipped, each mounted at its own path from its
resolved host path) and compared; a difference is recorded as an availability qualification, never folded into the inventory.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import episode
import run as r6
import site_task

spec = importlib.util.spec_from_file_location('r6_013_audit_for_inventory', ROOT/'reviews/2026-09-22/cohort_v6_audit.py')
audit = importlib.util.module_from_spec(spec); spec.loader.exec_module(audit)
ANCHOR = '7a82fed3'  # experiments: R6-013 ... cohort v5 and v6 with native runs
REPO = ROOT.parents[1]


def committed(path):
    return json.loads(subprocess.run(['git', '-C', str(REPO), 'show', f'{ANCHOR}:experiments/r6/{path}'], check=True, capture_output=True).stdout)


def closure(binary, extras, compiler):
    deps = set()
    for executable in [binary, *extras]: deps.update(episode.libraries(executable))
    return [(str(lib.resolve()), str(lib)) for lib in sorted(deps) if not (compiler and lib.is_relative_to(compiler))]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    tools = audit.stage_tools(); stages, sources = {}, {}
    names = subprocess.run(['git', '-C', str(REPO), 'ls-tree', '--name-only', f'{ANCHOR}:experiments/r6/{audit.RUNS}'], check=True, capture_output=True, text=True).stdout.split()
    for name in sorted(names):
        summary = committed(f'{audit.RUNS}/{name}/search-policy.json'); task = site_task.get(summary['task_id'])
        listing = subprocess.run(['git', '-C', str(REPO), 'ls-tree', '--name-only', f'{ANCHOR}:experiments/r6/{audit.RUNS}/{name}/stages'], check=True, capture_output=True, text=True).stdout.split()
        for stage in listing:
            if stage == 'proposal-1': continue
            cmd = committed(f'{audit.RUNS}/{name}/stages/{stage}/command.json'); recorded = Path(cmd['run'])
            specs = audit.stage_specs(recorded, task, tools); challenge = None
            if stage.startswith('validation-'):
                argv = cmd['argv']; challenge = Path(argv[argv.index('/challenge.ndjson')-1])
            head_ok, tail_ok, pairs = audit.split_command(cmd['argv'], stage, specs[stage], tools, recorded, challenge)
            assert head_ok and tail_ok and pairs is not None, (name, stage)
            assert stages.setdefault(stage, pairs) == pairs, (name, stage, 'differs across runs')
            sources.setdefault(stage, []).append(name)
    compiler = tools['compiler']; lean = compiler/'bin/lean'
    native = audit.consumption_overlay.DEST/'bridge/.lake/build/lib/lean'
    bridge = [audit.consumption_overlay.DEST/'sdk/_build/default/ffi/proof_broker_ffi.so', ROOT.parents[1]/'lean-bridge/.lake/build/lib/libpbglue.so',
              *[native/f'r6_x2dproposal_ProofBroker_{m}.so' for m in audit.BRIDGE_MODULES]]
    binaries = {'preparation-build': (lean, bridge, compiler), 'preparation': (lean, bridge, compiler), 'capture-build': (lean, bridge, compiler),
                'reconstruct': (lean, bridge, compiler), 'export': (tools['exporter'], bridge, compiler), 'pipeline-prepare': (tools['driver'], [], None),
                'assembly': (tools['driver'], [], None), 'certificate-check': (tools['verifier'], [], None),
                'validation-local': (tools['checker'], [], None), 'validation-whole': (tools['checker'], [], None)}
    current = {stage: [list(p) for p in closure(*binaries[stage])] for stage in stages}
    agreement = {stage: current[stage] == [list(p) for p in pairs] for stage, pairs in stages.items()}
    contained = {stage: all(audit.contained(h, g) for h, g in pairs) for stage, pairs in stages.items()}
    assert all(contained.values()), contained
    record = {'schema_version': 'r6-library-inventory-1', 'anchor_commit': subprocess.run(['git', '-C', str(REPO), 'rev-parse', ANCHOR], check=True, capture_output=True, text=True).stdout.strip(),
              'source': f'experiments/r6/{audit.RUNS}/*/stages/*/command.json at the anchor commit', 'stages': {s: [list(p) for p in v] for s, v in sorted(stages.items())},
              'runs_per_stage': {s: len(v) for s, v in sorted(sources.items())}, 'current_host_closure_equal': agreement, 'current_host_closure': current,
              'lexically_contained': contained, 'program_sha256': r6.sha(Path(__file__)),
              'scope': 'committed command bytes; the closure comparison is an availability check on this host, not a historical attestation'}
    args.output.write_text(json.dumps(record, indent=1)+'\n')
    print(json.dumps({'stages': {s: len(v) for s, v in stages.items()}, 'current_host_closure_equal': agreement}, indent=1))


if __name__ == '__main__':
    main()
