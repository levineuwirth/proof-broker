#!/usr/bin/env python3
"""R6-015 step 2: control 8 exercised on synthetic proofs, before the lock (`experiments/r6/R6-015-PROPOSAL.md`, revision 5).

    synthetic_audit.py --output RECORD.json

Builds the bridge revision `BRIDGE_REV` from git (never the working tree) with R6's pinned Lean 4.32.0, builds
`R6015AuditSynthetic.lean` against it, exports each `local`/`whole` pair with R6's pinned exporter, and runs the audit
program of `qualification-audit-v1` on each export in `--synthetic` mode. The exporter and the program are used as that
lock records them: their digests are checked against it, and nothing about that lock changes.

Control 8's predicate, as revision 5 freezes it, with binding replaced by `--synthetic` mode's `not_applicable_synthetic`
(there is no retained residual for a synthetic proof): the program exits 0 and its report has no `refused` field;
`local.locatable` and `whole.locatable` are `true`; `local.hypotheses` and `whole.hypotheses` are present and empty. An error,
a refusal or a missing field fails. Expected: every `c*` pair (the constrained route) passes; every `p*` pair (the pinned
fold, contrast) fails.

Offline: no provider, credential, episode or spending, and no retained R6 certificate.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
REPO = R6.parents[1]
BRIDGE_REV = '476fab317e6633511b2a73b36313457d762e3a9c'
BUILD = R6/'.cache/r6-015-synthetic-audit'
TOOLCHAIN = Path.home()/'build/elan/toolchains/leanprover--lean4---v4.32.0'
AUDIT_TOOLCHAIN = Path.home()/'build/elan/toolchains/leanprover--lean4---v4.32.2'
EXPORTER = R6/'.cache/exporter/.lake/build/bin/lean4export'
TOOL = R6/'.cache/qualification-audit/.lake/build/bin/r6-qualification-audit'
AUDIT_LOCK = R6/'policies/qualification-audit-v1.sha256.json'
GLUE = REPO/'lean-bridge/.lake/build/lib/libpbglue.so'
FFI = REPO/'_build/default/sdk/ffi/proof_broker_ffi.so'
MODULES = ('IR', 'Trace', 'Bridge', 'TermMode', 'Alethe', 'Tactic')
PAIRS = {'c1': True, 'c2': True, 'c3': True, 'c4': True, 'c5': True, 'c6': True, 'c7': True, 'p1': False, 'p2': False}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(cmd, **kw):
    return subprocess.run(cmd, check=True, **kw)


def predicate(r):
    """Control 8, frozen (revision 5), in `--synthetic` mode. Returns the unmet conditions."""
    a = r.get('audit')
    if r.get('exit') != 0: return [f"exit {r.get('exit')}"]
    if 'refused' in r or not isinstance(a, dict): return ['refused or no report']
    unmet = []
    if a.get('binding') != 'not_applicable_synthetic': unmet.append(f"binding {a.get('binding')!r}")
    for t in ('local', 'whole'):
        s = a.get(t)
        if not isinstance(s, dict): unmet.append(f'{t} missing'); continue
        if s.get('locatable') is not True: unmet.append(f'{t} not locatable')
        if not isinstance(s.get('hypotheses'), list): unmet.append(f'{t}.hypotheses missing')
        elif s['hypotheses']: unmet.append(f"{t} refers to {[h.get('name') for h in s['hypotheses']]}")
    return unmet


def build():
    lock = json.loads(AUDIT_LOCK.read_text())
    if sha(TOOL) != lock['tool_sha256'] or sha(EXPORTER) != lock['exporter_sha256']:
        raise SystemExit('the audit program or the exporter differs from qualification-audit-v1')
    if BUILD.exists(): shutil.rmtree(BUILD)
    (BUILD/'ProofBroker').mkdir(parents=True)
    for m in MODULES:
        (BUILD/f'ProofBroker/{m}.lean').write_bytes(
            subprocess.check_output(['git', '-C', str(REPO), 'show', f'{BRIDGE_REV}:lean-bridge/ProofBroker/{m}.lean']))
    (BUILD/'ProofBroker.lean').write_bytes(
        subprocess.check_output(['git', '-C', str(REPO), 'show', f'{BRIDGE_REV}:lean-bridge/ProofBroker.lean']))
    shutil.copyfile(HERE/'R6015AuditSynthetic.lean', BUILD/'R6015AuditSynthetic.lean')
    (BUILD/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
    (BUILD/'lakefile.lean').write_text(
        'import Lake\nopen Lake DSL\npackage «r6-015-synthetic-audit»\n'
        'lean_lib ProofBroker where\n  precompileModules := true\n'
        'lean_lib R6015AuditSynthetic where\n  precompileModules := false\n'
        f'  moreLeanArgs := #["--load-dynlib={GLUE}", "--load-dynlib={FFI}"]\n')
    run([str(TOOLCHAIN/'bin/lake'), 'build', 'R6015AuditSynthetic'], cwd=BUILD, stdout=subprocess.DEVNULL)
    env = {'LEAN_PATH': str(BUILD/'.lake/build/lib/lean'), 'PATH': '/usr/bin:/bin', 'LEAN_SYSROOT': str(TOOLCHAIN)}
    for p in PAIRS:
        with open(BUILD/f'{p}.ndjson', 'wb') as out:
            run([str(EXPORTER), 'R6015AuditSynthetic', '--', f'R6015Audit.{p}_local', f'R6015Audit.{p}_whole'],
                cwd=BUILD, stdout=out, env=env)


def audit_one(export, local, whole):
    with tempfile.TemporaryDirectory(prefix='r6-015-synthetic-') as tmp:
        report = Path(tmp)/'report.json'
        proc = subprocess.run([str(TOOL), '--synthetic', str(export), local, whole, '-', str(report)], capture_output=True,
                              text=True, env={'PATH': '/usr/bin:/bin', 'LEAN_SYSROOT': str(AUDIT_TOOLCHAIN)})
        r = json.loads(report.read_text()) if report.exists() else {'error': (proc.stdout + proc.stderr)[-2000:]}
        r['exit'] = proc.returncode
        return r


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--output', required=True)
    out = Path(p.parse_args().output)
    if out.exists(): raise SystemExit(f'refusing to overwrite {out}')
    build()
    results, failures = {}, {}
    for pair, constrained in PAIRS.items():
        r = audit_one(BUILD/f'{pair}.ndjson', f'R6015Audit.{pair}_local', f'R6015Audit.{pair}_whole')
        unmet = predicate(r)
        failures[pair] = unmet if constrained else ([] if unmet else ['passed control 8, expected to fail'])
        results[pair] = {'route': 'constrained' if constrained else 'pinned (contrast)', 'control_8_unmet': unmet, 'report': r}
        print(pair, 'as expected' if not failures[pair] else failures[pair], flush=True)
    passed = not any(failures.values())
    out.write_text(json.dumps({
        'passed': passed, 'failures': failures, 'results': results, 'bridge_rev': BRIDGE_REV,
        'tool_sha256': sha(TOOL), 'exporter_sha256': sha(EXPORTER), 'audit_lock_sha256': sha(AUDIT_LOCK),
        'sources_sha256': {str(f.relative_to(REPO)): sha(f) for f in (HERE/'R6015AuditSynthetic.lean', Path(__file__).resolve())},
        'scope': 'synthetic proofs only; no retained R6 certificate replayed; pre-lock'}, indent=1) + '\n')
    print(json.dumps({'passed': passed}))
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(main())
