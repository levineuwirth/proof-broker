#!/usr/bin/env python3
"""R6-016's bounded diagnosis of l070 draw 5 (`R6-016-PROPOSAL.md`, revision 2, section 4).

    diagnose_l070.py build                    build the diagnosis program (Lean 4.32.2)
    diagnose_l070.py run --output RECORD      under the R6-016 lock, after the replay: R6's retained l070 draw 5 export
    diagnose_l070.py rehearse --output RECORD pre-lock: synthetic exports only, each with a frozen expectation

**The program** (`diagnosis/Diagnose.lean`) imports `AuditCore`: `qualification-audit-v2`'s `Audit.lean`, byte for byte, cut
before its `main`. The build checks the file against `qualification-audit-v2`'s lock, and that the cut text is a prefix of it. So
the export is parsed, compared with `Init`, replayed and searched exactly as the locked audit does, and its atoms are the
audit's (`atomsOf`).

**The input** is one export: `cohort-live-v9/l070-draw5/solution.ndjson.gz`, checked against its run's seal and against
`qualification-audit-v2`'s locked selection, with `live-evaluation-v3` verified before and after. It runs under the R6-016 lock,
verified before and after, so that it cannot inform the atom rules.

**The classification** of each pair, from established evidence only (`classify`), in the proposal's order:
- `identical`: equal after instantiating metavariables, or equal up to metadata;
- `printed_only`: otherwise, definitionally equal: the first established meta-level attempt (each confirmed by the kernel), or the
  kernel's `rfl`;
- `arithmetically_equal`: otherwise, an established proof of `a = b` (`omega` or `grobner`);
- `distinct`: otherwise, an established, kernel-checked counterexample;
- `equality_not_established`: none of these. Unresolved, and not a claim that the terms differ.

Evidence of both equality and a counterexample would contradict the kernel; it is reported as `contradictory_evidence`, for
diagnosis. The analysis recomputes every classification from the record's attempts.

Offline: no provider, credential or spending.
"""
import argparse
import gzip
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
if str(R6) not in sys.path: sys.path.insert(0, str(R6))
if str(HERE) not in sys.path: sys.path.insert(0, str(HERE))

import run as r6  # noqa: E402
import replay_lock  # noqa: E402
sys.path.insert(0, str(R6/'qualification-audit-v2'))
import qualification_audit_v2 as audit_v2  # noqa: E402

SCHEMA = 'r6-016-diagnosis-1'
BUILD = replay_lock.DIAGNOSIS_TOOL.parents[3]
TOOL = replay_lock.DIAGNOSIS_TOOL
TOOLCHAIN = replay_lock.AUDIT_TOOLCHAIN
SOURCE = HERE/'diagnosis/Diagnose.lean'
AUDIT_SOURCE = R6/'qualification-audit-v2/Audit.lean'
CUT = '\ndef main (args : List String)'
SLOT = 'bracket-l070/5'
RUN = 'cohort-live-v9/l070-draw5'
SOURCES = (Path(__file__).resolve(), SOURCE)
ENV = {'PATH': '/usr/bin:/bin', 'LEAN_SYSROOT': str(TOOLCHAIN)}
CLASSES = ('identical', 'printed_only', 'arithmetically_equal', 'distinct', 'equality_not_established', 'contradictory_evidence')


def audit_core():
    """`Audit.lean` as locked by `qualification-audit-v2`, cut before its `main`."""
    frozen = r6.read_json(replay_lock.AUDIT_LOCK)['sources_sha256']
    if frozen.get(str(AUDIT_SOURCE.relative_to(R6.parents[1]))) != r6.sha(AUDIT_SOURCE):
        raise ValueError("Audit.lean differs from qualification-audit-v2's lock")
    text = AUDIT_SOURCE.read_text()
    if text.count(CUT) != 1: raise ValueError('Audit.lean has no single main to cut')
    core = text[:text.index(CUT)] + '\n'
    if not text.startswith(core.rstrip('\n')) or 'def main' in core: raise ValueError('the cut is not a prefix without main')
    return core


def build(_=None):
    if BUILD.exists(): shutil.rmtree(BUILD)
    BUILD.mkdir(parents=True)
    shutil.copytree(R6/'vendor/lean4export/Export', BUILD/'Export')
    shutil.copyfile(R6/'vendor/lean4export/Export.lean', BUILD/'Export.lean')
    (BUILD/'AuditCore.lean').write_text(audit_core())
    shutil.copyfile(SOURCE, BUILD/'Diagnose.lean')
    (BUILD/'lakefile.toml').write_text('name = "r6016diagnosis"\n[[lean_lib]]\nname = "Export"\n[[lean_lib]]\nname = "AuditCore"\n'
                                       '[[lean_exe]]\nname = "r6-016-diagnose"\nroot = "Diagnose"\nsupportInterpreter = true\n')
    (BUILD/'lean-toolchain').write_text(f'{audit_v2.TOOL_TOOLCHAIN}\n')
    subprocess.run([str(TOOLCHAIN/'bin/lake'), 'build', 'r6-016-diagnose'], cwd=BUILD, check=True)
    print(json.dumps({'tool': r6.sha(TOOL), 'audit_core_sha256': r6.sha(BUILD/'AuditCore.lean')}))


def run_tool(export, local):
    with tempfile.TemporaryDirectory(prefix='r6-016-diagnosis-') as tmp:
        report = Path(tmp)/'report.json'
        proc = subprocess.run([str(TOOL), str(export), local, str(report)], capture_output=True, text=True, env=ENV)
        r = r6.read_json(report) if report.exists() else {'error': (proc.stdout + proc.stderr)[-2000:]}
    command = {'argv': [str(TOOL.relative_to(R6)), '<tmp>/export.ndjson', local, '<tmp>/report.json'], 'env': ENV,
               'exit_code': proc.returncode, 'tool_sha256': r6.sha(TOOL), 'stderr': proc.stderr[-2000:]}
    return r, command


def established(a): return isinstance(a, dict) and a.get('outcome') == 'established'


def classify(pair):
    """(classification, basis) from the pair's recorded attempts; established evidence only."""
    s, d, ar, cx = (pair.get(k) or {} for k in ('syntactic', 'definitional', 'arithmetic', 'counterexample'))
    if s.get('equal_after_instantiation') is True or s.get('equal_up_to_metadata') is True:
        return 'identical', 'equal after instantiation' if s.get('equal_after_instantiation') is True else 'equal up to metadata'
    meta = [m for m in d.get('meta') or [] if established(m)]
    equal = (f"definitionally equal: {meta[0]['transparency']}, zeta_delta {meta[0]['zeta_delta']}" if meta
             else 'definitionally equal: the kernel' if established(d.get('kernel')) else None)
    proved = [k for k in ('omega', 'grobner') if established(ar.get(k))]
    if established(cx) and (equal or proved): return 'contradictory_evidence', 'equality and a counterexample both established'
    if equal: return 'printed_only', equal
    if proved: return 'arithmetically_equal', f'proved by {proved[0]}'
    if established(cx): return 'distinct', f"counterexample at {cx.get('instance')}"
    return 'equality_not_established', 'no attempt established equality or a counterexample'


def classified(report):
    pairs = ((report.get('diagnosis') or {}).get('pairs')) or []
    return [{'atoms': p.get('atoms'), 'classification': c, 'basis': b} for p in pairs for c, b in [classify(p)]]


def run(args):
    out = Path(args.output)
    if out.exists(): raise SystemExit(f'refusing to overwrite {out}')
    try:
        frozen = replay_lock.verify_lock()
    except replay_lock.Refused as refused:
        raise SystemExit(str(refused))
    audit_v2.v1.verify_live_evaluation()
    selected = r6.read_json(replay_lock.AUDIT_LOCK)['selection']['regression'][SLOT]
    source = R6.parents[1]/selected['run']
    if selected['run'] != f'experiments/r6/{RUN}': raise SystemExit('the locked selection names another run for l070 draw 5')
    seal = r6.read_json(source/'seal.json')['retained_sha256']
    packed = r6.sha(source/'solution.ndjson.gz')
    if seal.get('solution.ndjson.gz') != packed or packed != selected['solution.ndjson.gz_sha256']:
        raise SystemExit('the l070 draw 5 export differs from its seal or the locked selection')
    with tempfile.TemporaryDirectory(prefix='r6-016-diagnosis-export-') as tmp:
        export = Path(tmp)/'export.ndjson'; export.write_bytes(gzip.decompress((source/'solution.ndjson.gz').read_bytes()))
        unpacked = r6.sha(export)
        report, command = run_tool(export, selected['local'])
    if r6.sha(source/'solution.ndjson.gz') != packed: raise SystemExit('the export changed during the diagnosis')
    audit_v2.v1.verify_live_evaluation(); replay_lock.verify_lock()
    command['inputs'] = {'<tmp>/export.ndjson': {'unpacked_from': f'{RUN}/solution.ndjson.gz', 'sha256': unpacked, 'packed_sha256': packed}}
    record = {'schema_version': SCHEMA, 'slot': SLOT, 'run': RUN, 'local': selected['local'], 'lock_sha256': r6.sha(replay_lock.LOCK),
              'tool_sha256': r6.sha(TOOL), 'sources_sha256': {str(f.relative_to(R6)): r6.sha(f) for f in SOURCES},
              'audit_source_sha256': r6.sha(AUDIT_SOURCE), 'command': command, 'report': report, 'pairs': classified(report),
              'scope': 'R6-016 section 4: diagnosis, after the replay; it changes no route and counts nothing'}
    out.write_text(json.dumps(record, indent=1) + '\n')
    print(json.dumps({'pairs': record['pairs']}))


# The rehearsal: synthetic exports, each a local theorem folding `a - b + 1` for one pair of atoms `a`, `b` that print identically.
# Two limits of an export, both stated in the harness record:
# - R6's pinned exporter erases metadata (`exportMData` is off), so no export carries any, and `identical` cannot arise from a
#   pair;
# - an export carries declarations, not attributes. Outside `Init`, a `@[reducible]` or `@[instance]` definition is a plain
#   definition in the replayed environment, so the meta-level attempts below default transparency, and the tactics, do not
#   unfold it. The kernel, and default transparency, are unaffected.
# No pair here is `arithmetically_equal` (`d_cast` is, through a `@[reducible]` cast the export does not mark); `test_harness.py`
# covers that branch of `classify`, and `identical`'s.
SYNTHETIC = '''import ProofBroker.TermMode

namespace R6016DiagnosisSynthetic

@[reducible] def mulVia : Mul Int := ⟨Int.mul⟩
def mulSwapped : Mul Int := ⟨fun a b => b * a⟩
def mulAdding : Mul Int := ⟨fun a b => a + b⟩
opaque g {α : Type} : α → Int
@[reducible] def castZero : NatCast Int := ⟨fun n => Int.ofNat (0 + n)⟩

{cases}
end R6016DiagnosisSynthetic
'''
FOLD = ('theorem {name}_local {binders} (h0 : {a} - {b} + 1 ≤ 0) (hp : 0 < {a} - {b} + 1) : False :=\n'
        '  ProofBroker.TermMode.farkasContradictN ({a} - {b} + 1) h0 hp\n')
# name -> (binders, a, b, the frozen expectation), frozen after the rehearsals. `d_swapped` and `d_cast` are arithmetically equal,
# through definitions no attempt sees through in the export's environment: unresolved.
REHEARSAL = {
    'd_instance': ('(x y : Int)', 'x * y', '(@HMul.hMul Int Int Int (@instHMul Int mulVia) x y)', 'printed_only'),
    'd_cast': ('(x : Nat) (y : Int)', '(@Nat.cast Int castZero x * y)', '((x : Int) * y)', 'equality_not_established'),
    'd_adding': ('(x y : Int)', 'x * y', '(@HMul.hMul Int Int Int (@instHMul Int mulAdding) x y)', 'distinct'),
    'd_swapped': ('(x y : Int)', 'x * y', '(@HMul.hMul Int Int Int (@instHMul Int mulSwapped) x y)', 'equality_not_established'),
    'd_opaque': ('', '(@g Nat 0)', '(@g Int 0)', 'equality_not_established'),
}


def rehearse(args):
    out = Path(args.output)
    if out.exists(): raise SystemExit(f'refusing to overwrite {out}')
    work = R6/'.cache/r6-016-diagnosis-rehearsal'
    if work.exists(): shutil.rmtree(work)
    work.mkdir(parents=True)
    cases = ''.join(FOLD.format(name=n, binders=bs, a=a, b=b) + '\n' for n, (bs, a, b, _) in REHEARSAL.items())
    (work/'R6016DiagnosisSynthetic.lean').write_text(SYNTHETIC.replace('{cases}', cases))
    env = audit_v2.controls_env(); env['LEAN_PATH'] = f"{audit_v2.BRIDGE_ENVIRONMENT}:{work}"
    lean = audit_v2.CONTROLS_TOOLCHAIN/'bin/lean'
    subprocess.run([str(lean), 'R6016DiagnosisSynthetic.lean', '-o', 'R6016DiagnosisSynthetic.olean'], cwd=work, env=env, check=True)
    expected = {n: e for n, (_, _, _, e) in REHEARSAL.items()}
    results, unmet = {}, []
    for name, want in expected.items():
        export = work/f'{name}.ndjson'
        with open(export, 'wb') as f:
            subprocess.run([str(audit_v2.EXPORTER), 'R6016DiagnosisSynthetic', '--', f'R6016DiagnosisSynthetic.{name}_local'],
                           cwd=work, stdout=f, env=env, check=True)
        report, command = run_tool(export, f'R6016DiagnosisSynthetic.{name}_local')
        pairs = classified(report)
        results[name] = {'report': report, 'exit': command['exit_code'], 'pairs': pairs, 'expected': want}
        got = [p['classification'] for p in pairs]
        if command['exit_code'] != 0 or len(got) != 1 or (want is not None and got != [want]):
            unmet.append(f'{name}: {got} (exit {command["exit_code"]}), expected [{want}]')
        print(name, got, flush=True)
    out.write_text(json.dumps({'schema_version': SCHEMA + '-rehearsal', 'passed': not unmet, 'unmet': unmet, 'results': results,
                               'tool_sha256': r6.sha(TOOL), 'sources_sha256': {str(f.relative_to(R6)): r6.sha(f) for f in SOURCES},
                               'scope': 'pre-lock rehearsal: synthetic exports only; no retained export read'}, indent=1) + '\n')
    print(json.dumps({'passed': not unmet, 'unmet': unmet}))
    return 0 if not unmet else 1


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='cmd', required=True)
    sub.add_parser('build').set_defaults(f=build)
    for name, f in (('run', run), ('rehearse', rehearse)):
        c = sub.add_parser(name); c.add_argument('--output', required=True); c.set_defaults(f=f)
    args = p.parse_args()
    sys.exit(args.f(args) or 0)


if __name__ == '__main__':
    main()
