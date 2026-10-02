"""R6-016 admission and lock: R6-015's (`r6-015/replay_lock.py`, harness revision 3), with R6-016's lock, programs and data.

Every episode passes `admit` before anything else runs or is written: a **planned** episode must be exactly its entry in the
locked plan, and the R6-016 lock must verify. **Nothing else is admitted.** R6-016 has no pinned rehearsal (`REHEARSALS` is
empty): its harness is rehearsed on synthetic goals only.

The plan is R6-015's (`r6-015/plan.json`, 108 episodes), unchanged, with its step-3 record and `mutations.py`, which must name
it and each other. Control 5's labels are R6-016's own record (`labels.py`), computed by R6-015's frozen rule from the
classifications recorded at this lock: addendum 1 and addendum 2.

The lock binds the complete source closure these paths use:
- every Python module the episode, campaign, control-3, control-9, diagnosis, analysis and supervisor processes import from
  `experiments/r6`, computed by importing them (`python_closure`), so a module added to the closure changes the record;
- the non-Python inputs (`DATA`): the capture helper, the event and site schemas, the checker and assembler sources, the vendor
  lock, and R6's harness locks, the census lock among them; step 3's record (revision 2) and `mutations.py`; the control-5
  labels; both audit programs' locks, and the records the labels read; the analysis inputs; the diagnosis program's sources; and
  the tests;
- the binaries: the compiler, the exporter, the kernel checker, the glue library, both audit programs and the diagnosis program;
- the bridge revision and the instrumented `Tactic.lean`;
- the plan, and every planned episode's source seal and consumed artifact.

**The audit program is `qualification-audit-v2`** (`c42906ed…`), for the residual printed from each export and for control 8, as
R6-016's proposal (section 5) names it. `qualification-audit-v1`'s program and lock are bound too, by digest, as the proposal's
section 7 says; neither runs.
"""
import importlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
if str(R6) not in sys.path: sys.path.insert(0, str(R6))
if str(HERE) not in sys.path: sys.path.insert(0, str(HERE))

import run as r6  # noqa: E402

LOCK = R6/'policies/r6-016-replay-v1.sha256.json'
AUDIT_TOOL = R6/'.cache/qualification-audit-v2/.lake/build/bin/r6-qualification-audit'
AUDIT_TOOLCHAIN = Path.home()/'build/elan/toolchains/leanprover--lean4---v4.32.2'
AUDIT_LOCK = R6/'policies/qualification-audit-v2.sha256.json'
AUDIT_V1_TOOL = R6/'.cache/qualification-audit/.lake/build/bin/r6-qualification-audit'
AUDIT_V1_LOCK = R6/'policies/qualification-audit-v1.sha256.json'
DIAGNOSIS_TOOL = R6/'.cache/r6-016-diagnosis/.lake/build/bin/r6-016-diagnose'
EXPORTER = R6/'.cache/exporter/.lake/build/bin/lean4export'
GLUE = R6.parents[1]/'lean-bridge/.lake/build/lib/libpbglue.so'
ENTRY_MODULES = ('replay_lock', 'replay_bridge', 'replay_episode', 'replay_campaign', 'control3', 'control9', 'diagnose_l070', 'labels',
                 'analysis', 'site_supervise', 'supervise')
DATA = ('capture/CaptureSite.lean', 'schema/event.schema.json', 'schema/task-site.schema.json', 'validate/verify_certificate.ml',
        'validate/proposal_driver.ml', 'validate/Replay.lean', 'vendor/sources.lock.json', 'policies/census-harness-v1.sha256.json',
        'policies/site-harness-v4.sha256.json', 'policies/fixture-harness-v1.sha256.json', 'policies/qualification-audit-v1.sha256.json',
        'reviews/2026-10-01/R6-015-MUTATIONS-2.json', 'r6-015/mutations.py', 'reviews/2026-09-29/R6-014-BLOCK2-ANALYSIS.json',
        'reviews/2026-10-01/R6-QUALIFICATION-1-AUDIT.json', 'policies/qualification-audit-v2.sha256.json',
        'reviews/2026-10-02/R6-QUALIFICATION-1-AUDIT-V2-REGRESSION.json', 'reviews/2026-10-02/R6-QUALIFICATION-1-AUDIT-V2-ADDENDUM-2.json',
        'qualification-audit/qualification_audit.py',  # imported by qualification-audit-v2's driver from its path, outside sys.modules
        'r6-016/diagnosis/Diagnose.lean', 'r6-016/diagnosis/DiagnoseTest.lean', 'r6-016/test_binding.py', 'r6-016/test_analysis.py', 'r6-016/test_harness.py')
LABELS = 'reviews/2026-10-02/R6-016-CONTROL-5-LABELS.json'
MUTATIONS = 'reviews/2026-10-01/R6-015-MUTATIONS-2.json'
SPEC_FIELDS = {'id', 'site', 'source', 'coefficients', 'inject_unverified', 'route'}
REHEARSALS = {}   # R6-016 admits no pinned episode: its harness is rehearsed on synthetic goals only


class Refused(Exception):
    """An episode outside the locked plan."""


def check_spec(spec):
    if not isinstance(spec, dict) or set(spec) != SPEC_FIELDS: raise ValueError('spec fields')
    if spec['route'] not in ('constrained', 'pinned'): raise ValueError('route')
    if not isinstance(spec['source'], dict) or set(spec['source']) != {'arm', 'run'} or spec['source']['arm'] not in ('learned', 'deterministic'):
        raise ValueError('source')
    if spec['coefficients'] is not None and not (isinstance(spec['coefficients'], list)
                                                and all(isinstance(c, dict) and set(c) == {'hypothesis', 'coefficient'} for c in spec['coefficients'])):
        raise ValueError('coefficients')
    if not isinstance(spec['inject_unverified'], bool): raise ValueError('inject_unverified')


def python_closure():
    """Every module the episode, campaign and supervisor processes load from `experiments/r6`, by path."""
    for name in ENTRY_MODULES: importlib.import_module(name)
    files = set()
    for module in list(sys.modules.values()):
        path = getattr(module, '__file__', None)
        if path and Path(path).resolve().is_relative_to(R6) and Path(path).suffix == '.py': files.add(Path(path).resolve())
    return sorted(files)


def binaries():
    compiler, exporter, checker = r6.build_tools(task=r6.D1)
    return {'compiler': compiler/'bin/lean', 'exporter': EXPORTER, 'checker': checker, 'glue': GLUE, 'audit_tool': AUDIT_TOOL,
            'audit_tool_v1': AUDIT_V1_TOOL, 'diagnosis_tool': DIAGNOSIS_TOOL, 'r6_exporter': exporter}


def consumed(spec):
    run = R6/spec['source']['run']
    name = 'evidence.json' if spec['source']['arm'] == 'learned' else 'events.ndjson'
    return {'seal_sha256': r6.sha(run/'seal.json'), 'artifact': name, 'artifact_sha256': r6.sha(run/name)}


def lock_record(plan_path):
    import replay_bridge
    plan = r6.read_json(plan_path)
    audit, audit_v1 = r6.read_json(AUDIT_LOCK), r6.read_json(AUDIT_V1_LOCK)
    tools = binaries()
    if r6.sha(AUDIT_TOOL) != audit['tool_sha256'] or r6.sha(EXPORTER) != audit['exporter_sha256'] or tools['r6_exporter'] != EXPORTER:
        raise ValueError('the audit program or the exporter differs from qualification-audit-v2')
    if r6.sha(AUDIT_V1_TOOL) != audit_v1['tool_sha256'] or audit['qualification_audit_v1_lock_sha256'] != r6.sha(AUDIT_V1_LOCK):
        raise ValueError("qualification-audit-v1's program or lock differs from what qualification-audit-v2 binds")
    import labels
    labels.verify(plan_path)   # control 5's labels: R6-015's frozen rule, over the classifications recorded at this lock
    sources, patch = replay_bridge.source_record()
    if set(plan) != {'schema_version', 'episodes'} or plan['schema_version'] != 'r6-015-plan-1': raise ValueError('plan fields')
    for spec in plan['episodes']: check_spec(spec)
    ids = [s['id'] for s in plan['episodes']]
    if len(set(ids)) != len(ids) or set(ids) & set(REHEARSALS): raise ValueError('episode ids are not unique')
    if any(s['route'] != 'constrained' for s in plan['episodes']): raise ValueError('the plan runs the constrained route only')
    mutations = r6.read_json(R6/MUTATIONS)
    if mutations['plan_sha256'] != r6.sha(plan_path) or mutations['sources_sha256']['r6-015/mutations.py'] != r6.sha(R6/'r6-015/mutations.py'):
        raise ValueError('the step-3 record is not bound to this plan and this mutations.py')
    if set(mutations['episodes']) != set(ids): raise ValueError("the step-3 record's episodes differ from the plan")
    return {'schema_version': 'r6-016-replay-lock-1',
            'python_sha256': {str(p.relative_to(R6)): r6.sha(p) for p in python_closure()},
            'data_sha256': {p: r6.sha(R6/p) for p in DATA}, 'labels': LABELS, 'labels_sha256': r6.sha(R6/LABELS),
            'binaries_sha256': {k: r6.sha(v) for k, v in tools.items()},
            'bridge_rev': replay_bridge.BRIDGE_REV,
            'instrumented_tactic_sha256': sources['lean-bridge/ProofBroker/Tactic.lean']['instrumented_sha256'],
            'instrumentation_patch_sha256': r6.hashlib.sha256(patch.encode()).hexdigest(),
            'plan': str(Path(plan_path).resolve().relative_to(R6)), 'plan_sha256': r6.sha(plan_path),
            'consumed': {s['id']: consumed(s) for s in plan['episodes']}}


def verify_lock():
    import census
    import site_task
    if not LOCK.exists(): raise Refused('the R6-016 lock does not exist; nothing is replayed before the lock')
    frozen = r6.read_json(LOCK)
    site_task.verify_lock(); census.verify_lock()
    if lock_record(R6/frozen['plan']) != frozen: raise Refused('the R6-016 lock does not verify')
    return frozen


def planned(frozen):
    return {s['id']: s for s in r6.read_json(R6/frozen['plan'])['episodes']}


def admit(spec):
    """'planned', or `Refused`. Runs before anything else in an episode."""
    check_spec(spec)
    if spec['route'] == 'pinned': raise Refused('R6-016 admits no pinned episode')
    if planned(verify_lock()).get(spec['id']) != spec: raise Refused('the episode is not its entry in the locked plan')
    return 'planned'


def write_lock(plan_path):
    if LOCK.exists(): raise Refused('the R6-016 lock already exists')
    LOCK.write_text(json.dumps(lock_record(plan_path), indent=1) + '\n')
    return r6.sha(LOCK)
