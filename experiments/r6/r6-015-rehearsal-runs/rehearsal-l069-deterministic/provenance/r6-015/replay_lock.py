"""R6-015 admission and lock (harness revision 2).

Every episode passes `admit` before anything else runs or is written:
- a **planned** episode must be exactly its entry in the locked plan, and the R6-015 lock must verify;
- a **pinned** episode must be exactly one of `REHEARSALS`, the two pre-lock rehearsals the review of harness revision 1 approved
  as a limited exception (bridge `476fab31`, the option unset, injection disabled). They test the harness and are excluded from
  R6-015's results.

Nothing else is admitted.

The lock binds the complete source closure these paths use:
- every Python module the episode, campaign and supervisor processes import from `experiments/r6`, computed by importing them
  (`python_closure`), so a module added to the closure changes the record;
- the non-Python inputs (`DATA`): the capture helper, the event and site schemas, the checker and assembler sources, the vendor
  lock, and R6's harness locks, the census lock among them;
- the binaries: the compiler, the exporter, the kernel checker, the glue library and the audit program;
- the bridge revision and the instrumented `Tactic.lean`;
- the plan, and every planned episode's source seal and consumed artifact.
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

LOCK = R6/'policies/r6-015-replay-v1.sha256.json'
AUDIT_TOOL = R6/'.cache/qualification-audit/.lake/build/bin/r6-qualification-audit'
AUDIT_TOOLCHAIN = Path.home()/'build/elan/toolchains/leanprover--lean4---v4.32.2'
AUDIT_LOCK = R6/'policies/qualification-audit-v1.sha256.json'
EXPORTER = R6/'.cache/exporter/.lake/build/bin/lean4export'
GLUE = R6.parents[1]/'lean-bridge/.lake/build/lib/libpbglue.so'
ENTRY_MODULES = ('replay_lock', 'replay_bridge', 'replay_episode', 'replay_campaign', 'site_supervise', 'supervise')
DATA = ('capture/CaptureSite.lean', 'schema/event.schema.json', 'schema/task-site.schema.json', 'validate/verify_certificate.ml',
        'validate/proposal_driver.ml', 'validate/Replay.lean', 'vendor/sources.lock.json', 'policies/census-harness-v1.sha256.json',
        'policies/site-harness-v4.sha256.json', 'policies/fixture-harness-v1.sha256.json', 'policies/qualification-audit-v1.sha256.json')
SPEC_FIELDS = {'id', 'site', 'source', 'coefficients', 'inject_unverified', 'route'}
REHEARSALS = {
    'rehearsal-l069-learned-draw1': {'id': 'rehearsal-l069-learned-draw1', 'site': 'bracket-l069',
        'source': {'arm': 'learned', 'run': 'cohort-live-v9/l069-draw1'},
        'coefficients': None, 'inject_unverified': False, 'route': 'pinned'},
    'rehearsal-l069-deterministic': {'id': 'rehearsal-l069-deterministic', 'site': 'bracket-l069',
        'source': {'arm': 'deterministic', 'run': 'census-runs/deterministic-v1/site_cvc4_term_mode_v1/bracket-l069'},
        'coefficients': None, 'inject_unverified': False, 'route': 'pinned'},
}


class Refused(Exception):
    """An episode outside the locked plan and the approved rehearsals."""


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
            'r6_exporter': exporter}


def consumed(spec):
    run = R6/spec['source']['run']
    name = 'evidence.json' if spec['source']['arm'] == 'learned' else 'events.ndjson'
    return {'seal_sha256': r6.sha(run/'seal.json'), 'artifact': name, 'artifact_sha256': r6.sha(run/name)}


def lock_record(plan_path):
    import replay_bridge
    plan = r6.read_json(plan_path)
    audit = r6.read_json(AUDIT_LOCK)
    tools = binaries()
    if r6.sha(AUDIT_TOOL) != audit['tool_sha256'] or r6.sha(EXPORTER) != audit['exporter_sha256'] or tools['r6_exporter'] != EXPORTER:
        raise ValueError('the audit program or the exporter differs from qualification-audit-v1')
    sources, patch = replay_bridge.source_record()
    if set(plan) != {'schema_version', 'episodes'} or plan['schema_version'] != 'r6-015-plan-1': raise ValueError('plan fields')
    for spec in plan['episodes']: check_spec(spec)
    ids = [s['id'] for s in plan['episodes']]
    if len(set(ids)) != len(ids) or set(ids) & set(REHEARSALS): raise ValueError('episode ids are not unique')
    if any(s['route'] != 'constrained' for s in plan['episodes']): raise ValueError('the plan runs the constrained route only')
    return {'schema_version': 'r6-015-replay-lock-2',
            'python_sha256': {str(p.relative_to(R6)): r6.sha(p) for p in python_closure()},
            'data_sha256': {p: r6.sha(R6/p) for p in DATA},
            'binaries_sha256': {k: r6.sha(v) for k, v in tools.items()},
            'bridge_rev': replay_bridge.BRIDGE_REV,
            'instrumented_tactic_sha256': sources['lean-bridge/ProofBroker/Tactic.lean']['instrumented_sha256'],
            'instrumentation_patch_sha256': r6.hashlib.sha256(patch.encode()).hexdigest(),
            'plan': str(Path(plan_path).resolve().relative_to(R6)), 'plan_sha256': r6.sha(plan_path),
            'consumed': {s['id']: consumed(s) for s in plan['episodes']}}


def verify_lock():
    import census
    import site_task
    if not LOCK.exists(): raise Refused('the R6-015 lock does not exist; nothing is replayed before the lock')
    frozen = r6.read_json(LOCK)
    site_task.verify_lock(); census.verify_lock()
    if lock_record(R6/frozen['plan']) != frozen: raise Refused('the R6-015 lock does not verify')
    return frozen


def planned(frozen):
    return {s['id']: s for s in r6.read_json(R6/frozen['plan'])['episodes']}


def admit(spec):
    """'planned' or 'rehearsal', or `Refused`. Runs before anything else in an episode."""
    check_spec(spec)
    if spec['route'] == 'pinned':
        if REHEARSALS.get(spec['id']) != spec: raise Refused('a pinned episode must be one of the approved rehearsals, exactly')
        return 'rehearsal'
    if planned(verify_lock()).get(spec['id']) != spec: raise Refused('the episode is not its entry in the locked plan')
    return 'planned'


def write_lock(plan_path):
    if LOCK.exists(): raise Refused('the R6-015 lock already exists')
    LOCK.write_text(json.dumps(lock_record(plan_path), indent=1) + '\n')
    return r6.sha(LOCK)
