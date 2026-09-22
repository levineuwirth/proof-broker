"""R6-011 census site tasks: the frozen R6-000/R6-001 stages run on a census site without editing them.

The frozen stage machinery takes a registered `Task` and reaches a site's obligation through three task-specific pieces:
the anchor-line instrumentation (`run.instrument`), the manifest check (`run.frozen_task`) and the registry itself
(`task_spec.TASKS`, consulted by `events.append` and `episode.stage`). A census site differs in all three: it is instrumented
at a byte span with a parameterized capture, its manifest is a site manifest under `tasks/census-v1/`, and it is not one of the
two registered controls. This module supplies exactly those three pieces and nothing else:

- `SiteTask` carries the attributes the frozen stages read (id, path, local, whole, capture) for one site of the reviewed
  population, and is registered in the frozen registry *in process*, only after the site has been verified (`frozen_site`);
  the registry file is unchanged, and the two controls keep their entries.
- `frozen_site` is the site analogue of `run.frozen_task`: census lock, reviewed membership and exposure addendum, manifest
  schema and artifact digests, the decompressed challenge digest, the expected policy.
- `compile_input` is `proposal_episode.compile_input` with the census freeze's byte-span instrumentation in place of the
  anchor-line one; the helper text comes from the frozen `proposal_instrument.capture_source` applied to the site helper.
- `setup` runs the frozen `proposal_episode.setup` on the registered D1 control — setup is task-independent apart from the
  frozen expectation and the environment — after proving that the site's environment lock and compiled-environment inventory
  equal D1's, then substitutes the site's frozen expectation.
- `prepare` is `proposal_episode.prepare` up to the prepared problem, with the same stages, receipts and context check; the
  request is built by the contract that consumes it, not here.
"""
import difflib
import gzip
import hashlib
import json
from pathlib import Path
import shutil

import jsonschema

import census
import episode
import site_stage
import events
import payload
import proposal_episode as downstream
import proposal_instrument as overlay
import run as r6
import site_freeze
import task_spec

CENSUS_DIR = site_freeze.CENSUS_DIR
MEMBERSHIP_DECISION = r6.ROOT/'reviews/2026-09-22/R6-010-MEMBERSHIP-REVIEW.json'
MEMBERSHIP_DECISION_SHA256 = '107e59ef6dd255a6088aee91d9136b218748089849e7612ddd431fa4686a6bb6'  # the reviewed population decision, pinned
ADDENDUM = CENSUS_DIR/'exposure-addendum.json'


LOCK = r6.ROOT/'policies/site-harness-v1.sha256.json'
FILES = ('site_task.py', 'site_stage.py', 'site_supervise.py', 'site_representability.py', 'test_site.py')


def sha(data): return hashlib.sha256(data).hexdigest()


def lock():
    """The source lock of the site harness: written once; any later edit is a new revision."""
    if LOCK.exists(): raise ValueError('site lock already exists')
    LOCK.write_text(json.dumps({p: sha((r6.ROOT/p).read_bytes()) for p in FILES}, indent=2)+'\n')
    return LOCK


def verify_lock():
    values = json.loads(LOCK.read_bytes())
    if set(values) != set(FILES): raise ValueError('site source inventory changed')
    if any(sha((r6.ROOT/p).read_bytes()) != h for p, h in values.items()): raise ValueError('site harness requires its frozen source revision')
    census.verify_lock()
    return values


class SiteTask:
    """A reviewed census site, shaped like the frozen `Task` where the frozen stages read it."""
    def __init__(self, entry):
        self.entry = entry; self.id = entry['site_id']; self.path = CENSUS_DIR/self.id
        self.local = entry['saved_local_declaration']; self.whole = entry['declaration']; self.capture = site_freeze.CAPTURE
        self.source_hash = census.SOURCE_HASH; self.family = entry['declaration']; self.span = entry['byte_span']; self.line = entry['line']
        self.site = site_freeze.Site(entry)

    def __repr__(self): return f'SiteTask({self.id})'


def primary():
    """The reviewed primary population, in census order."""
    decision = json.loads(MEMBERSHIP_DECISION.read_bytes())
    return tuple(decision['primary'])


def frozen_site(task):
    """The site analogue of `run.frozen_task`: every relationship the frozen stages would otherwise take on trust."""
    census.verify_lock()
    decision_bytes = MEMBERSHIP_DECISION.read_bytes(); decision = json.loads(decision_bytes)
    if sha(decision_bytes) != MEMBERSHIP_DECISION_SHA256: raise ValueError('reviewed membership decision changed')
    frozen = json.loads((CENSUS_DIR/'census.json').read_bytes()); addendum = json.loads(ADDENDUM.read_bytes())
    if sha((CENSUS_DIR/'census.json').read_bytes()) != decision['census_sha256'] or sha((CENSUS_DIR/'membership.json').read_bytes()) != decision['membership_proposal_sha256']:
        raise ValueError('census or membership differs from the reviewed decision')
    if addendum['decision_sha256'] != sha(decision_bytes) or addendum['census_sha256'] != decision['census_sha256']:
        raise ValueError('exposure addendum is not bound to the reviewed decision')
    if task.id not in decision['primary']: raise ValueError(f'{task.id} is outside the reviewed primary population')
    manifest_bytes = (task.path/'manifest.json').read_bytes(); manifest = json.loads(manifest_bytes)
    if sha(manifest_bytes) != decision['manifests_sha256'][task.id]: raise ValueError(f'{task.id}: manifest differs from the reviewed one')
    jsonschema.validate(manifest, r6.read_json(site_freeze.SCHEMA))
    if (manifest['task_id'], manifest['saved_local_declaration'], manifest['original_declaration']) != (task.id, task.local, task.whole):
        raise ValueError('frozen site identity differs from the census entry')
    if sorted(manifest['artifacts_sha256']) != sorted(site_freeze.SITE_FILES): raise ValueError('site artifact population changed')
    for name, digest in manifest['artifacts_sha256'].items():
        if sha((task.path/name).read_bytes()) != digest: raise ValueError(f'frozen site artifact mismatch: {name}')
    for name, digest in manifest['shared_artifacts_sha256'].items():
        if sha((CENSUS_DIR/name).read_bytes()) != digest: raise ValueError(f'frozen shared artifact mismatch: {name}')
    if manifest['capture_sha256'] != sha(task.capture.read_bytes()) or manifest['vendor_lock_sha256'] != r6.sha(r6.ROOT/'vendor/sources.lock.json'):
        raise ValueError('capture helper or checking libraries differ from the frozen site')
    expected = r6.read_json(task.path/'expected.json')
    if sha(gzip.decompress((task.path/'challenge.ndjson.gz').read_bytes())) != expected['challenge_sha256']: raise ValueError('challenge export differs')
    if expected['task_id'] != task.id or expected['policy'] != r6.policy([task.local, task.whole], True, task=task):
        raise ValueError('frozen validation policy differs from evaluator policy')
    result = next(r for r in frozen['results'] if r['site_id'] == task.id)
    if result['status'] != 'admitted' or result['challenge_sha256'] != expected['challenge_sha256']: raise ValueError('census result differs')
    return manifest, expected


def get(site_id):
    """A verified site, registered in the frozen registry for this process. The two controls are returned unchanged."""
    if site_id in (r6.D1.id, r6.C8.id): return task_spec.get(site_id)
    entry = next((s for s in census.census()['sites'] if s['site_id'] == site_id), None)
    if entry is None: raise ValueError(f'Unknown census site: {site_id}')
    task = SiteTask(entry); frozen_site(task)
    existing = task_spec.TASKS.get(site_id)
    if existing is not None and (not isinstance(existing, SiteTask) or existing.entry != entry): raise ValueError('registry already holds a different task')
    task_spec.TASKS[site_id] = task
    return task


def register_primary():
    """Every reviewed primary site, verified and registered; used by the site supervisor in its own process."""
    return [get(site_id) for site_id in primary()]


def instrumented(task, helper_name, tactic):
    """The census freeze's byte-span instrumentation, renamed exactly as `proposal_episode.compile_input` renames the anchor form."""
    source = site_freeze.instrument(census.pristine(), task.site).decode()
    if source.count('r6_capture_human') != 1 or source.count('import Capture\n') != 1: raise ValueError('instrumented source is not the census form')
    return source.replace('import Capture\n', f'import {helper_name}\n').replace('r6_capture_human', tactic)


def compile_input(run, name, helper_name, helper_text, task):
    root = run/name
    root.mkdir()
    (root/(helper_name+'.lean')).write_text(helper_text)
    pristine = census.pristine().decode()
    tactic = 'r6_prepare' if helper_name == 'PreparationCapture' else 'r6_capture_proposal'
    source = instrumented(task, helper_name, tactic)
    (root/'Frozen.lean').write_text(source)
    (root/'source.patch').write_text(''.join(difflib.unified_diff(pristine.splitlines(True), source.splitlines(True),
                                                               fromfile='Pristine.lean', tofile='Frozen.lean')))
    return root


def capture_source(task, preparation=False):
    """The frozen overlay transformation, applied to the site helper."""
    return overlay.capture_source(task, preparation)


def same_environment():
    """The site's environment lock and compiled-environment inventory equal the D1 control's, byte for byte."""
    for name in ('upstream-lake-manifest.json', 'upstream-lakefile.toml', 'lean-toolchain', 'Pristine.lean'):
        if (CENSUS_DIR/name).read_bytes() != (r6.D1.path/name).read_bytes(): raise ValueError(f'environment differs from D1: {name}')
    if gzip.decompress((CENSUS_DIR/'environment-inventory.json.gz').read_bytes()) != gzip.decompress((r6.D1.path/'environment-inventory.json.gz').read_bytes()):
        raise ValueError('compiled-environment inventory differs from D1')


def setup(run, task, packages):
    """The frozen setup, run on the registered D1 control, with the site's frozen expectation substituted."""
    _, expected = frozen_site(task); same_environment()
    tools = downstream.setup(run, r6.D1, packages)
    if tools['expected']['environment'] != expected['environment']: raise ValueError('site expectation environment differs from the verified setup')
    tools['expected'] = expected
    return tools


def prepare(run, task, tools):
    """`proposal_episode.prepare` to the prepared problem, on the site: same stages, same receipts, same context equality."""
    inputs = compile_input(run, 'preparation-input', 'PreparationCapture', capture_source(task, True), task)
    compiler = tools['compiler']
    mounts = [*tools['mounts'], (inputs, '/input')]
    built = site_stage.stage(run, 'preparation-build', compiler/'bin/lean',
        [*tools['loads'], '-R', '/input', '-o', '/out/PreparationCapture.olean', '/input/PreparationCapture.lean'],
        mounts, compiler=compiler, env={'LEAN_PATH': tools['lean_path']+':/out'}, extra_binaries=tools['extras'])
    prepared = site_stage.stage(run, 'preparation', compiler/'bin/lean',
        [*tools['loads'], '-R', '/input', '-o', '/out/Frozen.olean', '/input/Frozen.lean'],
        [*mounts, (built, '/capture')], compiler=compiler, extra_binaries=tools['extras'],
        env={'LEAN_PATH': tools['lean_path']+':/capture', 'R6_CAPTURE_OUTPUT': '/out/context.json',
             'R6_PREPARE_OUTPUT': '/out/reification.json'})
    context = r6.read_json(prepared/'context.json')
    downstream.require(context == r6.read_json(task.path/'context/local-context.json'), 'preparation changed frozen context')
    reified = r6.read_json(prepared/'reification.json')
    r6.write_json(run/'input-ir.json', reified['ir'])
    output = site_stage.stage(run, 'pipeline-prepare', tools['driver'], ['prepare', '/input-ir.json', '/out/prepared.json'],
                           [(run/'input-ir.json', '/input-ir.json')])
    shutil.copyfile(output/'prepared.json', run/'prepared.json')
    prepared = r6.read_json(run/'prepared.json')
    projection = payload.project_context(context)
    r6.write_json(run/'sanitized-context.json', projection)
    r6.write_json(run/'payload-audit.json', {
        'sanitized_context_sha256': r6.sha(run/'sanitized-context.json'), 'source_context_sha256': r6.sha(task.path/'context/local-context.json'),
        'context_projection_is_model_visible': False, 'context_policy': 'farkas_rows_only_v1',
        'let_facts_preserved': [r['name'] for r in context['telescope'] if r['kind'] == 'let'],
        'reifier_omissions': reified['skipped_locals'], 'farkas_omissions': prepared['farkas_omissions']})
    events.append(run, 'payload', 'prepared_problem', {'prepared_sha256': r6.sha(run/'prepared.json'), 'input_ir_sha256': r6.sha(run/'input-ir.json'),
        'payload_audit_sha256': r6.sha(run/'payload-audit.json')})
    return prepared, reified
