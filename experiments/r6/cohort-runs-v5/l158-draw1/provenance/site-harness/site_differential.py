"""R6-013 differential control: the repaired preparation reifies exactly what reconstruction reifies, and the frozen equality
guard still rejects any difference.

Each case is a small Lean file whose one obligation exhibits a preparation hazard: absent directives, existing directives
(a numeral definition the reifier asks to unfold), an identifier that is not SMT-safe, an unsafe identifier whose sanitized
form collides with an existing safe name, duplicate `this` locals, and all of them combined. For each case, natively and
through the frozen stages:

1. the *repaired* preparation helper (`site_task.capture_source(…, True)`) records the input IR and the renamed search context;
2. reconstruction (`r6_capture_proposal`, the frozen proposal helper) receives a packet whose `input_ir` is that IR, and must
   pass the unchanged guard — the packet deliberately carries no certificate, so the stage then fails at the next check,
   whose message is recorded; the guard's own message must be absent;
3. the same packet with its directives removed, and with one renamed identifier reverted, must each fail *at the guard*;
4. the *unrepaired* helper (the frozen R6-001 overlay) is run on the same case for contrast, and its IR is sent the same way.

The event log of each case run borrows a registered census site's identity only because the frozen stages require one; the
compiled source is the case's own. No proposal, no provider, no credential.
"""
import argparse
import copy
import json
from pathlib import Path
import shutil
import time

import events
import proposal_instrument as overlay
import run as r6
import site_stage
import site_task

RUNS = r6.ROOT/'census-runs/differential-v1'
HOST_SITE = 'bracket-l070'  # event-log identity only
GUARD = 'R6 proposal input differs from freshly reified goal/context'
CASES = {
    'absent_directives': ('(a b : Int) (h : a ≤ b)', 'a ≤ b + 1', '', []),
    'existing_directives': ('(x : ℕ) (hK : R6Diff.K = 7) (hx : x < R6Diff.K)', 'x < 8', '', []),  # K is a numeral definition: the reifier asks to unfold it
    'unsafe_name': ("(c c' : Int) (hlt : c < c')", "c ≤ c' - 1", '', ["c'"]),
    'collision_with_safe_name': ("(c_ c' : Int) (hlt : c_ < c')", "c_ ≤ c' - 1", '', ["c'"]),
    'duplicate_this': ('(a b : Int) (h : a ≤ b)', 'a ≤ b + 2', 'have : a ≤ b := h\n  have : b ≤ b + 1 := by omega\n  ', ['this']),
    'combined': ("(c_ c' : Int) (hlt : c_ < c')", "c_ ≤ c' + 1", "have : c_ ≤ c' := by omega\n  have : c' ≤ c' + 1 := by omega\n  ", ["c'", 'this']),
}
PRELUDE = 'import Mathlib\nimport {helper}\n\nnamespace R6Diff\n\ndef K : ℕ := 7\n\n'


def source(case, helper, tactic):
    binders, goal, steps, _ = CASES[case]
    return (PRELUDE.format(helper=helper) + f'theorem obligation {binders} : {goal} := by\n  {steps}{tactic} "R6Diff.obligation.r6_site" "{case}"\n\nend R6Diff\n')


def compile_case(run, name, helper_name, helper_text, text, tools, env):
    """Two frozen-shaped stages: the helper, then the case file importing it."""
    inputs = run/(name+'-input'); inputs.mkdir()
    (inputs/(helper_name+'.lean')).write_text(helper_text); (inputs/'Frozen.lean').write_text(text)
    compiler = tools['compiler']; mounts = [*tools['mounts'], (inputs, '/input')]
    built = site_stage.stage(run, name+'-build', compiler/'bin/lean',
        [*tools['loads'], '-R', '/input', '-o', f'/out/{helper_name}.olean', f'/input/{helper_name}.lean'],
        mounts, compiler=compiler, env={'LEAN_PATH': tools['lean_path']+':/out'}, extra_binaries=tools['extras'])
    try:
        out = site_stage.stage(run, name, compiler/'bin/lean', [*tools['loads'], '-R', '/input', '-o', '/out/Frozen.olean', '/input/Frozen.lean'],
                               [*mounts, (built, '/capture')], compiler=compiler, extra_binaries=tools['extras'],
                               env={'LEAN_PATH': tools['lean_path']+':/capture', 'R6_CAPTURE_OUTPUT': '/out/context.json', **env})
        return out, None
    except site_stage.StageFailure:
        record = run/'stages'/name
        return record/'output', (record/(name+'.stdout')).read_text()+(record/(name+'.stderr')).read_text()


def reconstruct(run, name, case, packet, tools):
    path = run/(name+'-packet.json'); r6.write_json(path, packet)
    helper = site_task.capture_source(types_task(), False)
    tools_packet = {**tools, 'mounts': [*tools['mounts'], (path, '/evidence.json')]}
    _, log = compile_case(run, name, 'ProposalCapture', helper, source(case, 'ProposalCapture', 'r6_capture_proposal'), tools_packet,
                          {'R6_PROPOSAL_PACKET': '/evidence.json'})
    return {'guard_rejected': log is not None and GUARD in log, 'failed': log is not None,
            'first_error': None if log is None else next((l for l in log.splitlines() if 'error' in l), log[:300])[:300]}


def types_task():
    return site_task.get(HOST_SITE)


def packet_for(ir):
    return {'input_ir': ir, 'certificate': {}, 'final_ir': {}, 'trace': {}}


def revert_rename(ir, context):
    """The IR with one renamed identifier restored to its original spelling everywhere it occurs."""
    renamed = [e for e in context if e['original_name'] != e['search_name'] and e['original_name']]
    if not renamed: return None
    old, new = renamed[0]['search_name'], renamed[0]['original_name']
    text = json.dumps(ir).replace(f'"{old}"', json.dumps(new))
    return json.loads(text)


def run_case(case, tools, runs):
    run = runs/case; run.mkdir(parents=True); types_task()  # registered before the event log is opened
    events.append(run, 'episode', 'episode_started', {'purpose': 'differential preparation control', 'case': case, 'borrowed_identity': HOST_SITE}, task_id=HOST_SITE)
    task = types_task(); result = {'case': case, 'expected_renames': CASES[case][3]}
    for variant, helper in (('repaired', site_task.capture_source(task, True)), ('unrepaired', overlay.capture_source(task, True))):
        out, log = compile_case(run, f'prepare-{variant}', 'PreparationCapture', helper, source(case, 'PreparationCapture', 'r6_prepare'), tools,
                                {'R6_PREPARE_OUTPUT': '/out/reification.json'})
        if log is not None: result[variant] = {'prepared': False, 'error': log[:500]}; continue
        reified = r6.read_json(out/'reification.json'); ir = reified['ir']
        record = {'prepared': True, 'user_directives': ir.get('user_directives'), 'search_context': reified.get('search_context'),
                  'hypothesis_names': [h['name'] for h in ir['context']['hypotheses']],
                  'free_var_names': [v['name'] for v in ir['context']['free_vars']],
                  'same_ir': reconstruct(run, f'reconstruct-{variant}', case, packet_for(ir), tools)}
        if variant == 'repaired':
            stripped = copy.deepcopy(ir); stripped.pop('user_directives', None)
            record['directives_removed'] = reconstruct(run, 'reconstruct-directives-removed', case, packet_for(stripped), tools)
            reverted = revert_rename(ir, reified.get('search_context') or [])
            record['rename_reverted'] = None if reverted is None else reconstruct(run, 'reconstruct-rename-reverted', case, packet_for(reverted), tools)
        result[variant] = record
    r6.write_json(run/'differential.json', result)
    events.append(run, 'differential', 'recorded', {'differential_sha256': r6.sha(run/'differential.json')})
    events.append(run, 'episode', 'episode_finished', {'differential_sha256': r6.sha(run/'differential.json')})
    import site_representability; site_representability.seal(run)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packages-dir', type=Path, default=r6.ROOT.parents[1]/'lean-bridge/.lake/packages')
    parser.add_argument('--runs', type=Path, default=RUNS)
    parser.add_argument('--cases', nargs='*', default=list(CASES))
    args = parser.parse_args()
    site_task.verify_lock(); runs = args.runs.resolve()
    if (runs/'differential.json').exists(): raise SystemExit('differential already recorded: '+str(runs))
    setup_run = runs/'setup'; setup_run.mkdir(parents=True); types_task()  # registered before the event log is opened
    events.append(setup_run, 'episode', 'episode_started', {'purpose': 'tools for the differential control'}, task_id=HOST_SITE)
    tools = site_task.setup(setup_run, types_task(), args.packages_dir.resolve())
    results = {}
    for case in args.cases:
        started = time.monotonic(); results[case] = run_case(case, tools, runs); results[case]['seconds'] = round(time.monotonic()-started, 1)
        print(json.dumps({case: {v: (results[case][v].get('same_ir') if isinstance(results[case].get(v), dict) else None) for v in ('repaired', 'unrepaired')}}), flush=True)
    events.append(setup_run, 'episode', 'episode_finished', {})
    r6.write_json(runs/'differential.json', {'schema_version': 'r6-differential-1', 'cases': list(results), 'results': results,
                                             'site_task_sha256': r6.sha(r6.ROOT/'site_task.py'), 'program_sha256': r6.sha(Path(__file__)),
                                             'guard_message': GUARD, 'scope': 'native preparation and reconstruction stages on synthetic cases; no proposal, no provider'})


if __name__ == '__main__':
    main()
