#!/usr/bin/env python3
"""R6-016 analysis, frozen before the lock: R6-015's (`r6-015/analysis.py`, frozen at its lock), with the changes of
`R6-016-PROPOSAL.md`, revision 2, section 6:
- **the axiom gates are reported separately** (section 2), per episode and per target: every axiom in the allowlist, and no
  axiom added against the site's frozen expected targets. Consumed and validated needs both, as in R6-015;
- **control 9 is verified and recomputed**, as control 3 is (`check_control9`, `control9.evaluate`);
- **control 8 is checked against the program the lock names**, `qualification-audit-v2`;
- **the diagnosis's record is verified** by identity, provenance and recomputation (`check_diagnosis`). It is reported, and
  counts toward nothing;
- **control 5's labels are R6-016's** (`labels.py`): 12 expected passes, l096's and l099's learned maps added;
- **failures after a proof** (an acceptance or control-8 failure) are listed for diagnosis, which closes the gap R6-015's record
  disclosed.

The failure-stage table (`STAGES`) is R6-015's: R6-016's bridge (`64585867`) raises the same messages as `476fab31`, checked
line by line.

    analysis.py --runs DIR --control3 RECORD.json --control9 RECORD.json --control8 RECORD.json --diagnosis RECORD.json \
                --output ANALYSIS.json

Runs after the replay (`replay_campaign.py run`), control 3 (`control3.py`), control 9 (`control9.py`), control 8
(`replay_campaign.py control8`) and the diagnosis (`diagnose_l070.py run`), under the R6-016 lock, which must verify before and
after. Reads only bound evidence:
- **every planned run** is bound to the locked plan by `replay_campaign.bound` (seal, spec, start record and provenance, terminal
  event, seal acceptance, verdict identity, packet, and for a proof the receipt). A run that does not bind stops the analysis;
- **the control-3, control-9 and control-8 records are evidence, not verdicts.** Each predicate is recomputed. Control 8's record must cover
  exactly the plan, each entry bound to the current run's seal, verdict, export and residual digests and audited with the locked
  program; its predicate is recomputed from the retained report. Control 3's record must be the frozen probe, run under this lock
  and bridge by the locked programs, not a dry run; its predicate is recomputed from its results (`control3.evaluate`). Control
  9's likewise, with its frozen cases (`control9.evaluate`). The diagnosis's record must be the locked program's, run on the
  sealed l070 draw 5 export; its classifications are recomputed from its attempts. A record whose flags disagree with the recomputation is rejected. Control 8's recorded commands, and each run's residual command, must be
  the locked program on the planned targets in the frozen environment, their exit codes agreeing with the reports. Afterwards every
  run's retained files are revalidated against its unchanged seal (exports, residuals, events, kernel reports), and every consumed
  input is rechecked;
- **the step-3 record** (`R6-015-MUTATIONS-2.json`, bound by the lock) supplies the maps and classes; **R6-016's control-5
  labels** (`R6-016-CONTROL-5-LABELS.json`, bound by the lock and verified again here) supply the labels;
- **R6-014's analysis** (`R6-014-BLOCK2-ANALYSIS.json`, bound by the lock) supplies the original closers (control 5) and the
  reference route's closures (control 7).

**Consumed and validated** (the proposal's acceptance, for one episode): the outcome is a proof; the receipt names this
certificate, the closer and the constrained final step (checked in binding); the local and whole kernel replays accepted; at both
targets, every axiom among `propext`, `Classical.choice`, `Quot.sound` (the allowlist) and no axiom added (unchanged), the two
gates reported separately; and control 8's predicate met.

**Failure stages**, from the verdict's bound evidence only. A failed reconstruction is classified by its first bridge error line,
against `STAGES` in order:
- certificate decoding, the packet binding (the fresh-reification guard), the bridge's gate, the specialization gate;
- selection; fact assertion (casts and opaque atoms included); the fold; the constrained final step;
- otherwise `unclassified`, which requires diagnosis.

A kernel rejection is `kernel`; a checker rejection is `checker`. A harness outcome (an unobserved receipt, a route mismatch, a
changed context, an unprinted residual, a stage or harness failure) is not a route result and requires diagnosis.

**Units:** results per obligation (4), per map (6) and per class (5), by source, never merged.

**The measurement** (the 36 retained certificates of the four obligations) is reported on its own: consumed and validated, of 36,
per obligation, map and class.

**The overall outcome, by R6-015's frozen definitions** (R6-016's section 6: every control behaves as frozen):
- **complete success**: all 36 consumed and validated (so all six maps, both sources, all four obligations, both l166 maps), and
  controls 1, 2, 3, 4, 6, 8 and 9 as frozen, and control 5's twelve expected-pass entries passing;
- **none**: none of the 36 consumed and validated;
- **partial**: anything else, with the reasons and the failures located.

**The controls, each recomputed from bound evidence:**
- **control 1**: every injected invalid mutation is rejected by the checker, its bypass is recorded, and the constrained closer
  fails in its final step because the sum does not cancel;
- **control 4**: l170's checked proposals are rejected by the checker; the injected one fails in the final step as not positive.
  An earlier refusal or a harness failure fails these controls and requires diagnosis;
- **control 5**: each entry against its label. A pass is consumed and validated with R6-014's closer named. The four entries without
  a prediction are diagnostic only;
- **control 6**: on every episode that reached selection, a `Nat` comparison takes `term_mode_nat`, any other `term_mode_int`;
- **control 7** is cited, never counted as consumption.

Axiom deltas, removals included, are retained per episode.
"""
import argparse
from collections import Counter
import functools
import gzip
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
if str(R6) not in sys.path: sys.path.insert(0, str(R6))
if str(HERE) not in sys.path: sys.path.insert(0, str(HERE))

import events  # noqa: E402
import run as r6  # noqa: E402
import control3  # noqa: E402
import control9  # noqa: E402
import diagnose_l070  # noqa: E402
import labels  # noqa: E402
import replay_campaign  # noqa: E402
import replay_lock  # noqa: E402
import site_task  # noqa: E402

MUTATIONS = R6/'reviews/2026-10-01/R6-015-MUTATIONS-2.json'
LABELS = labels.RECORD
R6014 = R6/'reviews/2026-09-29/R6-014-BLOCK2-ANALYSIS.json'
EXPECTED_PASSES = 12
TARGETS = ('l166', 'l175', 'l178', 'l204')
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
HARNESS_OUTCOMES = {'consumption_unobserved', 'route_mismatch', 'context_changed', 'residual_unprinted', 'stage_failure', 'harness_failure'}
STAGES = (  # (stage, detail, substring of the first bridge error line), in order
    ('certificate_decode', 'payload', 'proof_broker_term: cert missing'),
    ('certificate_decode', 'not farkas', 'proof_broker_term: cert is not a Farkas witness'),
    ('certificate_decode', 'coefficient', 'proof_broker_term: malformed coefficient'),
    ('certificate_decode', 'entry', 'proof_broker_term: witness entry missing hypothesis'),
    ('packet_binding', 'input IR', 'R6 proposal input differs'),
    ('bridge_gate', 'verifier', 'verifier did not'),
    ('specialization_gate', 'specialization', 'records a specialization'),
    ('specialization_gate', 'specialization', 'records no Nat → Int type specialization'),
    ('selection', 'outside the route', 'is outside the constrained route'),
    ('selection', 'goal shape', 'goal must have shape'),
    ('selection', 'goal shape', 'witness lacks neg_goal'),
    ('selection', 'goal shape', 'cert/goal mismatch'),
    ('fact_assertion', 'name not in scope', 'witness names hypothesis'),
    ('fact_assertion', 'cast', 'the ℕ→ℤ lift cannot cast'),
    ('fact_assertion', 'atom', 'but the extraction has no atom'),
    ('constrained_final_step', 'does not cancel', '(constrained): the weighted sum does not cancel'),
    ('constrained_final_step', 'not positive', 'which is not positive'),
    ('constrained_final_step', 'reaches hypotheses', '(constrained): the positivity proof reaches hypotheses'),
    ('constrained_final_step', 'kernel rejected the step', '(constrained): the kernel rejected the positivity proof'),
    ('fold', 'hypothesis shape', 'hypothesis shape outside'),
    ('fold', 'negative coefficient', 'negative coefficient'),
    ('fold', 'zero coefficients', 'all coefficients are zero'),
    ('fold', 'empty witness', 'empty witness'),
    ('fold', 'name not in scope', "' not in scope"),
    ('fold', 'shadowed', 'is ambiguous (shadowed)'),
)


def classify(verdict):
    """(stage, detail, line) for a non-proof, from the verdict's bound evidence only."""
    outcome = verdict['outcome']
    if outcome == 'proved': return ('proved', None, None)
    if outcome == 'certificate_rejected': return ('checker', None, None)
    if outcome == 'kernel_rejected': return ('kernel', None, str(verdict.get('detail'))[:300])
    if outcome in HARNESS_OUTCOMES: return ('harness', outcome, str(verdict.get('detail'))[:300])
    if outcome != 'reconstruction_failed': return ('unclassified', outcome, None)
    errors = (verdict.get('detail') or {}).get('errors') or []
    line = next((e for e in errors if 'proof_broker' in e or 'R6 proposal' in e), None)
    if line is None: return ('unclassified', 'no bridge error line', errors[0][:300] if errors else None)
    for stage, detail, needle in STAGES:
        if needle in line: return (stage, detail, line[:300])
    return ('unclassified', 'no stage matched', line[:300])


def reconstruct_events(run):
    return [(r['event'], r['payload']['data']) for r in events.read(run/'events.ndjson') if r['source'] == 'child_report' and r['stage'] == 'reconstruct']


AUDIT_ARGV0 = str(replay_lock.AUDIT_TOOL.relative_to(R6))
AUDIT_ENV = {'PATH': '/usr/bin:/bin', 'LEAN_SYSROOT': str(replay_lock.AUDIT_TOOLCHAIN)}


def targets(site):
    task = site_task.get(site)
    return task.local, task.whole


def residual_command(run):
    return r6.read_json(run/'residual/command.json')


def revalidate(run):
    """Every retained file of the run against its seal, the event chain, no unsealed file; returns the seal's digest."""
    replay_campaign.sealed(run)
    return r6.sha(run/'seal.json')


def packet_certificate(run):
    return r6.read_json(run/'evidence.json')['certificate']


def current(run, proved):
    """The run's current digests: its seal and verdict, and for a proof its export (packed and unpacked) and residual."""
    d = {'seal_sha256': r6.sha(run/'seal.json'), 'verdict_sha256': r6.sha(run/'verdict.json')}
    if proved:
        d.update(solution_sha256=r6.sha(run/'solution.ndjson.gz'), residual_sha256=r6.sha(run/'residual.txt'),
                 export_sha256=hashlib.sha256(gzip.decompress((run/'solution.ndjson.gz').read_bytes())).hexdigest())
    return d


@functools.lru_cache(maxsize=None)
def original_axioms(site):
    """The site's frozen original targets and their axioms (`expected.json`, verified by `site_task.frozen_site`): the baseline
    R6's final validation computes each run's delta against."""
    _, expected = site_task.frozen_site(site_task.get(site))
    return {t['name']: tuple(sorted(t['axioms'])) for t in expected['targets']}


def axiom_gates(run, verdict, site):
    """The two axiom gates, separately, per target (proposal section 2), recomputed: every axiom in the allowlist, from the
    kernel's report; and no axiom added, the delta recomputed from that report against the site's frozen original targets. The
    kernel reports must be complete, and the verdict's recorded delta must equal the recomputation; otherwise the analysis
    stops. The deltas are retained either way."""
    local, whole = targets(site)
    original = original_axioms(site)
    if set(original) != {local, whole}: raise SystemExit(f"{run.name}: the site's frozen targets are not its local and whole targets")
    recorded = verdict.get('axiom_delta')
    if not isinstance(recorded, dict) or set(recorded) != {local, whole}:
        raise SystemExit(f"{run.name}: the verdict's axiom delta does not name exactly the local and whole targets")
    gates = {}
    for kind, name in (('local', local), ('whole', whole)):
        report = json.loads(gzip.decompress((run/f'validation-{kind}.raw.json.gz').read_bytes()))
        rows = report.get('targets')
        if (report.get('accepted') is not True or not isinstance(rows, list) or len(rows) != 1 or not isinstance(rows[0], dict)
                or rows[0].get('name') != name or not isinstance(rows[0].get('axioms'), list)
                or not all(isinstance(x, str) for x in rows[0]['axioms'])):
            raise SystemExit(f'{run.name}: the {kind} kernel report is not an accepted report of {name} with its axioms')
        axioms, before = set(rows[0]['axioms']), set(original[name])
        delta = {'added': sorted(axioms - before), 'removed': sorted(before - axioms)}
        if recorded[name] != delta:
            raise SystemExit(f"{run.name}: the verdict's {kind} axiom delta disagrees with its kernel report and the frozen targets")
        gates[kind] = {'target': name, 'kernel_accepted': True, 'axioms': sorted(axioms), 'original': sorted(before),
                       'allowlist': axioms <= ALLOWED_AXIOMS, 'unchanged': not delta['added'], 'delta': delta}
    return gates


def check_control8(record, lock_sha, frozen, verdicts, runs, plan):
    """Control 8, recomputed from retained evidence. Rejects a record that does not cover exactly the plan, whose entries do not
    bind to the current runs, or whose flags disagree with the recomputation. Returns {id: predicate met} for the proofs."""
    if (record.get('schema_version') != 'r6-016-control-8-1' or record.get('lock_sha256') != lock_sha
            or record.get('audit_lock_sha256') != frozen['data_sha256']['policies/qualification-audit-v2.sha256.json']):
        raise SystemExit('control 8: identity')
    results = record.get('results') or {}
    if set(results) != set(verdicts): raise SystemExit('control 8 does not cover exactly the plan')
    met = {}
    for i, verdict in verdicts.items():
        entry, proved = results[i], verdict['outcome'] == 'proved'
        if entry.get('bound') is not True or entry.get('outcome') != verdict['outcome'] or entry.get('audited') is not proved:
            raise SystemExit(f'control 8: {i} does not describe the run')
        now = current(runs/i, proved)
        for key in ('seal_sha256', 'verdict_sha256') + (('solution_sha256', 'residual_sha256') if proved else ()):
            if entry.get(key) != now[key]: raise SystemExit(f'control 8: {i} {key} differs from the run')
        if not proved: continue
        local, whole = targets(plan[i]['site'])
        command = entry.get('command') or {}
        inputs = command.get('inputs') or {}
        report_exit = (entry.get('report') or {}).get('exit')
        if (command.get('argv') != [AUDIT_ARGV0, '<tmp>/export.ndjson', local, whole, '<tmp>/residual.txt', '<tmp>/report.json']
                or command.get('env') != AUDIT_ENV or type(command.get('exit_code')) is not int or command.get('exit_code') != report_exit
                or command.get('tool_sha256') != frozen['binaries_sha256']['audit_tool']
                or (inputs.get('<tmp>/export.ndjson') or {}).get('sha256') != now['export_sha256']
                or (inputs.get('<tmp>/residual.txt') or {}).get('sha256') != now['residual_sha256']):
            raise SystemExit(f'control 8: {i} was not audited on this export and residual with the locked program, targets and environment')
        printed = residual_command(runs/i)  # the residual itself: printed from this export by the locked program
        if (printed.get('argv') != [AUDIT_ARGV0, '--synthetic', '<tmp>/export.ndjson', local, whole, '-', 'residual/report.json']
                or printed.get('env') != AUDIT_ENV or printed.get('exit_code') != 0 or type(printed.get('exit_code')) is not int
                or printed.get('tool_sha256') != frozen['binaries_sha256']['audit_tool']
                or printed.get('audit_lock_sha256') != frozen['data_sha256']['policies/qualification-audit-v2.sha256.json']
                or (printed.get('inputs') or {}).get('<tmp>/export.ndjson', {}).get('sha256') != now['export_sha256']):
            raise SystemExit(f'control 8: {i} has a residual not printed from this export by the locked program')
        unmet = replay_campaign.predicate(entry.get('report') or {})
        if unmet != entry.get('unmet'): raise SystemExit(f'control 8: {i} records a predicate its report does not support')
        met[i] = not unmet
    if record.get('passed') is not all(met.values()): raise SystemExit('control 8: the summary disagrees with its entries')
    return met


def check_control3(record, lock_sha, frozen):
    """Control 3's identity, provenance and results; its predicate recomputed. A dry run or a contradictory record is rejected."""
    if record.get('schema_version') != control3.SCHEMA or record.get('control') != 3 or 'dry_run' in record:
        raise SystemExit('control 3: not a control-3 record (or a dry run)')
    if record.get('lock_sha256') != lock_sha or record.get('bridge_rev') != frozen['bridge_rev'] \
            or record.get('instrumented_tactic_sha256') != frozen['instrumented_tactic_sha256']:
        raise SystemExit('control 3: not run under this lock and bridge')
    sources = record.get('sources_sha256') or {}
    if set(sources) != {str(f.relative_to(R6)) for f in control3.SOURCES} or any(frozen['python_sha256'].get(k) != v for k, v in sources.items()):
        raise SystemExit('control 3: not run by the locked programs')
    if (record.get('evidence') or {}).get('coefficients') != control3.PROBE: raise SystemExit('control 3: not the frozen probe')
    unmet = control3.evaluate(record.get('results') or {})
    if unmet != record.get('unmet') or record.get('passed') is not (not unmet): raise SystemExit('control 3: the record contradicts its results')
    return not unmet


def check_control9(record, lock_sha, frozen):
    """Control 9's identity, provenance and results, as control 3's; its predicate recomputed (`control9.evaluate`)."""
    if record.get('schema_version') != control9.SCHEMA or record.get('control') != 9 or 'dry_run' in record:
        raise SystemExit('control 9: not a control-9 record (or a dry run)')
    if record.get('lock_sha256') != lock_sha or record.get('bridge_rev') != frozen['bridge_rev'] \
            or record.get('instrumented_tactic_sha256') != frozen['instrumented_tactic_sha256']:
        raise SystemExit('control 9: not run under this lock and bridge')
    sources = record.get('sources_sha256') or {}
    if set(sources) != {str(f.relative_to(R6)) for f in control9.SOURCES} or any(frozen['python_sha256'].get(k) != v for k, v in sources.items()):
        raise SystemExit('control 9: not run by the locked programs')
    frozen_cases = {n: {'statement': c[1], 'witness': c[2], 'checker': c[3], 'expectation': c[4]} for n, c in control9.CASES.items()}
    if record.get('cases') != frozen_cases or any((record.get('evidence') or {}).get(n, {}).get('coefficients') != c['witness']
                                                  for n, c in frozen_cases.items()):
        raise SystemExit('control 9: not the frozen cases')
    unmet = control9.evaluate(record.get('results') or {})
    if unmet != record.get('unmet') or record.get('passed') is not (not unmet): raise SystemExit('control 9: the record contradicts its results')
    return not unmet


def export_digests():
    """The l070 draw 5 export's digests, packed, sealed and unpacked."""
    source = R6/diagnose_l070.RUN
    return {'packed': r6.sha(source/'solution.ndjson.gz'),
            'sealed': r6.read_json(source/'seal.json')['retained_sha256'].get('solution.ndjson.gz'),
            'unpacked': hashlib.sha256(gzip.decompress((source/'solution.ndjson.gz').read_bytes())).hexdigest()}


def check_diagnosis(record, lock_sha, frozen):
    """The diagnosis's identity, provenance and command, bound to the sealed export; its classifications recomputed from its
    attempts (`diagnose_l070.classify`). Reported; it counts toward nothing."""
    d = diagnose_l070
    selected = r6.read_json(replay_lock.AUDIT_LOCK)['selection']['regression'][d.SLOT]   # the target, from v2's locked selection
    if (record.get('schema_version') != d.SCHEMA or record.get('slot') != d.SLOT or record.get('run') != d.RUN
            or selected['run'] != f'experiments/r6/{d.RUN}' or record.get('local') != selected['local']
            or record.get('lock_sha256') != lock_sha):
        raise SystemExit('diagnosis: identity')
    sources = record.get('sources_sha256') or {}
    if (record.get('tool_sha256') != frozen['binaries_sha256']['diagnosis_tool']
            or sources.get('r6-016/diagnose_l070.py') != frozen['python_sha256'].get('r6-016/diagnose_l070.py')
            or sources.get('r6-016/diagnosis/Diagnose.lean') != frozen['data_sha256']['r6-016/diagnosis/Diagnose.lean']
            or set(sources) != {'r6-016/diagnose_l070.py', 'r6-016/diagnosis/Diagnose.lean'}
            or record.get('audit_source_sha256') != r6.sha(d.AUDIT_SOURCE)):
        raise SystemExit('diagnosis: not run by the locked programs')
    command = record.get('command') or {}
    inputs = (command.get('inputs') or {}).get('<tmp>/export.ndjson') or {}
    export = export_digests()
    if (command.get('argv') != [str(d.TOOL.relative_to(R6)), '<tmp>/export.ndjson', selected['local'], '<tmp>/report.json']
            or command.get('env') != d.ENV or type(command.get('exit_code')) is not int or command.get('exit_code') != 0
            or command.get('tool_sha256') != record.get('tool_sha256')
            or inputs.get('packed_sha256') != export['packed'] or export['packed'] != export['sealed']
            or inputs.get('sha256') != export['unpacked']):
        raise SystemExit('diagnosis: not run on the sealed export with the locked program')
    report = record.get('report') or {}
    if 'refused' in report or 'error' in report or (report.get('diagnosis') or {}).get('located') is not True:
        raise SystemExit('diagnosis: no located report')
    pairs = d.classified(report)
    if pairs != record.get('pairs'): raise SystemExit('diagnosis: the record contradicts its attempts')
    if any(p['classification'] in d.INVALID for p in pairs):
        raise SystemExit(f"diagnosis: its evidence is inconsistent ({[p['basis'] for p in pairs if p['classification'] in d.INVALID]})")
    return {'pairs': pairs, 'atoms': len((report.get('diagnosis') or {}).get('atoms') or []),
            'positivity': (report.get('diagnosis') or {}).get('positivity')}


def analyse(runs, control3_path, control9_path, control8_path, diagnosis_path):
    frozen = replay_lock.verify_lock(); lock_sha = r6.sha(replay_lock.LOCK)
    inputs = [Path(control3_path), Path(control9_path), Path(control8_path), Path(diagnosis_path), MUTATIONS, LABELS, R6014]
    consumed = {str(p): r6.sha(p) for p in inputs}
    plan = replay_lock.planned(frozen); mutations = r6.read_json(MUTATIONS); r6014 = r6.read_json(R6014)
    control5_labels = labels.verify()['control_5']
    verdicts, seals = {}, {}
    for spec in plan.values():
        run = runs/spec['id']
        try:
            _, verdicts[spec['id']] = replay_campaign.bound(run, spec, frozen, lock_sha)
        except (OSError, ValueError, KeyError, replay_campaign.replay_episode.Outcome) as unbound:
            raise SystemExit(f"{spec['id']} does not bind: {unbound}")
        seals[spec['id']] = current(run, False)['seal_sha256']
    c8 = check_control8(r6.read_json(control8_path), lock_sha, frozen, verdicts, runs, plan)
    c3 = check_control3(r6.read_json(control3_path), lock_sha, frozen)
    c9 = check_control9(r6.read_json(control9_path), lock_sha, frozen)
    exported = export_digests(); diagnosis = check_diagnosis(r6.read_json(diagnosis_path), lock_sha, frozen)

    episodes = {}
    for spec in plan.values():
        i = spec['id']; run = runs/i; verdict = verdicts[i]
        stage, detail, line = classify(verdict)
        found = dict(reconstruct_events(run))
        proved = verdict['outcome'] == 'proved'
        gates = axiom_gates(run, verdict, spec['site']) if proved else None
        kernel_and_axioms = (proved and verdict.get('local_validated') is True and verdict.get('whole_validated') is True
                             and all(g['kernel_accepted'] and g['allowlist'] and g['unchanged'] for g in gates.values()))
        episodes[i] = {
            'site': spec['site'].removeprefix('bracket-'), 'arm': spec['source']['arm'], 'source': spec['source']['run'],
            'mutated': spec['coefficients'] is not None, 'injected': spec['inject_unverified'], 'outcome': verdict['outcome'],
            'stage': stage, 'stage_detail': detail, 'error_line': line, 'certificate_accepted': verdict.get('certificate_accepted'),
            'closer_selected': (found.get('closer_selected') or {}).get('closer'),
            'comparison_type': (found.get('closer_selected') or {}).get('comparison_type'),
            'gate_bypassed': 'certificate_gate_bypassed' in found and found['certificate_gate_bypassed'].get('certificate') == packet_certificate(run),
            'closer': verdict.get('closer'), 'final_step': verdict.get('final_step'), 'axiom_delta': verdict.get('axiom_delta'),
            'axiom_gates': gates,
            'allowlist': None if gates is None else all(g['allowlist'] for g in gates.values()),
            'unchanged': None if gates is None else all(g['unchanged'] for g in gates.values()),
            'kernel_and_axioms': kernel_and_axioms, 'control_8': c8.get(i) if proved else None,
            'consumed_and_validated': bool(kernel_and_axioms and c8.get(i))}

    # the measurement: the 36 retained certificates of the four obligations, reported on its own
    measurement = {i: e for i, e in episodes.items() if e['site'] in TARGETS and not e['mutated'] and not e['injected']}
    if len(measurement) != 36: raise SystemExit('the measurement is not 36 episodes')
    def unit(e, kind):
        s = mutations['sources'][e['source']]
        return json.dumps([e['site'], s['map' if kind == 'map' else 'class']], sort_keys=True)
    def tally(selected):
        proofs = [e for e in selected if e['outcome'] == 'proved']
        return {'episodes': len(selected), 'consumed_and_validated': sum(e['consumed_and_validated'] for e in selected),
                'stages': dict(Counter(e['stage'] if not e['consumed_and_validated'] else 'consumed_and_validated' for e in selected)),
                'proofs': len(proofs), 'allowlist_failed': sum(e['allowlist'] is False for e in proofs),
                'unchanged_failed': sum(e['unchanged'] is False for e in proofs),
                'control_8_failed': sum(e['control_8'] is False for e in proofs)}
    per_obligation = {site: {arm: tally([e for e in measurement.values() if e['site'] == site and e['arm'] == arm])
                             for arm in ('learned', 'deterministic')} for site in TARGETS}
    per_map, per_class = {}, {}
    for kind, table in (('map', per_map), ('class', per_class)):
        for key in sorted({unit(e, kind) for e in measurement.values()}):
            sel = [e for e in measurement.values() if unit(e, kind) == key]
            table[key] = {arm: tally([e for e in sel if e['arm'] == arm]) for arm in ('learned', 'deterministic') if any(e['arm'] == arm for e in sel)}
    if (len(per_map), len(per_class)) != (6, 5): raise SystemExit('the units are not 6 maps and 5 classes')

    # the controls, each recomputed from bound evidence
    def ids(pred): return [i for i, e in episodes.items() if pred(i, e)]
    def failed_at(e, detail):  # the constrained closer was reached, and failed in its final step, in this way
        return (e['certificate_accepted'] is False and e['gate_bypassed'] and e['outcome'] == 'reconstruction_failed'
                and (e['stage'], e['stage_detail']) == ('constrained_final_step', detail))
    c1 = ids(lambda i, e: e['site'] in TARGETS and e['mutated'] and e['injected'])
    c2 = ids(lambda i, e: e['site'] in TARGETS and e['mutated'] and not e['injected'])
    c4 = ids(lambda i, e: e['site'] == 'l170')
    c5 = ids(lambda i, e: '-control5-' in i)
    sizes = {'control_1': (len(c1), 24), 'control_2': (len(c2), 25), 'control_4': (len(c4), 9), 'control_5': (len(c5), 14)}
    for name, (got, want) in sizes.items():
        if got != want: raise SystemExit(f'{name} has {got} episodes, not {want}')
    controls = {
        'control_1': {'episodes': len(c1), 'failures': [i for i in c1 if not failed_at(episodes[i], 'does not cancel')],
                      'stages': dict(Counter(f"{episodes[i]['stage']}: {episodes[i]['stage_detail']}" for i in c1))},
        'control_2': {'episodes': len(c2), 'failures': [i for i in c2 if not episodes[i]['consumed_and_validated']],
                      'stages': dict(Counter(episodes[i]['stage'] for i in c2))},
        'control_3': {'passed': c3, 'record': str(control3_path)},
        'control_9': {'passed': c9, 'record': str(control9_path)},
        'control_4': {'episodes': len(c4), 'failures': [i for i in c4 if not (
                       failed_at(episodes[i], 'not positive') if episodes[i]['injected'] else episodes[i]['outcome'] == 'certificate_rejected')]},
        'control_6': {'checked': 0, 'failures': []},
        'control_7': {'cited': {s: {'outcome': r6014['arms']['deterministic_reference']['by_site'][f'bracket-{s}'],
                                    'closer': r6014['arms']['deterministic_reference']['closers'][f'bracket-{s}']} for s in TARGETS},
                      'counted_as_consumption': False},
        'control_8': {'passed': all(c8.values()), 'proofs': len(c8), 'failures': sorted(i for i, ok in c8.items() if not ok)},
    }
    for i, e in episodes.items():  # control 6: a Nat comparison takes the ℕ closer, any other the ℤ closer
        if e['closer_selected'] is None: continue
        controls['control_6']['checked'] += 1
        if (e['comparison_type'] in ('ℕ', 'Nat')) != (e['closer_selected'] == 'term_mode_nat'): controls['control_6']['failures'].append(i)
    for name in ('control_1', 'control_2', 'control_4', 'control_6'):
        controls[name]['passed'] = not controls[name]['failures']

    # control 5: each entry against its stated label; the expected passes are part of the overall outcome
    original = {}
    for slot, row in r6014['per_slot'].items():
        if row.get('closer'): original.setdefault(slot.split('/')[0].removeprefix('bracket-'), set()).add(row['closer'])
    entries = []
    for c in control5_labels:
        if c.get('retained') is False: entries.append({'site': c['site'], 'arm': 'deterministic', 'retained': False}); continue
        id_ = f"{c['site']}-control5-learned-draw{c['draws'][0]}" if c['source']['arm'] == 'learned' else f"{c['site']}-control5-deterministic"
        e = episodes[id_]; closers = original.get(c['site'], set())
        if len(closers) != 1: raise SystemExit(f"{c['site']}: R6-014's closer is not unique")
        passed = e['consumed_and_validated'] and e['closer'] == next(iter(closers))
        entries.append({'episode': id_, 'site': c['site'], 'arm': c['source']['arm'], 'map': c['map'], 'expectation': c['expectation'],
                        'passed': passed, 'original_closer': next(iter(closers)), 'closer': e['closer'], 'stage': e['stage'],
                        'predicted': c['expectation'] == 'expected_pass', 'requires_diagnosis': c['expectation'] == 'expected_pass' and not passed})
    predicted = [x for x in entries if x.get('predicted')]
    if len(predicted) != EXPECTED_PASSES: raise SystemExit(f'control 5 has {len(predicted)} expected-pass entries, not {EXPECTED_PASSES}')
    controls['control_5'] = {'episodes': len(c5), 'entries': entries, 'expected_pass': len(predicted),
                             'expected_pass_met': sum(x['passed'] for x in predicted), 'passed': all(x['passed'] for x in predicted),
                             'diagnostic_only': [x['episode'] for x in entries if 'episode' in x and not x['predicted']],
                             'requires_diagnosis': [x['episode'] for x in entries if x.get('requires_diagnosis')]}

    measured = sum(e['consumed_and_validated'] for e in measurement.values())
    frozen_controls = ('control_1', 'control_2', 'control_3', 'control_4', 'control_5', 'control_6', 'control_8', 'control_9')
    reasons = ([] if measured == 36 else [f'{36 - measured} of the 36 retained certificates not consumed and validated']) + \
              [f'{c} not as frozen' for c in frozen_controls if not controls[c]['passed']]
    outcome = 'complete_success' if not reasons else 'none' if measured == 0 else 'partial'
    after_proof = {i: [g for g, failed in (('kernel', not (e['axiom_gates'] and all(x['kernel_accepted'] for x in e['axiom_gates'].values()))),
                                           ('allowlist', e['allowlist'] is False), ('unchanged', e['unchanged'] is False),
                                           ('control_8', e['control_8'] is False)) if failed]
                   for i, e in episodes.items() if e['outcome'] == 'proved' and not e['consumed_and_validated']}
    requires = sorted({i for i, e in episodes.items() if e['stage'] in ('harness', 'unclassified')}
                      | set(controls['control_1']['failures']) | set(controls['control_4']['failures'])
                      | set(controls['control_5']['requires_diagnosis']) | set(after_proof))

    # afterwards: the lock, every run's retained files against its unchanged seal, and every consumed input
    replay_lock.verify_lock()
    for i, h in seals.items():
        try:
            if revalidate(runs/i) != h: raise ValueError('its seal changed')
        except (OSError, ValueError, KeyError) as changed:
            raise SystemExit(f'{i} changed during the analysis: {changed}')
    if any(r6.sha(Path(p)) != h for p, h in consumed.items()) or export_digests() != exported:
        raise SystemExit('an analysis input changed during the analysis')
    return {'schema_version': 'r6-016-analysis-1', 'lock_sha256': lock_sha, 'inputs_sha256': consumed,
            'outcome': outcome, 'outcome_reasons': reasons,
            'measurement': {'consumed_and_validated': measured, 'of': 36, 'per_obligation': per_obligation, 'per_map': per_map,
                            'per_class': per_class},
            'controls': controls, 'requires_diagnosis': requires, 'failures_after_proof': after_proof,
            'l070_diagnosis': diagnosis, 'episodes': episodes,
            'scope': 'R6-016, offline; reported separately from R6-014 and R6-015 and never pooled with them'}


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--runs', required=True); p.add_argument('--control3', required=True); p.add_argument('--control9', required=True)
    p.add_argument('--control8', required=True); p.add_argument('--diagnosis', required=True)
    p.add_argument('--output', required=True)
    args = p.parse_args()
    out = Path(args.output)
    if out.exists(): raise SystemExit(f'refusing to overwrite {out}')
    try:
        result = analyse(Path(args.runs).resolve(), Path(args.control3).resolve(), Path(args.control9).resolve(),
                         Path(args.control8).resolve(), Path(args.diagnosis).resolve())
    except replay_lock.Refused as refused:
        raise SystemExit(str(refused))
    out.write_text(json.dumps(result, indent=1) + '\n')
    print(json.dumps({'outcome': result['outcome'], 'consumed_and_validated': result['measurement']['consumed_and_validated'],
                      'reasons': result['outcome_reasons']}))


if __name__ == '__main__':
    main()
