#!/usr/bin/env python3
"""R6-013 auditor over the cohort v6 canned runs on the census sites, with bounded historical checks of cohorts v4 and v5. Non-locked;
read-only.

Built from the R6-009 auditor (`reviews/2026-09-14/cohort_audit.py`, retained unchanged for revisions v1-v3) through the R6-013 draft
(`cohort_v5_audit.py`, retained unchanged as the reviewed draft). Every relationship the R6-009 auditor checks is carried forward by name
where it still applies; `CARRIED_FORWARD` states where each is checked now or why it has no instance. On top, for the sites:

* site identity, the original context, and the recorded renaming, bound to the frozen telescope (per run);
* eligibility recomputed over all fifteen sites from the retained classification; the run population derived from it and from the
  predeclared closer-reachability stratum (`RECONSTRUCTION_STRATUM`, fixed by the R6-013 outcome decision from the v5 record), never
  from the v6 outcomes;
* stages kept separate, each its own case: request admission and arithmetic feasibility; the generated witness's verification
  (`certificate:verified_and_bound`); reconstruction attempted, preparation/reconstruction IR equality and the selected closer
  (`reconstruction:*`); successful consumption, by the closer's own receipt (`proof:certificate_consumed`); and local and
  containing-declaration validation (`proof:original_declarations_validated`). A refused reconstruction is audited for integrity
  (`reconstruction:refusal_diagnosed`, `reconstruction:no_completion_evidence`); an accepted audit of it is not a proof success;
* revision-specific bindings: the supersession of v5, the runtime pin and its divergence, the pricing capture and its narrow review,
  the campaign ledger, the publication scan version, and the site harness lock with the revision 2 overlay;
* history_v4 and history_v5: the retained populations, seals and chains, ledgers, and what each recorded. v5's l096/l099 are
  qualified kernel successes without a consumption receipt; no receipt is synthesized or read into them. The v4 guard failures are
  checked for IR equality in v6 independently of any later success.

The case population is derived before any run is read; the audit fails unless exactly that set of named cases was evaluated.
"""
import argparse
import copy
import difflib
import gzip
import hashlib
import inspect
import json
from fractions import Fraction
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import campaign_ledger as base
import campaign_network as network
import cohort_budget as budget
import cohort_contract as contract
import cohort_episode as driver
import cohort_ledger as ledger
import credential
import credential_episode as publication_driver
import envelope_proof_audit
import episode
import events
import payload
import priced_payload_v2 as v2
import pricing_gate_v2 as gate2
import pricing_gate_v4 as gate
import provider_payload
import publication
import run as r6
import consumption_overlay
import site_network
import site_representability as rep
import site_request
import site_task

REVISION = 'farkas_cohort_v6'
RUNS = 'cohort-runs-v6'
POLICY, LOCK = 'farkas-cohort-v6.json', 'cohort-harness-v6.sha256.json'
CONTRACT_PATH = 'contracts/farkas-proposal-contract-v2.json'
SITE_LOCK = 'site-harness-v4.sha256.json'
REPRESENTABILITY = 'census-runs/representability-v4'
PRICING_CAPTURE = 'sources/pricing-approved-campaign-3'
RULES = {'task_join': True, 'grant_domain': 'r6-campaign-send-grant-2'}
KIND_OF_CLASS = {'posable_certificate': 'proof', 'posable_negative_control': 'negative', 'interface_refused': 'interface_refused'}
RELEASE_RUN = ('l096-draw2-format', 'bracket-l096', 2)  # the declared credential-format release: one reservation, no transmission
# The fixed closer-reachability stratum (R6-013 outcome decision, from the v5 record): certificate sites whose goal the pinned ℕ
# closer refuses. Declared before v6 ran; a v6 outcome that differs is a rejection, not a reclassification.
RECONSTRUCTION_STRATUM = {'bracket-l166': 'nat_closer_int_goal', 'bracket-l175': 'nat_closer_int_goal',
                          'bracket-l178': 'nat_closer_int_goal', 'bracket-l204': 'nat_closer_int_goal'}
CONSUMING_CLOSERS = ('term_mode_nat', 'term_mode_int')  # the core closers whose receipts the revision 2 overlay states from the implementation
SENT = ('proof', 'negative', 'reconstruction_refused')
TERMINAL_KIND = {'proof': 'send_grant', 'negative': 'send_grant', 'reconstruction_refused': 'send_grant', 'release': 'release'}
FAILURE_CATEGORY = {'proof': None, 'negative': 'certificate_verification', 'reconstruction_refused': 'reconstruction_refused',
                    'release': 'credential_format', 'interface_refused': 'interface_refused'}
ALLOWANCE = {'proof': 1, 'negative': 1, 'reconstruction_refused': 1, 'release': 0, 'interface_refused': None}
FAILING_STAGE = {'negative': 'certificate-check', 'interface_refused': 'pipeline-prepare', 'reconstruction_refused': 'reconstruct'}  # the one stage whose non-zero exit is the outcome
GUARD = 'R6 proposal input differs from freshly reified goal/context'
SMT_SIMPLE = __import__('re').compile(r'[A-Za-z~!@$%^&*_\-+=<>.?/][A-Za-z0-9~!@$%^&*_\-+=<>.?/]*')

MODULE_MOUNTS = {'/adapter.py': 'cohort_https.py', '/cohort_ledger.py': 'cohort_ledger.py', '/campaign_ledger.py': 'campaign_ledger.py',
                 '/pricing_gate_v4.py': 'pricing_gate_v4.py', '/pricing_gate_v2.py': 'pricing_gate_v2.py', '/live_https.py': 'live_https.py'}
RESERVATION_STATUS = 'byte_ceiling_plus_framing_assumption'
COHORT_MODULES = ('cohort_budget', 'cohort_contract', 'cohort_ledger', 'cohort_episode', 'cohort_https', 'pricing_gate_v4', 'site_network')
MODULES = {'cohort_budget': ('cohort-harness', budget), 'cohort_contract': ('cohort-harness', contract), 'cohort_ledger': ('cohort-harness', ledger),
           'cohort_episode': ('cohort-harness', driver), 'cohort_https': ('cohort-harness', None), 'pricing_gate_v4': ('cohort-harness', gate),
           'site_network': ('cohort-harness', site_network),
           'site_task': ('site-harness', site_task), 'site_request': ('site-harness', site_request), 'site_representability': ('site-harness', rep),
           'site_stage': ('site-harness', None), 'site_supervise': ('site-harness', None), 'site_differential': ('site-harness', None),
           'consumption_overlay': ('site-harness', consumption_overlay),
           'campaign_ledger': ('campaign-harness', base), 'campaign_network': ('campaign-harness', None), 'campaign_budget': ('campaign-harness', None),
           'campaign_contract': ('campaign-harness', None), 'campaign_episode': ('campaign-harness', None), 'campaign_https': ('campaign-harness', None),
           'credential': ('credential-harness', credential), 'publication': ('credential-harness', publication),
           'credential_episode': ('credential-harness', publication_driver), 'envelope_proof_audit': ('envelope-harness', envelope_proof_audit),
           'episode': ('harness', episode), 'events': ('harness', events), 'payload': ('harness', payload), 'run': ('harness', r6), 'admission': ('harness', None),
           'priced_payload_v2': ('priced-v2-harness', v2), 'pricing_gate_v2': ('priced-v2-harness', gate2),
           'provider_payload': ('provider-harness', provider_payload), 'provider_episode': ('provider-harness', None),
           'live_https': ('live-harness', None), 'live_tls_fixture': ('live-harness', None)}
COMMITMENT_DOMAIN = 'r6-campaign-credential-commitment-1'
RUNTIME_PIN = 'cohort-runtime-v1'

STARTED = [('supervisor', 'episode', 'episode_started')] + [('supervisor', st, e) for st in ('preparation-build', 'preparation', 'pipeline-prepare')
                                                             for e in ('stage_started', 'stage_finished')]
PREPARED = STARTED + [('supervisor', 'payload', 'prepared_problem'), ('supervisor', 'live-payload', 'payload_validated'),
                      ('supervisor', 'proposal', 'recovery_started'), ('supervisor', 'campaign-ledger', 'reservation_attempted')]
PREFIX = PREPARED + [('supervisor', 'pricing-admission', 'pricing_admitted'), ('supervisor', 'campaign-ledger', 'request_reserved'),
                     ('supervisor', 'proposal-1', 'stage_started'), ('supervisor', 'proposal-1', 'stage_finished'),
                     ('supervisor', 'campaign-ledger', 'reservation_reconciled')]
OBSERVED = [('supervisor', 'proposal', 'https_observed'), ('supervisor', 'proposal', 'transport_validated')]
RECEIPT = [('supervisor', 'credential-receipt', 'credential_receipt_checked')]
RECONSTRUCTED = ('reification_started', 'reification_finished', 'dispatch_started', 'dispatch_received', 'certificate_verification_started',
                 'certificate_verification_finished', 'reconstruction_started', 'closer_selected')
CHILDREN = [('child_report', 'reconstruct', e) for e in (*RECONSTRUCTED, 'residual_started', 'residual_finished', 'reconstruction_finished')]
CHECKED = [('supervisor', 'assembly', 'stage_started'), ('supervisor', 'assembly', 'stage_finished'),
           ('supervisor', 'assembly', 'certificate_assembled'), ('supervisor', 'certificate-check', 'stage_started'),
           ('supervisor', 'certificate-check', 'stage_finished'), ('supervisor', 'certificate-check', 'independent_certificate_verdict'),
           ('supervisor', 'proposal', 'recovery_finished')]
PROOF = CHECKED + [('supervisor', 'capture-build', 'stage_started'),
         ('supervisor', 'capture-build', 'stage_finished'), ('supervisor', 'reconstruct', 'stage_started'), *CHILDREN,
         ('supervisor', 'reconstruct', 'stage_finished'), ('supervisor', 'reconstruct', 'context_validated'),
         ('supervisor', 'export', 'stage_started'), ('supervisor', 'export', 'stage_finished'),
         ('supervisor', 'validation-local', 'stage_started'), ('supervisor', 'validation-local', 'stage_finished'),
         ('supervisor', 'validation-local', 'kernel_verdict'), ('supervisor', 'validation-whole', 'stage_started'),
         ('supervisor', 'validation-whole', 'stage_finished'), ('supervisor', 'validation-whole', 'kernel_verdict'),
         ('supervisor', 'episode', 'proof_validated'), ('supervisor', 'episode', 'episode_finished')]
REJECTED = [('supervisor', 'episode', 'episode_rejected')]
REFUSED = CHECKED + [('supervisor', 'capture-build', 'stage_started'), ('supervisor', 'capture-build', 'stage_finished'),
                     ('supervisor', 'reconstruct', 'stage_started'), *[('child_report', 'reconstruct', e) for e in RECONSTRUCTED],
                     ('supervisor', 'reconstruct', 'stage_finished'), ('supervisor', 'reconstruct', 'reconstruction_refused')] + REJECTED
PREPARATION_STAGES = ('preparation-build', 'preparation', 'pipeline-prepare')
STAGES = {'interface_refused': PREPARATION_STAGES, 'release': (*PREPARATION_STAGES, 'proposal-1'),
          'negative': (*PREPARATION_STAGES, 'proposal-1', 'assembly', 'certificate-check'),
          'reconstruction_refused': (*PREPARATION_STAGES, 'proposal-1', 'assembly', 'certificate-check', 'capture-build', 'reconstruct'),
          'proof': (*PREPARATION_STAGES, 'proposal-1', 'assembly', 'certificate-check', 'capture-build', 'reconstruct', 'export', 'validation-local', 'validation-whole')}
SENDER_PREFIX = ['bwrap', *network.NAMESPACES, '--unshare-net', '--die-with-parent', '--new-session', '--cap-drop', 'ALL',
                 '--clearenv', '--setenv', 'PATH', '/no-programs', '--setenv', 'LEAN_ABORT_ON_PANIC', '1',
                 '--symlink', 'usr/lib', '/lib', '--symlink', 'usr/lib64', '/lib64',
                 '--proc', '/proc', '--dev', '/dev', '--tmpfs', '/tmp', '--dir', '/work', '--chdir', '/work']
EPHEMERAL = ('/credential', '/ca.pem', '/server.pem', '/server.key')
SEQUENCES = {'proof': PREFIX+OBSERVED+RECEIPT+PROOF, 'negative': PREFIX+OBSERVED+RECEIPT+CHECKED+REJECTED,
             'reconstruction_refused': PREFIX+OBSERVED+RECEIPT+REFUSED,
             'release': PREFIX+OBSERVED+RECEIPT+REJECTED,
             'interface_refused': STARTED+[('supervisor', 'request-admission', 'interface_refused')]+RECEIPT+REJECTED}

# The bounded historical check of cohort v4 (R6-012): its exact population and what each run recorded.
HISTORY_V4 = {'runs': 'cohort-runs-v4', 'policy': 'farkas-cohort-v4.json', 'lock': 'cohort-harness-v4.sha256.json', 'name': 'farkas_cohort_v4',
              'representability': 'census-runs/representability-v2',
              'expected': {**{f'l{n}-draw1': ('proof', f'bracket-l{n}') for n in ('069', '070', '071', '078')},
                           **{f'l{n}-draw1': ('reconstruction_guard', f'bracket-l{n}') for n in ('096', '099', '166', '175', '204')},
                           'l170-draw1': ('negative', 'bracket-l170'), 'l098-draw1': ('interface_refused', 'bracket-l098'),
                           'l178-draw1': ('policy_refused', 'bracket-l178'), 'l096-draw2-format': ('release', 'bracket-l096')}}
HISTORY_V5 = {'runs': 'cohort-runs-v5', 'policy': 'farkas-cohort-v5.json', 'lock': 'cohort-harness-v5.sha256.json', 'name': 'farkas_cohort_v5',
              'representability': 'census-runs/representability-v3',
              'expected': {**{f'l{n}-draw1': ('proof', f'bracket-l{n}') for n in ('069', '070', '071', '078')},
                           **{f'l{n}-draw1': ('kernel_success_unreceipted', f'bracket-l{n}') for n in ('096', '099')},
                           **{f'l{n}-draw1': ('closer_refused_undiagnosed', f'bracket-l{n}') for n in ('166', '175', '178', '204')},
                           'l170-draw1': ('negative', 'bracket-l170'), 'l096-draw2-format': ('release', 'bracket-l096'),
                           **{f'l{n}-draw1': ('interface_refused', f'bracket-l{n}') for n in ('098', '101', '158', '180')}}}
# v4: the guard failures' preparation/reconstruction IR equality in v6 is its own case, independent of any later success.
HISTORY_CASES = ('history_v4:population_exact', 'history_v4:seals_and_chains', 'history_v4:verified_certificates',
                 'history_v4:reconstruction_errors', 'history_v4:ledger_dispositions', 'history_v4:preparation_ir_equal_in_v6',
                 'history_v4:later_outcomes_recorded_in_v6',
                 'history_v5:population_exact', 'history_v5:seals_and_chains', 'history_v5:qualified_kernel_successes',
                 'history_v5:closer_refusals_recorded', 'history_v5:ledger_dispositions')

# Each R6-009 case, and where it is checked now. Per-run cases keep their names; `None` marks a relationship with no instance here.
CARRIED_FORWARD = {
    'population:exactly_expected_runs': 'population:exactly_expected_runs (population derived from eligibility: population:derived_from_eligibility)',
    'tasks:manifests_bound': 'tasks:manifests_bound (and per run site:identity_bound)',
    'modules:bound_to_retained_copies': 'modules:bound_to_retained_copies (site harness modules added)',
    'modules:cohort_revision': 'modules:cohort_revision',
    'campaign:single_identity': 'campaign:single_identity',
    'revisions:chained_distinct_policies_same_lock': 'revision:superseded_v5_bound (one revision; its predecessor is the superseded v5 policy and lock, itself superseding v4)',
    'input:identical_model_bytes_across_revisions:<task>': 'input:identical_model_bytes_across_draws:bracket-l096 (one revision; the same site across draws)',
    'input:distinct_model_bytes_across_tasks': 'input:distinct_model_bytes_across_tasks (eleven sites)',
    'receipts:distinct_across_runs': 'receipts:distinct_across_runs',
    'ledger:continuous_across_revisions': 'ledger:continuous_single_revision',
    'ledger:consumed_slots_persist': 'ledger:slots_match_population',
    'ledger:refusals_bound_to_earlier_consumption': None,  # no slot-consumed refusal in a single-revision checkpoint;
    # pre-reservation refusals are checked instead by ledger:no_rows_for_prereservation_refusals and <run>:interface:refused_before_reservation
    '<run>:refusal:slot_consumed_before_reservation': '<run>:interface:refused_before_reservation (the refusal kind here)',
    '<run>:proof:export_expected': '<run>:proof:export_recorded (no canned export digest exists for a site; the export is bound to its stage and the verdict)',
    '<run>:proof:certificate_bound': '<run>:certificate:verified_and_bound (also for reconstruction_refused runs: validity is separate from consumption)',
    '<run>:proof:shared_checker': '<run>:proof:shared_checker (the frozen R6-001 checks with the closer read from its own receipt)',
    '<run>:* (all other per-run cases)': 'the same name, for every kind to which it applies',
}


class Rejection(AssertionError):
    def __init__(self, case, detail=''):
        super().__init__(case+(': '+detail if detail else '')); self.case = case


class Audit:
    def __init__(self): self.cases = {}
    def require(self, ok, case, detail=''):
        if case in self.cases: raise Rejection(case, 'duplicate case name')
        self.cases[case] = bool(ok)
        if not ok: raise Rejection(case, detail)


def sha(data): return hashlib.sha256(data).hexdigest()
def load(path): return json.loads(Path(path).read_bytes())
def canonical(value): return events.canonical(value)
def run_name(site_id, draw=1): return site_id.removeprefix('bracket-')+f'-draw{draw}'


def derive_population(classes):
    """The run population from the classification: one draw-1 run per site in a class with a declared run kind, plus the declared
    release. A non-empty class without a run kind is an error, not an omission."""
    expected = {}
    for cls, sites in classes.items():
        if sites and cls not in KIND_OF_CLASS: raise ValueError(f'class {cls} has sites but no declared run kind: {sites}')
        for s in sites:
            kind = KIND_OF_CLASS[cls]
            if s in RECONSTRUCTION_STRATUM:
                if kind != 'proof': raise ValueError(f'{s}: the reconstruction stratum names a site that is not certificate-feasible')
                kind = 'reconstruction_refused'
            expected[run_name(s)] = (kind, s, 1, 1)
    if not all(any(t == s for (_, t, _, _) in expected.values()) for s in RECONSTRUCTION_STRATUM): raise ValueError('stratum names a site outside the population')
    name, site, draw = RELEASE_RUN
    if expected.get(run_name(site), ('',))[0] != 'proof': raise ValueError('the release site is not a posable certificate site')
    expected[name] = ('release', site, draw, 1)
    return expected


def expected_cases(expected):
    """The complete named population: the audit must evaluate exactly these."""
    names = ['eligibility:recomputed_fifteen_sites', 'population:derived_from_eligibility', 'population:exactly_expected_runs',
             'revision:superseded_v5_bound', 'revision:runtime_pricing_ledger_publication_bound',
             'tasks:manifests_bound', 'modules:bound_to_retained_copies', 'modules:cohort_revision', 'campaign:single_identity',
             f'input:identical_model_bytes_across_draws:{RELEASE_RUN[1]}', 'input:distinct_model_bytes_across_tasks', 'receipts:distinct_across_runs',
             'ledger:continuous_single_revision', 'ledger:slots_match_population', 'ledger:no_rows_for_prereservation_refusals', *HISTORY_CASES]
    for run, (kind, task, draw, revision) in expected.items():
        names += [f'{run}:versions:policy_lock_contract_campaign_bound', f'{run}:chain:valid', f'{run}:chain:expected_sequence',
                  f'{run}:site:identity_bound', f'{run}:site:prepared_equals_classification', f'{run}:site:preparation_is_the_repaired_helper',
                  f'{run}:site:original_context_bound', f'{run}:site:renaming_recorded',
                  f'{run}:seal:retained_hashes', f'{run}:publication:recomputed', f'{run}:terminal:commitments_bound',
                  f'{run}:summary:bound_to_audited_records', f'{run}:seal:chain_and_outcome', f'{run}:accounting:recomputed', f'{run}:credential_receipt:recorded',
                  f'{run}:receipts:payloads_bound_to_records', f'{run}:stages:every_stage_on_the_path_returned']
        if kind == 'interface_refused':
            names += [f'{run}:interface:refused_before_reservation']; continue
        names += [f'{run}:request:regenerated_under_contract', f'{run}:envelope:recomputed_from_contract', f'{run}:pricing:host_admission_rederived',
                  f'{run}:ledger:permit_and_reconciliation_bound', f'{run}:ledger:reservation_priced_from_contract_limits', f'{run}:ledger:disposition_derived',
                  f'{run}:slot:authoritative_matches_retained', f'{run}:mounts:authority_bound', f'{run}:command:reconstructed_from_pinned_runtime_and_layout',
                  f'{run}:receipts:single_pair_bound_to_process',
                  f'{run}:receipts:stage_returned_within_frozen_limits', f'{run}:grant:consistent_with_outcome',
                  f'{run}:pricing:actor_check_rederived', f'{run}:transport:record_consistent', f'{run}:transport:bodies_are_the_contract_rendering',
                  f'{run}:interpretation:reproduced', f'{run}:commitment:bound_to_mounted_canary', f'{run}:slot:identity_in_receipts_not_in_model_bytes']
        if kind in SENT:
            names += [f'{run}:transport:local_send_and_remote_receipt', f'{run}:grant:ordered_before_first_header_byte',
                      f'{run}:{kind}:response_bound', f'{run}:{kind}:attribution_passed_through']
        if kind in ('proof', 'reconstruction_refused'):
            names += [f'{run}:certificate:verified_and_bound', f'{run}:reconstruction:preparation_ir_equal', f'{run}:reconstruction:closer_selected']
        if kind == 'proof':
            names += [f'{run}:proof:certificate_consumed', f'{run}:proof:shared_checker', f'{run}:proof:original_declarations_validated', f'{run}:proof:export_recorded']
        elif kind == 'reconstruction_refused':
            names += [f'{run}:reconstruction:refusal_diagnosed', f'{run}:reconstruction:no_completion_evidence']
        elif kind == 'negative':
            names += [f'{run}:negative:witness_is_the_canned_non_certificate', f'{run}:negative:verifier_rejected_and_stopped']
        else:
            names += [f'{run}:failure:classified_and_finalized']
    if len(names) != len(set(names)): raise ValueError('duplicate expected case name')
    return tuple(names)


# ---------------------------------------------------------------------------------------------------------------- eligibility

RECOMPUTED_KEYS = ('class', 'fragment', 'row_count', 'row_names', 'neg_goal_rows', 'variables', 'farkas_omissions', 'names_unique', 'duplicate_names',
                   'frozen_policy_class', 'arithmetic_certificate', 'certificate_rows', 'certificate', 'feasible_point', 'policy_c')


def eligibility(a, representability):
    """All fifteen sites, from the classification's retained bytes: each site's class recomputed with the exact arithmetic and policy C over
    its retained prepared problem (or the SDK's recorded refusal), equal to its own record and the summary; the posable set equals the
    policy's confirmation, recomputed through gate v4, and the frozen POSABLE."""
    problems = []
    try:
        summary = load(representability/'representability.json'); primary = list(site_task.primary())
        if summary['population'] != primary or len(primary) != 15: problems.append('population is not the fifteen reviewed sites')
        recomputed = {c: [] for c in rep.CLASSES}
        for site_id in primary:
            run = representability/site_id; record = load(run/'representability.json')
            sealed = load(run/'seal.json'); rows = events.read(run/'events.ndjson')
            if not (sealed['event_count'] == len(rows) and sealed['last_event_hash'] == rows[-1]['event_hash']
                    and all((run/k).is_file() and sha((run/k).read_bytes()) == v for k, v in sealed['retained_sha256'].items())):
                problems.append(f'{site_id}: classification run seal')
            if not (run/'prepared.json').exists():
                failure = rep.failure_record(run)
                cls = 'interface_refused' if failure['stage'] == 'pipeline-prepare' and failure.get('stderr_head', '').startswith('Failure(') else 'preparation_failed'
                if record['class'] != cls: problems.append(f'{site_id}: recorded {record["class"]}, recomputed {cls}')
            else:
                prepared = load(run/'prepared.json'); reified = load(run/'stages/preparation/output/reification.json')
                if prepared['input_ir'] != reified['ir'] or load(run/'input-ir.json') != reified['ir']: problems.append(f'{site_id}: prepared input IR is not the reified IR')
                fresh = rep.classify(prepared, reified); cls = fresh['class']
                differing = [k for k in RECOMPUTED_KEYS if fresh.get(k) != record.get(k)]
                if differing: problems.append(f'{site_id}: recomputation differs in {differing}')
                if fresh['arithmetic_certificate']:
                    if not rep.check_indexed(prepared['rows'], {r['index']: int(r['coefficient']) for r in fresh['certificate_rows']}): problems.append(f'{site_id}: certificate')
                elif not rep.check_point(prepared['rows'], {k: Fraction(v) for k, v in fresh['feasible_point'].items()}): problems.append(f'{site_id}: feasible point')
            recomputed[cls].append(site_id)
        if summary['classes'] != recomputed: problems.append(f'summary classes differ: {summary["classes"]} vs {recomputed}')
        confirmation = contract.confirm_posable(); policy = load(ROOT/'policies'/POLICY)
        posable = sorted(recomputed['posable_certificate']+recomputed['posable_negative_control'])
        if not (policy['posable_confirmation'] == confirmation and confirmation['representability_sha256'] == sha((representability/'representability.json').read_bytes())
                and sorted(s for s, o in confirmation['outcome'].items() if o['posable']) == posable == sorted(contract.POSABLE)
                and sorted(s for s, o in confirmation['outcome'].items() if o['code'] == 'interface_refused') == sorted(recomputed['interface_refused'])
                and confirmation['denominator'] == 15 and policy['campaign']['schedule'] == {s: contract.DRAWS for s in contract.POSABLE}):
            problems.append('policy confirmation or POSABLE differs from the recomputed eligibility')
    except (ValueError, KeyError, OSError, site_request.Refusal, gate.Failure) as error:
        problems.append(type(error).__name__+': '+str(error)[:300])
    a.require(not problems, 'eligibility:recomputed_fifteen_sites', '; '.join(problems))
    return recomputed


# ---------------------------------------------------------------------------------------------------------------- revision bindings

def revision_bindings(a, root, expected, policy):
    """The revision's own supersession, runtime, pricing, ledger and publication, each bound to the bytes it names."""
    v4_policy = ROOT/'policies'/HISTORY_V4['policy']; v5_policy = ROOT/'policies'/HISTORY_V5['policy']; v5_lock = ROOT/'policies'/HISTORY_V5['lock']
    earlier = load(v5_policy)
    same_science = all(policy[k] == earlier[k] for k in ('contract_sha256', 'pricing', 'pricing_admission', 'pricing_sources', 'limits', 'request', 'model',
                                                        'runtime_lock_sha256', 'runtime_divergence', 'publication', 'attribution')) \
                   and policy['campaign']['schedule'] == earlier['campaign']['schedule'] \
                   and {k: v for k, v in policy['posable_confirmation'].items() if k != 'representability_sha256'} \
                       == {k: v for k, v in earlier['posable_confirmation'].items() if k != 'representability_sha256'}  # same outcome, confirmed from its own classification
    a.require(policy['name'] == REVISION == contract.NAME and policy['revision'] == 1 and policy['revision_reason'] is None
              and policy['supersedes'] == {'cohort_policy_sha256': sha(v5_policy.read_bytes()), 'cohort_lock_sha256': sha(v5_lock.read_bytes()),
                                           'reason': 'v5 recorded no consumption receipt on the core Int closer and no closer selection (R6-013 outcome decision); site harness v4 adds closer-specific observations',
                                           'contract_sha256': sha((ROOT/'contracts/farkas-proposal-contract-v1.json').read_bytes())}
              and earlier['supersedes']['cohort_policy_sha256'] == sha(v4_policy.read_bytes())
              and len({policy['campaign']['id'], earlier['campaign']['id'], load(v4_policy)['campaign']['id']}) == 3 and same_science
              and policy['site_lock_sha256'] == sha((ROOT/'policies'/SITE_LOCK).read_bytes()) != earlier['site_lock_sha256'],
              'revision:superseded_v5_bound')
    problems = []
    pin = ROOT/'policies'/(RUNTIME_PIN+'.json')
    if not (policy['runtime_lock_sha256'] == sha(pin.read_bytes()) and policy['runtime_divergence'] == contract.runtime_divergence()):
        problems.append('runtime pin or its recorded divergence')
    capture = ROOT/PRICING_CAPTURE
    try: review = contract.pinned_admission(capture)
    except ValueError as error: review = None; problems.append('pricing review: '+str(error))
    if review is not None and not (policy['pricing_sources'] == PRICING_CAPTURE and policy['pricing_admission'] == review
                                   and review['source_review']['differing_extract_fields'] == {'caching': [], 'model': ['snapshot_section']}
                                   and policy['pricing_gate_sha256'] == sha((ROOT/'pricing_gate_v4.py').read_bytes())):
        problems.append('pricing capture, admission review or gate')
    campaign = policy['campaign']['id']; ledgers = sorted(p.name for p in (ROOT/'ledgers/campaigns'/campaign).iterdir()) if (ROOT/'ledgers/campaigns'/campaign).is_dir() else None
    if ledgers != ['rehearsal']: problems.append(f'campaign ledger directory {ledgers}')
    site_lock = load(ROOT/'policies'/SITE_LOCK)
    if not (site_lock.get('consumption_overlay.py') == sha((ROOT/'consumption_overlay.py').read_bytes()) and consumption_overlay.REVISION == 2):
        problems.append('site lock does not bind the revision 2 overlay')
    for name in expected:
        run = root/name; sp = load(run/'search-policy.json')
        if not ((run/'provenance/cohort-harness/policies'/(RUNTIME_PIN+'.json')).read_bytes() == pin.read_bytes()
                and load(run/'provenance/roles.json')['runtime_pin'] == RUNTIME_PIN):
            problems.append(f'{name}: retained runtime pin')
        origin = sorted(p.name for p in (run/'pricing-origin').iterdir()); approved = sorted(p.name for p in capture.iterdir())
        if origin != approved or any((run/'pricing-origin'/f).read_bytes() != (capture/f).read_bytes() for f in origin):
            problems.append(f'{name}: pricing origin is not the reviewed capture')
        if not (sp['ledger_path'] == f'ledgers/campaigns/{campaign}/rehearsal/ledger.ndjson' and sp['campaign_id'] == campaign):
            problems.append(f'{name}: ledger binding')
        sources_record, patch = consumption_overlay.source_record()
        if not (load(run/'provenance/sources.json') == sources_record and (run/'provenance/instrumentation.patch').read_text() == patch):
            problems.append(f'{name}: bridge sources are not the revision 2 overlay')
        scan = load(run/'publication-scan.json')
        if scan.get('schema_version') != policy['publication']['scan_version'] or policy['publication'] != load(v4_policy)['publication']:
            problems.append(f'{name}: publication scan version')
    a.require(not problems, 'revision:runtime_pricing_ledger_publication_bound', '; '.join(problems))


# ---------------------------------------------------------------------------------------------------------------- per run: identity

def retained(run):
    ph = run/'provenance/cohort-harness'
    policy_path = ph/'policies'/POLICY; lock_path = ph/'policies'/LOCK
    return ph, policy_path, lock_path, load(policy_path), load(lock_path)


def versions(a, run, name, kind, task, draw, revision, contract_value, contract_digest):
    sp = load(run/'search-policy.json'); ph, policy_path, lock_path, policy, lock = retained(run)
    retained_contract = load(ph/CONTRACT_PATH); files = tuple(lock)
    sources = {f: sha((ph/f).read_bytes()) for f in files}
    campaign = policy['campaign']['id']
    if kind == 'interface_refused': same_sources = not (run/'pricing-sources').exists()
    else:
        origin = sorted(p.name for p in (run/'pricing-origin').iterdir()); pinned = sorted(p.name for p in (run/'pricing-sources').iterdir())
        same_sources = origin == pinned and all((run/'pricing-origin'/f).read_bytes() == (run/'pricing-sources'/f).read_bytes() for f in origin)
    try: policy_ok = gate.check_policy(policy, contract_value) is None and gate.check_contract(retained_contract) == contract_digest
    except gate.Failure: policy_ok = False
    a.require(sp['config_sha256'] == sha(policy_path.read_bytes()) and sp['source_lock_sha256'] == sha(lock_path.read_bytes())
              and policy['source_lock_sha256'] == sha(lock_path.read_bytes())
              and policy_path.read_bytes() == (ROOT/'policies'/POLICY).read_bytes() and lock_path.read_bytes() == (ROOT/'policies'/LOCK).read_bytes()
              and sorted(lock) == sorted(contract.FILES) and all(lock[f] == sources[f] for f in files)
              and sp['name'] == policy['name'] == REVISION and sp['mode'] == 'rehearsal' and sp['task_id'] == task.id and sp['draw'] == draw
              and sp['revision'] == policy['revision'] == revision and sp['campaign_id'] == campaign
              and sp['contract_sha256'] == policy['contract_sha256'] == contract_digest == sha(canonical(retained_contract)+b'\n')
              and retained_contract == contract_value and sp['manifest_sha256'] == sha((task.path/'manifest.json').read_bytes())
              and policy['live_enabled'] is False and policy['authorization'] is None and policy['prompt_sha256'] == contract_value['instruction']['sha256']
              and policy_path.read_bytes() == canonical(policy)+b'\n' and policy['campaign']['rehearsal_authorization'] == contract.REHEARSAL_AUTHORIZATION
              and sp['ledger_path'] == f'ledgers/campaigns/{campaign}/rehearsal/ledger.ndjson' and sp['ledger_slots'] == f'ledgers/campaigns/{campaign}/rehearsal/slots'
              and policy_ok and same_sources and policy['pricing_gate_sha256'] == sha((ph/'pricing_gate_v4.py').read_bytes())
              and (kind == 'interface_refused' or ((run/'transport-policy.json').read_bytes() == policy_path.read_bytes()
                                                   and (run/'transport-contract.json').read_bytes() == canonical(retained_contract)+b'\n'
                                                   and sha((run/'transport-instruction.txt').read_bytes()) == contract_value['instruction']['sha256'])),
              f'{name}:versions:policy_lock_contract_campaign_bound')
    return sp, policy


def modules(a, root, names):
    """Every module the runs used equals its retained copy in every run; the cohort revision is the current one."""
    def same(run, m, folder):
        p = run/'provenance'/folder/(m+'.py'); source = ROOT/(m+'.py')
        return p.is_file() and source.is_file() and sha(source.read_bytes()) == sha(p.read_bytes())
    for m, (folder, module) in MODULES.items():
        if module is not None and Path(module.__file__).resolve() != (ROOT/(m+'.py')).resolve(): a.require(False, 'modules:bound_to_retained_copies', 'imported '+m+' from elsewhere')
    differing = [f'{n}/{m}' for n in names for m, (folder, _) in MODULES.items() if not same(root/n, m, folder)]
    a.require(not differing, 'modules:bound_to_retained_copies', 'modules differ from the retained copies: '+', '.join(differing))
    a.require(contract.NAME == REVISION, 'modules:cohort_revision', 'current cohort revision is '+contract.NAME)
    return {'revision': REVISION, 'superseded': False}


def chain(a, run, name, kind, task):
    try: rows = events.read(run/'events.ndjson')
    except ValueError as error: a.require(False, f'{name}:chain:valid', str(error))
    a.require(all(r['task_id'] == task.id and r['run_id'] == rows[0]['run_id'] for r in rows), f'{name}:chain:valid')
    observed = [(r['source'], r['stage'], r['event']) for r in rows]
    a.require(observed == SEQUENCES[kind], f'{name}:chain:expected_sequence', f'{len(observed)} events')
    return rows


def site_identity(a, run, name, task, sp, policy):
    """The frozen site verifies; the site harness lock the policy names is retained in the run, and every locked site file equals it."""
    problems = []
    try: _, expected = site_task.frozen_site(task)
    except (ValueError, OSError, KeyError) as error: problems.append('frozen site: '+str(error)[:200]); expected = None
    decision = load(site_task.MEMBERSHIP_DECISION)
    retained_lock = run/'provenance/site-harness/policies'/SITE_LOCK
    lock = load(retained_lock) if retained_lock.is_file() else {}
    roles = load(run/'provenance/roles.json')
    if not (task.id in decision['primary'] and sp['manifest_sha256'] == decision['manifests_sha256'][task.id]): problems.append('membership')
    if not (retained_lock.is_file() and retained_lock.read_bytes() == (ROOT/'policies'/SITE_LOCK).read_bytes() and sha(retained_lock.read_bytes()) == policy['site_lock_sha256']
            and sorted(lock) == sorted(site_task.FILES) and all(sha((run/'provenance/site-harness'/f).read_bytes()) == h == sha((ROOT/f).read_bytes()) for f, h in lock.items())):
        problems.append('site harness lock or retained site sources')
    if not (roles['site_lock'] == str(ROOT/'policies'/SITE_LOCK) and roles['site_supervisor'] == str(ROOT/'site_supervise.py')
            and roles['site_stage'] == str(ROOT/'site_stage.py') and roles['site_network'] == str(ROOT/'site_network.py')):
        problems.append('site roles')
    if expected is not None and load(run/'provenance/cohort-harness/policies'/POLICY)['site_lock_sha256'] != sha((ROOT/'policies'/SITE_LOCK).read_bytes()):
        problems.append('policy names another site lock')
    a.require(not problems, f'{name}:site:identity_bound', '; '.join(problems))
    return expected


def prepared_equals_classification(a, run, name, kind, task, representability):
    """This run's preparation reproduced the classification's, byte for byte: the input IR, and the prepared problem or the SDK's refusal."""
    retained_run = representability/task.id; problems = []
    if (run/'input-ir.json').read_bytes() != (retained_run/'input-ir.json').read_bytes(): problems.append('input IR')
    if (run/'stages/preparation/output/reification.json').read_bytes() != (retained_run/'stages/preparation/output/reification.json').read_bytes(): problems.append('reification')
    record = load(retained_run/'representability.json')
    if kind == 'interface_refused':
        if (run/'prepared.json').exists() or (retained_run/'prepared.json').exists() or record['class'] != 'interface_refused': problems.append('refusal class')
    else:
        if (run/'prepared.json').read_bytes() != (retained_run/'prepared.json').read_bytes(): problems.append('prepared problem')
        if record['class'] != {'proof': 'posable_certificate', 'reconstruction_refused': 'posable_certificate', 'negative': 'posable_negative_control',
                               'release': 'posable_certificate'}[kind]: problems.append('class')
    a.require(not problems, f'{name}:site:prepared_equals_classification', ', '.join(problems))
    return record


def preparation_helper(a, run, name, task):
    """The preparation input is the repaired helper and the census instrumentation, exactly as `site_task.compile_input` writes them."""
    root = run/'preparation-input'; source = site_task.instrumented(task, 'PreparationCapture', 'r6_prepare')
    helper = site_task.capture_source(task, True); pristine = site_task.census.pristine().decode()
    patch = ''.join(difflib.unified_diff(pristine.splitlines(True), source.splitlines(True), fromfile='Pristine.lean', tofile='Frozen.lean'))
    a.require(sorted(p.name for p in root.iterdir()) == ['Frozen.lean', 'PreparationCapture.lean', 'source.patch']
              and (root/'Frozen.lean').read_text() == source and (root/'PreparationCapture.lean').read_text() == helper
              and (root/'source.patch').read_text() == patch and 'renameLocalsForSmt g' in helper and 'ir.userDirectives.getD' in helper,
              f'{name}:site:preparation_is_the_repaired_helper')


def original_context(a, run, name, kind, task):
    """Preparation captured the frozen local context itself; the sanitized projection and the payload audit are recomputed from it."""
    frozen_path = task.path/'context/local-context.json'; context = load(run/'stages/preparation/output/context.json')
    reified = load(run/'stages/preparation/output/reification.json'); ok = context == load(frozen_path)
    if ok and kind != 'interface_refused':
        projection = payload.project_context(context); audit_record = load(run/'payload-audit.json'); prepared = load(run/'prepared.json')
        ok = (load(run/'sanitized-context.json') == projection and audit_record == {
            'sanitized_context_sha256': sha((run/'sanitized-context.json').read_bytes()), 'source_context_sha256': sha(frozen_path.read_bytes()),
            'context_projection_is_model_visible': False, 'context_policy': 'farkas_rows_only_v1',
            'let_facts_preserved': [r['name'] for r in context['telescope'] if r['kind'] == 'let'],
            'reifier_omissions': reified['skipped_locals'], 'farkas_omissions': prepared['farkas_omissions']})
    a.require(ok, f'{name}:site:original_context_bound')


def renaming(a, run, name, task, record):
    """The renamed search context, bound to the frozen telescope by local index; only the renamer's cases differ; the IR names only search names."""
    reified = load(run/'stages/preparation/output/reification.json'); context = load(task.path/'context/local-context.json')
    entries = reified['search_context']; telescope = context['telescope']; problems = []
    if [e['index'] for e in entries] != list(range(1, len(telescope))): problems.append('indices do not cover the telescope')
    if not all(e['fvar_in_original'] is True and telescope[e['index']]['name'] == e['original_name'] for e in entries): problems.append('original names')
    search = [e['search_name'] for e in entries]
    if len(search) != len(set(search)) or not all(SMT_SIMPLE.fullmatch(n) for n in search): problems.append('search names not unique and SMT-simple')
    originals = [e['original_name'] for e in entries]
    for i, e in enumerate(entries):
        last = originals[i+1:].count(e['original_name']) == 0
        if last and SMT_SIMPLE.fullmatch(e['original_name']) and e['search_name'] != e['original_name'] and e['original_name'] not in search[:i]+search[i+1:]:
            problems.append(f"{e['original_name']} renamed without cause")
        if not last and e['search_name'] == e['original_name']: problems.append(f"earlier duplicate {e['original_name']} kept its name")
    renamed = [e for e in entries if e['original_name'] != e['search_name']]
    if renamed != record['search_context_renamed'] or len(entries) != record['search_context_entries']: problems.append('renamed set differs from the classification')
    ir = reified['ir']; names = [h['name'] for h in ir['context']['hypotheses']] + [v['name'] for v in ir['context']['free_vars']]
    if len(names) != len(set(names)) or not all(n in search or n.startswith('_pb_') for n in names): problems.append('IR names are not search names')
    a.require(not problems, f'{name}:site:renaming_recorded', '; '.join(problems))
    return renamed


# ---------------------------------------------------------------------------------------------------------------- per run: request, pricing, ledger

def request(a, run, name, kind, sp, task, contract_value, contract_digest):
    prepared = load(run/'prepared.json')
    try: regenerated, evidence = budget.request(task, prepared)
    except Exception as error: a.require(False, f'{name}:request:regenerated_under_contract', type(error).__name__+': '+str(error))
    request_bytes = (run/'live-request.json').read_bytes(); parsed = json.loads(request_bytes)
    try: gate.check_request_grammar(parsed); r6.jsonschema.validate(parsed, load(ROOT/contract.REQUEST_SCHEMA_PATH)); grammar = True
    except (gate.Failure, r6.jsonschema.ValidationError): grammar = False
    a.require(regenerated == request_bytes and 'policy_sha256' not in parsed and grammar and load(run/'policy-c-evidence.json') == evidence
              and parsed['contract_sha256'] == contract_digest and parsed['binding']['task_id'] == task.id and parsed['binding']['manifest_sha256'] == sp['manifest_sha256']
              and parsed['binding']['input_ir_sha256'] == events.digest(prepared['input_ir']) and parsed['binding']['final_ir_sha256'] == events.digest(prepared['final_ir'])
              and (run/'transport-request.json').read_bytes() == request_bytes, f'{name}:request:regenerated_under_contract')
    instruction = (run/'transport-instruction.txt').read_text()
    expected = gate.render_arguments(contract_value, instruction, request_bytes)
    try: envelope = gate.check_envelope(contract_value, instruction, expected, request_bytes)
    except gate.Failure as error: a.require(False, f'{name}:envelope:recomputed_from_contract', error.code)
    arguments = load(run/'live-arguments.json')
    a.require(gate.same_json(arguments, expected) and canonical(arguments) == canonical(expected) and gate.same_json(load(run/'transport-arguments.json'), expected)
              and load(run/'live-messages.json') == expected['input']
              and sha(instruction.encode()) == contract_value['instruction']['sha256'] == sha(contract.PROMPT.read_bytes()) and envelope['request_sha256'] == sha(request_bytes)
              and envelope['body_sha256'] == sha(gate2.entity_body(expected)), f'{name}:envelope:recomputed_from_contract')
    return request_bytes, expected, instruction, gate2.entity_body(expected), envelope


def host_admission(a, run, name, policy, contract_value, instruction, request_bytes, arguments):
    record = load(run/'host-pricing-admission.json')
    try: derived = gate.admission(policy, contract_value, instruction, run/'pricing-sources', arguments, request_bytes, record['evaluated_at_unix'])
    except gate.Failure as error: a.require(False, f'{name}:pricing:host_admission_rederived', error.code)
    a.require(record['accepted'] is True and derived == record and record['schema_version'] == 'r6-pricing-admission-3', f'{name}:pricing:host_admission_rederived')
    return record


def attempt_identity_bound(run, permit):
    value = permit.get('attempt_id'); receipts = [r['payload'].get('attempt_id') for r in events.read(run/'events.ndjson') if r['event'] == 'reservation_attempted']
    well_formed = isinstance(value, str) and len(value) == 64 and all(c in '0123456789abcdef' for c in value)
    return well_formed and receipts == [value]


def reconciliation_evidence(run, reconciliation):
    stage = run/'stages/proposal-1'; ev = reconciliation['evidence']
    markers = sorted(p.name for p in (stage/'grant').iterdir()) if (stage/'grant').is_dir() else []
    expected_markers = {'send_grant': ['send-grant.json'], 'release': ['release.json'], 'unknown': ['unknown.json']}[reconciliation['kind']]
    return (ev['process_sha256'] == sha((stage/'proposal-1.process.json').read_bytes())
            and ev['http_sha256'] == (sha((stage/'output/http.json').read_bytes()) if (stage/'output/http.json').exists() else None)
            and ev['grant_file_sha256'] == (sha((stage/'grant/send-grant.json').read_bytes()) if (stage/'grant/send-grant.json').exists() else None)
            and ev['launched'] is (stage/'command.json').exists() and markers == expected_markers and ev['record_read_failures'] == [])


def ledger_rows(a, run, name, kind, sp, task, draw, revision, request_bytes, policy, admission, contract_digest, frozen):
    permit = load(run/'campaign-permit.json'); reconciliation = load(run/'campaign-reconciliation.json'); campaign = sp['campaign_id']
    try:
        before = ledger.parse((run/'transport-ledger.ndjson').read_bytes()); after = ledger.parse((run/'ledger-after.ndjson').read_bytes())
        s_before = ledger.state(before, campaign); s_after = ledger.state(after, campaign)
    except ledger.Failure as error: a.require(False, f'{name}:ledger:permit_and_reconciliation_bound', error.code)
    reservation = load(run/'reservation.json')
    joined = permit['task_manifest_sha256'] == sha((task.path/'manifest.json').read_bytes()) and permit['challenge_sha256'] == frozen['challenge_sha256']
    consistent_termination = reconciliation['kind'] != 'release' or reconciliation['termination_established'] or reconciliation.get('reason') == 'pre_launch_failure'
    a.require(reconciliation_evidence(run, reconciliation) and before[-1] == permit and after[-1] == reconciliation and after[:len(before)] == before
              and permit['kind'] == 'reservation' and permit['episode_id'] == name and permit['task_id'] == task.id and permit['draw'] == draw
              and permit['policy_sha256'] == sp['config_sha256'] == s_before['policy_sha256'] and s_before['revision'] == revision-1
              and permit['contract_sha256'] == contract_digest == s_before['contract_sha256']
              and permit['request_sha256'] == sha(request_bytes) and permit['arguments_sha256'] == sha(canonical(load(run/'live-arguments.json')))
              and permit['pricing_admission'] == admission and permit['reserved_micro_usd'] == permit['reservation']['reserved_micro_usd'] <= policy['limits']['total_micro_usd']
              and joined and reconciliation['kind'] == TERMINAL_KIND[kind] and reconciliation['reservation_id'] == permit['reservation_id']
              and reconciliation['task_id'] == task.id and reconciliation['draw'] == draw and reconciliation['episode_id'] == name
              and reservation == {**permit['reservation'], 'reservation_id': permit['reservation_id'], 'request_sha256': permit['request_sha256'],
                                  'arguments_sha256': permit['arguments_sha256'], 'policy_sha256': permit['policy_sha256'],
                                  'pricing_admission_sha256': sha((run/'host-pricing-admission.json').read_bytes()),
                                  'ledger_row_hash': permit['row_hash'], 'ledger_sha256': sha((run/'transport-ledger.ndjson').read_bytes())}
              and before[0]['kind'] == 'activation' and before[0]['campaign_id'] == campaign and before[0]['purpose'] == 'rehearsal'
              and before[0]['authorization'] == policy['campaign']['rehearsal_authorization'] and s_before['schedule'] == contract.REHEARSAL_SCHEDULE
              and s_before['open_reservations'] == [permit['reservation_id']] and s_after['open_reservations'] == []
              and consistent_termination and attempt_identity_bound(run, permit),
              f'{name}:ledger:permit_and_reconciliation_bound')
    return permit, reconciliation


def reservation_priced(a, run, name, policy, permit, admission, envelope):
    limits = policy['limits']; rates = policy['pricing']['nano_usd_per_token']
    expected = {'reserved_micro_usd': gate.cost_micro(limits['input_tokens_reserved'], limits['output_tokens'], rates), 'message_utf8_bytes': envelope['message_utf8_bytes'],
                'input_tokens_reserved': limits['input_tokens_reserved'], 'output_tokens_reserved': limits['output_tokens'],
                'input_token_bound_status': RESERVATION_STATUS, 'billing_guarantee': False}
    reservation = load(run/'reservation.json'); check = load(run/'stages/proposal-1/output/pricing-check.json')
    a.require(permit['reservation'] == expected and permit['reserved_micro_usd'] == admission['reserved_micro_usd'] == check['reserved_micro_usd'] == expected['reserved_micro_usd']
              and admission['message_utf8_bytes'] == check['message_utf8_bytes'] == envelope['message_utf8_bytes'] <= limits['message_utf8_bytes']
              and admission['nano_usd_per_token'] == rates and all(reservation[k] == v for k, v in expected.items())
              and type(permit['reserved_micro_usd']) is int and expected['reserved_micro_usd'] > 0,
              f'{name}:ledger:reservation_priced_from_contract_limits', f"permit {permit['reserved_micro_usd']}, admission {admission['reserved_micro_usd']}, expected {expected['reserved_micro_usd']}")
    return expected['reserved_micro_usd']


def stage_records(run):
    stage = run/'stages/proposal-1'
    def record(path):
        if not path.exists(): return None
        try: value = json.loads(path.read_bytes())
        except (ValueError, OSError): return None
        return value if isinstance(value, dict) else None
    return record(stage/'proposal-1.process.json'), record(stage/'output/http.json'), (stage/'command.json').exists()


def read_grant(directory, permit):
    final = Path(directory)/ledger.GRANT_FILE
    if not final.exists(): return None
    try: record = json.loads(final.read_bytes())
    except (ValueError, OSError): raise ledger.Failure('campaign_grant_unreadable')
    if not (isinstance(record, dict) and record.get('domain') == RULES['grant_domain'] and record.get('reservation_id') == permit['reservation_id']
            and record.get('policy_sha256') == permit['policy_sha256'] and record.get('episode_id') == permit['episode_id']
            and record.get('request_sha256') == permit['request_sha256']): raise ledger.Failure('campaign_grant_binding')
    return record


def disposition(a, run, name, kind, permit, reconciliation, book):
    process, http, launched = stage_records(run); slot = book.grant_slot(permit)
    try: grant_state = 'present' if read_grant(slot, permit) is not None else 'absent'
    except ledger.Failure as error: grant_state = error.code
    terminated = ledger.termination_established(process)
    unsent = http is None or (http.get('body_sends_started') == 0 and http.get('header_sends_started') == 0)
    if grant_state == 'present': expected = 'send_grant'
    elif grant_state != 'absent': expected = 'unknown'
    elif not launched and process is None and http is None: expected = 'release'
    elif terminated and unsent: expected = 'release'
    else: expected = 'unknown'
    a.require(reconciliation['kind'] == expected == TERMINAL_KIND[kind] and reconciliation['termination_established'] is terminated and reconciliation['launched'] is launched,
              f'{name}:ledger:disposition_derived', f'derived {expected} (grant {grant_state}, terminated {terminated}, launched {launched}), recorded {reconciliation["kind"]}')


def slot_contents(a, run, name, permit, reconciliation, book):
    slot = book.grant_slot(permit); retained_dir = run/'stages/proposal-1/grant'
    files = sorted(p.name for p in slot.iterdir()) if slot.is_dir() else None
    expected = {'send_grant': ['send-grant.json'], 'release': ['release.json'], 'unknown': ['unknown.json']}[reconciliation['kind']]
    if reconciliation.get('torn_marker'): expected = sorted(set(expected+[reconciliation['torn_marker']]))
    same = files == expected and all((retained_dir/f).is_file() and (retained_dir/f).read_bytes() == (slot/f).read_bytes() for f in expected)
    if reconciliation['kind'] == 'send_grant':
        try: bound = read_grant(slot, permit) == reconciliation['grant']
        except ledger.Failure: bound = False
        bound = bound and reconciliation.get('marker_sha256') == sha((slot/ledger.GRANT_FILE).read_bytes())
    else:
        receipt_name = reconciliation['kind']+'.json'
        try: marker = load(slot/receipt_name) if same else None
        except ValueError: marker = None
        bound = same and isinstance(marker, dict) and marker.get('kind') == reconciliation['kind'] and marker.get('reservation_id') == permit['reservation_id'] \
                and isinstance(marker.get('reconciled_at_unix'), int) and reconciliation.get('marker_sha256') == sha((slot/receipt_name).read_bytes())
    a.require(same and bound and slot.parent == book.slot(permit['task_id'], permit['draw']), f'{name}:slot:authoritative_matches_retained',
              f'slot {files}, expected {expected}, bound {bound}')


def mounts(a, run, name, sp, task, draw, permit, book):
    command = load(run/'stages/proposal-1/command.json'); argv = command['argv']
    def source(guest, flag):
        hits = [i for i, x in enumerate(argv) if x == guest and i >= 2 and argv[i-2] == flag]
        return argv[hits[0]-1] if len(hits) == 1 else None
    def option(flag):
        hits = [i for i, x in enumerate(argv) if x == flag]
        return argv[hits[0]+1] if len(hits) == 1 and hits[0]+1 < len(argv) else None
    ledger_src, grant_src = source('/ledger.ndjson', '--ro-bind'), source('/grant', '--bind')
    root = ledger_src[:-len(sp['ledger_path'])] if ledger_src and ledger_src.endswith(sp['ledger_path']) else None
    run_dir = command['run']; roles = load(run/'provenance/roles.json')
    runtime = [i for i, x in enumerate(argv) if x == roles['runtime_path'] and i >= 1 and argv[i-1] == '--ro-bind']
    ok = (root is not None and grant_src == f"{root}{sp['ledger_slots']}/{task.id}/{draw}/{permit['reservation_id']}" and command['grant_slot'] == grant_src
          and Path(ledger_src).name == book.path.name and Path(grant_src).parent.parent.parent.name == book.slots.name
          and source('/policy.json', '--ro-bind') == run_dir+'/transport-policy.json' and source('/permit.json', '--ro-bind') == run_dir+'/campaign-permit.json'
          and source('/contract.json', '--ro-bind') == run_dir+'/transport-contract.json' and source('/instruction.txt', '--ro-bind') == run_dir+'/transport-instruction.txt'
          and source('/arguments.json', '--ro-bind') == run_dir+'/transport-arguments.json' and source('/request.json', '--ro-bind') == run_dir+'/transport-request.json'
          and source('/pricing-sources', '--ro-bind') == run_dir+'/transport-pricing-sources'
          and all(source(guest, '--ro-bind') == root+module for guest, module in MODULE_MOUNTS.items())
          and roles['actor_source'] == root+'cohort_https.py' and roles['ledger_module'] == root+'cohort_ledger.py' and roles['network_stage'] == root+'campaign_network.py'
          and roles['ledger_directory'] == root+'ledgers/campaigns' and roles['contract'] == root+CONTRACT_PATH
          and len(runtime) == 1 and roles['python'] in argv and command['records'] == run_dir+'/stages/proposal-1'
          and source('/out', '--bind') == command['records']+'/output' and source('/grant', '--ro-bind') is None and source('/ledger.ndjson', '--bind') is None
          and argv.count('--bind') == 2 and option('--task') == task.id and option('--draw') == str(draw) and option('--episode') == name
          and option('--contract') == '/contract.json' and option('--instruction') == '/instruction.txt' and option('--permit') == '/permit.json'
          and option('--ledger') == '/ledger.ndjson' and option('--grant') == '/grant' and option('--mode') == 'rehearsal')
    a.require(ok, f'{name}:mounts:authority_bound', f'ledger {ledger_src}, grant {grant_src}')
    return root


def command_reconstructed(a, run, name, sp, policy, task, draw, permit, http, root):
    command = load(run/'stages/proposal-1/command.json'); argv = command['argv']; run_dir = command['run']; roles = load(run/'provenance/roles.json')
    pin_path = run/'provenance/cohort-harness/policies'/(RUNTIME_PIN+'.json'); pin = load(pin_path)
    pinned = sha(pin_path.read_bytes()) == policy['runtime_lock_sha256'] and load(run/'provenance/python-runtime.json') == pin and roles['runtime_pin'] == RUNTIME_PIN \
             and load(run/'provenance/binaries.json').get(pin['python']) == pin['python_sha256'] and roles['python'] == pin['python']
    stdlib_source = f"{root}.cache/campaign-runtime/{policy['runtime_lock_sha256']}/stdlib"
    pinned = pinned and roles['runtime_path'] == stdlib_source
    libraries = [x for lib in sorted(pin['libraries'], key=lambda l: l['guest']) for x in ('--ro-bind', lib['host'], lib['guest'])]
    modules_ = [x for guest, module in (('/adapter.py', 'cohort_https.py'), ('/live_https.py', 'live_https.py'), ('/pricing_gate_v2.py', 'pricing_gate_v2.py'),
                                        ('/pricing_gate_v4.py', 'pricing_gate_v4.py'), ('/campaign_ledger.py', 'campaign_ledger.py'), ('/cohort_ledger.py', 'cohort_ledger.py'))
                for x in ('--ro-bind', root+module, guest)]
    records = [x for file, guest in (('transport-policy.json', '/policy.json'), ('transport-contract.json', '/contract.json'), ('transport-instruction.txt', '/instruction.txt'),
                                     ('transport-arguments.json', '/arguments.json'), ('transport-request.json', '/request.json'),
                                     ('transport-pricing-sources', '/pricing-sources'), ('campaign-permit.json', '/permit.json'))
               for x in ('--ro-bind', run_dir+'/'+file, guest)]
    def source(guest):
        hits = [i for i, x in enumerate(argv) if x == guest and i >= 2 and argv[i-2] == '--ro-bind']
        return argv[hits[0]-1] if len(hits) == 1 else None
    ephemeral = {guest: source(guest) for guest in EPHEMERAL}
    tls = [ephemeral[g] for g in ('/ca.pem', '/server.pem', '/server.key')]
    ephemeral_ok = (all(isinstance(v, str) and v.startswith('/') for v in ephemeral.values())
                    and all(Path(v).name == g[1:] for g, v in ephemeral.items() if g != '/credential')
                    and len({str(Path(v).parent) for v in tls}) == 1 and not any(v.startswith((root, run_dir)) for v in ephemeral.values()))
    expected = (SENDER_PREFIX + libraries + ['--ro-bind', stdlib_source, pin['stdlib']] + modules_ + records
                + ['--ro-bind', root+sp['ledger_path'], '/ledger.ndjson', '--ro-bind', run_dir+'/canned-provider.json', '/fixture.json']
                + [x for g in EPHEMERAL for x in ('--ro-bind', ephemeral[g] or '', g)]
                + ['--ro-bind', pin['python'], '/runner/bin/program', '--bind', run_dir+'/stages/proposal-1/output', '/out',
                   '--bind', f"{root}{sp['ledger_slots']}/{task.id}/{draw}/{permit['reservation_id']}", '/grant', '/runner/bin/program',
                   '-I', '-S', '-B', '/adapter.py', '--mode', 'rehearsal', '--policy', '/policy.json', '--contract', '/contract.json', '--instruction', '/instruction.txt',
                   '--arguments', '/arguments.json', '--credential-file', '/credential', '--ca', '/ca.pem', '--out', '/out', '--request', '/request.json',
                   '--sources', '/pricing-sources', '--permit', '/permit.json', '--ledger', '/ledger.ndjson', '--episode', name, '--task', task.id, '--draw', str(draw),
                   '--grant', '/grant', '--commitment-nonce', http['commitment_nonce'], '--fixture', '/fixture.json', '--server-cert', '/server.pem', '--server-key', '/server.key'])
    first = next((i for i, (x, y) in enumerate(zip(argv, expected)) if x != y), min(len(argv), len(expected)) if len(argv) != len(expected) else None)
    a.require(pinned and ephemeral_ok and argv == expected, f'{name}:command:reconstructed_from_pinned_runtime_and_layout',
              f'pinned {pinned}, ephemeral {ephemeral_ok}, first difference at {first}: {argv[first:first+3] if first is not None else None}')


def receipts(a, run, name, rows, policy):
    started = [r['payload'] for r in rows if r['stage'] == 'proposal-1' and r['event'] == 'stage_started']
    finished = [r['payload'] for r in rows if r['stage'] == 'proposal-1' and r['event'] == 'stage_finished']
    process = load(run/'stages/proposal-1/proposal-1.process.json'); command = load(run/'stages/proposal-1/command.json')
    a.require(len(started) == 1 and len(finished) == 1 and finished[0] == process and started[0]['command_file'] == 'stages/proposal-1/command.json'
              and command['network_namespace'] == 'unshared' and '--unshare-net' in command['argv'] and '/grant' in command['argv'],
              f'{name}:receipts:single_pair_bound_to_process')
    limits = policy['limits']
    a.require(process['exit_code'] == 0 and process['resource_exhausted'] is None and process['resource_violations'] == [] and process['monitor_error'] is None
              and process['observation_error'] is None and process['workload_empty_after_cleanup'] is True and process['accounting_scope'] == 'sandbox_process_tree'
              and command['wall_seconds'] == limits['request_wall_seconds'] and command['cpu_seconds'] == limits['request_cpu_seconds']
              and command['memory_bytes'] == limits['request_memory_bytes'] and command['output_bytes'] == limits['request_output_bytes']
              and command['capture_events'] is False and command['stage'] == 'proposal-1' and process['output_bytes'] <= command['output_bytes']
              and started[0]['wall_limit_seconds'] == command['wall_seconds'] and started[0]['cpu_limit_seconds'] == command['cpu_seconds']
              and started[0]['memory_limit_bytes'] == command['memory_bytes'],
              f'{name}:receipts:stage_returned_within_frozen_limits', f"exit {process['exit_code']}, limits {started[0]}")


def stage_outcomes(a, run, name, kind, policy):
    """Every stage on the kind's path returned under its limits, except the one stage whose rejection is the outcome, which exited
    non-zero on its own (no exhaustion, violation, monitor or observation failure, empty workload)."""
    present = sorted(p.name for p in (run/'stages').iterdir() if p.is_dir()) if (run/'stages').is_dir() else []
    defaults = {k: v.default for k, v in inspect.signature(episode.stage).parameters.items() if k in ('wall', 'cpu', 'memory', 'output_limit')}
    limits = policy['limits']; problems = []
    if present != sorted(STAGES[kind]): problems.append(f'stages {present}')
    for stage in STAGES[kind]:
        if stage not in present: continue
        process = load(run/'stages'/stage/(stage+'.process.json')); cmd = load(run/'stages'/stage/'command.json')
        clean = (process['resource_exhausted'] is None and process['resource_violations'] == [] and process['monitor_error'] is None
                 and process['observation_error'] is None and process['workload_empty_after_cleanup'] is True and process['accounting_scope'] == 'sandbox_process_tree'
                 and process['output_bytes'] <= cmd['output_bytes'] and cmd['stage'] == stage and cmd['records'] == cmd['run']+'/stages/'+stage)
        returned = clean and ((process['exit_code'] != 0) if FAILING_STAGE.get(kind) == stage else (process['exit_code'] == 0))
        if stage == 'proposal-1':
            bounded = (cmd['wall_seconds'], cmd['cpu_seconds'], cmd['memory_bytes'], cmd['output_bytes']) == \
                      (limits['request_wall_seconds'], limits['request_cpu_seconds'], limits['request_memory_bytes'], limits['request_output_bytes']) and cmd['capture_events'] is False
        else:
            bounded = (cmd['wall_seconds'], cmd['cpu_seconds'], cmd['memory_bytes'], cmd['output_bytes']) == \
                      (defaults['wall'], defaults['cpu'], defaults['memory'], defaults['output_limit']) and cmd['capture_events'] is (stage == 'reconstruct')
        if not (returned and bounded): problems.append(f"{stage} exit {process['exit_code']} returned {returned} bounded {bounded}")
    a.require(not problems, f'{name}:stages:every_stage_on_the_path_returned', '; '.join(problems))


def payload_receipts(a, run, name, kind, rows, sp, task, permit, reconciliation, http, admission, frozen):
    nonce = load(run/'credential-canary.json')['nonce']; problems = []
    def expect(stage, event, value, drop=()):
        hits = [r['payload'] for r in rows if r['source'] == 'supervisor' and r['stage'] == stage and r['event'] == event]
        got = [{k: v for k, v in h.items() if k not in drop} for h in hits]
        if got != [value]: problems.append(f'{stage}/{event}')
    for stage in sorted(p.name for p in (run/'stages').iterdir() if p.is_dir()):
        cmd = load(run/'stages'/stage/'command.json')
        expect(stage, 'stage_started', {'command_file': f'stages/{stage}/command.json', 'cpu_limit_seconds': cmd['cpu_seconds'],
                                        'memory_limit_bytes': cmd['memory_bytes'], 'wall_limit_seconds': cmd['wall_seconds']}, drop=('cgroup',))
        expect(stage, 'stage_finished', load(run/'stages'/stage/(stage+'.process.json')))
    expect('episode', 'episode_started', {'policy_sha256': sha((run/'search-policy.json').read_bytes()), 'challenge_sha256': frozen['challenge_sha256'], 'nonce': nonce, 'mode': 'rehearsal'})
    expect('credential-receipt', 'credential_receipt_checked', load(run/'credential-receipt.json'))
    if kind == 'interface_refused':
        expect('request-admission', 'interface_refused', {'stage': 'pipeline-prepare', 'stderr_sha256': sha((run/'stages/pipeline-prepare/pipeline-prepare.stderr').read_bytes())})
    else:
        out = run/'stages/proposal-1/output'
        expect('payload', 'prepared_problem', {'prepared_sha256': sha((run/'prepared.json').read_bytes()), 'input_ir_sha256': sha((run/'input-ir.json').read_bytes()),
                                               'payload_audit_sha256': sha((run/'payload-audit.json').read_bytes())})
        live = {'arguments_sha256': sha((run/'live-arguments.json').read_bytes()), 'contract_sha256': sp['contract_sha256'],
                'messages_sha256': sha((run/'live-messages.json').read_bytes()), 'policy_sha256': sp['config_sha256'],
                'prepared_sha256': sha((run/'prepared.json').read_bytes()), 'prompt_sha256': sha(contract.PROMPT.read_bytes()),
                'request_sha256': sha((run/'live-request.json').read_bytes()), 'policy_c_evidence_sha256': sha((run/'policy-c-evidence.json').read_bytes()),
                'payload_audit_sha256': sha((run/'payload-audit.json').read_bytes())}
        expect('live-payload', 'payload_validated', live, drop=('inner_binding',))
        if {k: v for k, v in load(run/'live-payload.json').items() if k != 'inner_binding'} != live: problems.append('live-payload.json')
        expect('campaign-ledger', 'reservation_attempted', {'attempt_id': permit['attempt_id']})
        expect('pricing-admission', 'pricing_admitted', {'admission_sha256': sha((run/'host-pricing-admission.json').read_bytes())})
        expect('campaign-ledger', 'request_reserved', load(run/'reservation.json'))
        expect('campaign-ledger', 'reservation_reconciled', {'kind': reconciliation['kind'], 'reservation_id': reconciliation['reservation_id'], 'row_hash': reconciliation['row_hash'],
                                                             'send_outcome': reconciliation.get('send_outcome'), 'termination_established': reconciliation['termination_established'],
                                                             'record_read_failures': len(reconciliation['evidence']['record_read_failures']), 'evidence_write_failures': [],
                                                             'ledger_sha256': sha((run/'ledger-after.ndjson').read_bytes()), 'recovered': None})
        expect('proposal', 'https_observed', {'http_sha256': sha((out/'http.json').read_bytes()), 'server_sha256': sha((out/'server.json').read_bytes()),
                                              'pricing_check_sha256': sha((out/'pricing-check.json').read_bytes())})
        expect('proposal', 'transport_validated', load(run/'transport-validation.json'))
    if kind in SENT:
        expect('certificate-check', 'independent_certificate_verdict', load(run/'certificate-verdict.json'))
    if kind == 'reconstruction_refused':
        expect('reconstruct', 'reconstruction_refused', load(run/'reconstruction-refusal.json'))
    if kind == 'proof':
        verdict = load(run/'verdict.json')
        expect('validation-local', 'kernel_verdict', verdict['final_validation']['local']); expect('validation-whole', 'kernel_verdict', verdict['final_validation']['whole'])
    a.require(not problems, f'{name}:receipts:payloads_bound_to_records', 'receipts differ from their records: '+', '.join(problems))


# ---------------------------------------------------------------------------------------------------------------- per run: finalization

def seal(a, run, name):
    if not (run/'seal.json').exists(): a.require(False, f'{name}:seal:retained_hashes', 'run is not sealed')
    s = load(run/'seal.json')
    present = {str(p.relative_to(run)) for p in run.rglob('*') if p.is_file()}
    mismatched = [k for k, v in s['retained_sha256'].items() if not (run/k).is_file() or sha((run/k).read_bytes()) != v]
    unlisted = sorted(present-set(s['retained_sha256'])-set(s['ephemeral_sha256'])-{'seal.json'})
    a.require(not mismatched and s['retained_sha256'] and not unlisted, f'{name}:seal:retained_hashes', f'{len(mismatched)} differ; unlisted {unlisted[:3]}')
    return s


def publication_recomputed(a, run, name):
    nonce = load(run/'credential-canary.json')['nonce']; canary = credential.derive(nonce)
    retained_report = load(run/'publication-scan.json'); final = load(run/'publication-final.json')
    fresh = publication.scan([run], canary, nonce)
    lines = (run/'events.ndjson').read_bytes().splitlines(True); prefix = b''.join(lines[:-1])
    entries = [e for e in retained_report['inventory'] if e['path']]
    paths = [e['path'] for e in entries]
    def describes(e):
        if e['path'] == 'events.ndjson': return e['sha256'] == sha(prefix) and e['bytes'] == len(prefix)
        p = run/e['path']; return p.is_file() and e['sha256'] == sha(p.read_bytes()) and e['bytes'] == p.stat().st_size
    fresh_streams = {e['path']: e['streams'] for e in fresh['inventory'] if e['path']}
    well_formed = all(e['scanned'] is True and e['error'] is None and e['findings'] == [] and 'raw' in e['streams']
                      and fresh_streams.get(e['path']) == e['streams'] for e in entries)
    a.require(retained_report['accepted'] is True and retained_report['disclosures'] == [] and retained_report['incompletely_scanned'] == []
              and retained_report['unreadable_directories'] == [] and retained_report['irregular_entries'] == []
              and len(paths) == len(set(paths)) == retained_report['files_scanned'] == len(retained_report['inventory'])
              and retained_report['gzip_streams_scanned'] == sum('gzip' in e['streams'] for e in entries)
              and retained_report['canary_nonce'] == nonce and well_formed and all(describes(e) for e in entries)
              and fresh['accepted'] is True and fresh['disclosures'] == []
              and {e['path'] for e in fresh['inventory'] if e['path']}-set(paths) <= {'publication-scan.json', 'publication-final.json', 'seal.json'}
              and final == publication.final_record(run/'publication-scan.json', canary, nonce),
              f'{name}:publication:recomputed')
    return retained_report, final


def terminal(a, run, name, kind, rows, report, final):
    summary = load(run/'credential-summary.json'); last = rows[-1]['payload']; acct = load(run/'accounting.json')
    publication_ok = bool(report['accepted'] and final['report_clean'])
    if kind == 'interface_refused':
        derived = (not (run/'campaign-permit.json').exists() and not (run/'campaign-reconciliation.json').exists() and not (run/'stages/proposal-1').exists()
                   and not any(r['event'] == 'reservation_attempted' for r in rows) and summary['reservation_state'] == 'not_reserved' and summary['ledger_reconciled'] is True)
    else:
        derived = ((run/'campaign-reconciliation.json').exists() and (run/'ledger-after.ndjson').exists() and (run/'stages/proposal-1/grant').is_dir()
                   and any(r['event'] == 'reservation_reconciled' for r in rows) and summary['reservation_state'] == 'reserved' and summary['ledger_reconciled'] is True)
    mirrors = (summary['evidence_complete'] is derived and acct['evidence_complete'] is derived and last['evidence_complete'] is derived
               and summary['reconciliation_evidence_complete'] is acct['reconciliation_evidence_complete']
               and summary['reservation_state'] == acct['reservation_state'] and summary['ledger_reconciled'] is acct['ledger_reconciled'])
    evidence_ok = derived and bool(summary['ledger_reconciled'])
    accepted = bool(summary['proof_accepted'] and summary['credential_use_accepted'] and publication_ok and evidence_ok)
    completed = summary['proof_accepted'] and summary['failure_category'] is None and publication_ok and evidence_ok
    a.require(mirrors and last['summary_sha256'] == sha((run/'credential-summary.json').read_bytes())
              and last['publication_scan_sha256'] == sha((run/'publication-scan.json').read_bytes())
              and last['publication_final_sha256'] == sha((run/'publication-final.json').read_bytes())
              and last['proof_accepted'] is bool(summary['proof_accepted']) and last['credential_use_accepted'] is bool(summary['credential_use_accepted'])
              and last['publication_accepted'] is publication_ok and last['publication_pending'] is False
              and last['ledger_reconciled'] is bool(summary['ledger_reconciled']) and last['accepted'] is accepted
              and rows[-1]['event'] == ('episode_finished' if completed else 'episode_rejected') and (kind == 'proof') == completed
              and publication.safe_record(last, driver.TERMINAL_KEYS),
              f'{name}:terminal:commitments_bound', 'evidence_complete mirrors disagree with the artifacts' if not mirrors else '')
    return accepted


def summary_bound(a, run, name, kind, task, draw, sp, contract_digest):
    summary = load(run/'credential-summary.json'); acct = load(run/'accounting.json')
    a.require(summary['schema_version'] == 'r6-cohort-summary-1' and summary['task_id'] == task.id and summary['draw'] == draw
              and summary['campaign_id'] == sp['campaign_id'] and summary['revision'] == sp['revision'] and summary['contract_sha256'] == contract_digest
              and summary['search_policy'] == sp['name'] and summary['mode'] == sp['mode'] and summary['accounting'] == acct
              and summary['proof_accepted'] is (run/'verdict.json').exists() and summary['proof_accepted'] is (kind == 'proof')
              and summary['failure_category'] == FAILURE_CATEGORY[kind],
              f'{name}:summary:bound_to_audited_records', 'summary identity or embedded accounting differs from the audited records')


def chain_and_outcome(a, run, name, kind, rows, s, accepted):
    a.require(s['event_count'] == len(rows) and s['last_event_hash'] == rows[-1]['event_hash'] and s['accepted'] is accepted is (kind == 'proof'),
              f'{name}:seal:chain_and_outcome')


def grant(a, run, name, kind, permit, http):
    slot = run/'stages/proposal-1/grant/send-grant.json'
    if kind in SENT:
        try: g = read_grant(slot.parent, permit)
        except ledger.Failure: g = None
        created, durable = http.get('grant_created_at_ns'), http.get('grant_durable_at_ns')
        a.require(g is not None and http['grant_committed'] is True and http['grant_id'] == g['grant_id'] and http['send_outcome'] == 'returned'
                  and created == g['at_ns'] and isinstance(durable, int) and http['grant_write_failed'] is False, f'{name}:grant:consistent_with_outcome',
                  'durable completion timestamp missing' if durable is None else '')
        a.require(http['tls_verified_at_ns'] < created <= durable < http['header_send_at_ns'] and http['connection_started_at_ns'] <= http['tls_verified_at_ns']
                  and http['permit_verified_at_ns'] < http['pricing_admitted_at_ns'] <= http['credential_read_at_ns'] < http['connection_started_at_ns'],
                  f'{name}:grant:ordered_before_first_header_byte')
    else:
        a.require(not slot.exists() and (http is None or (http['grant_committed'] is False and http['send_outcome'] == 'not_started'
                  and http['body_sends_started'] == 0 and http['header_sends_started'] == 0)), f'{name}:grant:consistent_with_outcome')


def actor_check(a, run, name, policy, contract_value, instruction, request_bytes, arguments, permit, body):
    out = run/'stages/proposal-1/output'; record = load(out/'pricing-check.json')
    try: derived = gate.admission(policy, contract_value, instruction, run/'transport-pricing-sources', arguments, request_bytes, record['evaluated_at_unix'])
    except gate.Failure as error: a.require(False, f'{name}:pricing:actor_check_rederived', error.code)
    a.require(record['accepted'] is True and {k: v for k, v in record.items() if k != 'admitted_at_ns'} == derived
              and record['reserved_micro_usd'] == permit['reserved_micro_usd'] == permit['reservation']['reserved_micro_usd']
              and record['body_sha256'] == sha((out/'serialized-body.json').read_bytes()) == sha(body)
              and 0 <= record['evaluated_at_unix']-permit['pricing_admission']['evaluated_at_unix'] <= policy['pricing_admission']['maximum_permit_age_seconds'],
              f'{name}:pricing:actor_check_rederived')


def transport(a, run, name, kind, policy, task, draw, permit, http, body, contract_digest):
    out = run/'stages/proposal-1/output'; serialized = (out/'serialized-body.json').read_bytes(); server = load(out/'server.json')
    sent = (out/'outbound-body.json').exists() or (out/'received-body.json').exists() or http['body_sends_started'] > 0
    a.require(serialized == body and (not sent or ((out/'outbound-body.json').read_bytes() == body and (out/'received-body.json').read_bytes() == body
                                                   and http['outbound_body_sha256'] == sha(body))) and sent is (kind in SENT),
              f'{name}:transport:bodies_are_the_contract_rendering')
    a.require(http['schema_version'] == 'r6-cohort-observation-1' and http['mode'] == 'rehearsal' and http['policy_sha256'] == sha((run/'transport-policy.json').read_bytes())
              and http['contract_sha256'] == contract_digest and http['task_id'] == task.id and http['draw'] == draw and http['slot'] == f'{task.id}/{draw}'
              and http['request_sha256'] == sha(serialized) and http['request_bytes'] == len(serialized) and http['retries'] == 0 and http['redirects_followed'] == 0
              and http['transport_scope'] == 'isolated_loopback_https_fixture' and http['endpoint'] == policy['endpoint']
              and http['reservation_id'] == permit['reservation_id'] and http['authorization_present_in_policy'] is None
              and http['maximum_response_bytes'] == policy['limits']['maximum_response_bytes'],
              f'{name}:transport:record_consistent')
    if kind in SENT:
        nonce = load(run/'credential-canary.json')['nonce']; header = credential.header(credential.derive(nonce))
        a.require(http['http_status'] == 200 and http['body_sends_returned'] == 1 and http['body_sends_started'] == 1 and http['header_sends_started'] == 1
                  and len(server['requests']) == 1 and server['requests'][0]['body_sha256'] == sha(body)
                  and server['requests'][0]['authorization_sha256'] == sha(header.encode()) and server['server_names'] == [policy['endpoint']['host']]
                  and http['tls']['verified'] is True and http['tls']['server_hostname'] == policy['endpoint']['host']
                  and http['response_sha256'] == sha((out/'provider-response.json').read_bytes()),
                  f'{name}:transport:local_send_and_remote_receipt')
    return serialized


def commitment(a, run, name, http):
    nonce = load(run/'credential-canary.json')['nonce']; header = credential.header(credential.derive(nonce))
    expected = sha((COMMITMENT_DOMAIN+':'+http['commitment_nonce']+':'+header).encode())
    text = (run/'stages/proposal-1/output/http.json').read_text()
    if http['failure_category'] == 'credential_format':
        a.require(http['credential_commitment_sha256'] is None and 'Bearer' not in text, f'{name}:commitment:bound_to_mounted_canary')
    else:
        a.require(http['credential_commitment_sha256'] == expected and credential.derive(nonce) not in text, f'{name}:commitment:bound_to_mounted_canary')


def interpretation(a, run, name, request_bytes):
    out = run/'stages/proposal-1/output'
    proposed, text, metadata, validation, error = budget.interpret(out, request_bytes, False)
    same_text = (text is None and not (run/'response.json').exists()) or (text is not None and (run/'response.json').read_bytes() == text)
    a.require(validation == load(run/'transport-validation.json') and metadata == load(run/'provider-metadata.json') and same_text
              and (error is None) == (validation['failure_category'] is None), f'{name}:interpretation:reproduced')


def slot_identity(a, run, name, sp, task, draw, permit, http, body):
    text = body.decode()
    a.require(http['slot'] == f'{task.id}/{draw}' and http['task_id'] == task.id and http['draw'] == draw and http['reservation_id'] == permit['reservation_id']
              and not any(needle in text for needle in (permit['reservation_id'], permit['attempt_id'], sp['campaign_id'], sp['config_sha256'], http['commitment_nonce'],
                                                        http.get('grant_id') or 'grant_id', 'draw', 'slot', 'campaign', 'revision')),
              f'{name}:slot:identity_in_receipts_not_in_model_bytes')


def accounting(a, run, name, kind, policy, http, permit, reconciliation):
    acct = load(run/'accounting.json'); out = run/'stages/proposal-1/output'
    server = load(out/'server.json') if (out/'server.json').exists() else None
    if kind == 'interface_refused':
        lifecycle = {'permit': None, 'reservation': None, 'reconciliation': None, 'reconcile_error': None, 'attempt_id': None,
                     'reservation_state': 'not_reserved', 'evidence_write_failures': []}
    else:
        lifecycle = {'permit': permit, 'reservation': load(run/'reservation.json'), 'reconciliation': reconciliation, 'reconcile_error': None,
                     'reservation_state': 'reserved', 'evidence_write_failures': []}
    expected = driver.accounting_for(run, policy, False, http, server, lifecycle)
    a.require(acct == expected and acct['allowance_consumed'] == ALLOWANCE[kind], f'{name}:accounting:recomputed')
    r = load(run/'credential-receipt.json'); nonce = load(run/'credential-canary.json')['nonce']
    expected_header = sha(credential.header(credential.derive(nonce)).encode())
    observed = server['requests'][0]['authorization_sha256'] if kind in SENT else None
    a.require(r['schema_version'] == 'r6-credential-receipt-1' and r['channel'] == 'private_read_only_file' and r['declared_case'] == 'rehearsal'
              and r['exact_receipt'] is (kind in SENT) and r['transmissions'] == (len(server['requests']) if server else 0) == (1 if kind in SENT else 0)
              and r['authorization_present'] is (kind in SENT) and r['expected_authorization_sha256'] == expected_header
              and r['observed_authorization_sha256'] == observed and (observed == expected_header) is (kind in SENT),
              f'{name}:credential_receipt:recorded')


# ---------------------------------------------------------------------------------------------------------------- per run: outcomes

def failure(a, run, name, http):
    summary = load(run/'credential-summary.json')
    stderr = (run/'stages/proposal-1/proposal-1.stderr').read_text(); process = load(run/'stages/proposal-1/proposal-1.process.json')
    a.require(summary['failure_category'] == 'credential_format' and summary['failure_phase'] == 'credential_delivery' and http['failure_category'] == 'credential_format'
              and process['exit_code'] == 0 and stderr == '' and http['connection_attempts'] == 0 and http['http_status'] is None
              and load(run/'stages/proposal-1/output/pricing-check.json')['accepted'] is True and not (run/'response.json').exists()
              and (run/'seal.json').exists(), f'{name}:failure:classified_and_finalized')


def interface_refused(a, run, name, rows, task, representability):
    """The SDK's own refusal, before any request, reservation or send: its message is the classification's, byte for byte."""
    stderr = (run/'stages/pipeline-prepare/pipeline-prepare.stderr').read_bytes(); summary = load(run/'credential-summary.json')
    retained = (representability/task.id/'stages/pipeline-prepare/pipeline-prepare.stderr').read_bytes()
    a.require(stderr.startswith(b'Failure(') and stderr == retained and summary['failure_phase'] == 'preparation'
              and summary['error'] == 'SDK refused to prepare: '+stderr.decode()[:200]
              and not any((run/f).exists() for f in ('prepared.json', 'live-request.json', 'campaign-permit.json', 'reservation.json', 'transport-ledger.ndjson',
                                                     'ledger-after.ndjson', 'campaign-reconciliation.json', 'transport-request.json', 'pricing-sources'))
              and not (run/'stages/proposal-1').exists(), f'{name}:interface:refused_before_reservation')


def response_bound(a, run, name, kind, request_bytes):
    response, validated = load(run/'response.json'), load(run/'validated-response.json'); out = run/'stages/proposal-1/output'
    raw = load(out/'provider-response.json')
    text = [c['text'] for item in raw['output'] if item.get('type') == 'message' for c in item['content'] if c.get('type') == 'output_text']
    a.require(response == validated and json.loads(''.join(text)) == response and response['request_sha256'] == sha(request_bytes) and raw['status'] == 'completed',
              f'{name}:{kind}:response_bound')
    return response


def attribution(a, run, name, kind, rows, sp):
    named = {r['event']: (r['payload'].get('proposer', r['payload'].get('witness_proposer')), r['payload'].get('route'), r['payload'].get('consumer_route'))
             for r in rows if r['event'] in ('recovery_started', 'certificate_assembled', 'recovery_finished')}
    assembled = next(r['payload'] for r in rows if r['event'] == 'certificate_assembled')
    verdict_ok = True
    if kind == 'proof':
        verdict = load(run/'verdict.json')
        verdict_ok = verdict['witness_proposer'] == 'canned_provider_response' and verdict['consumer_route'] == 'openai_responses_http_fixture_v1' \
                     and verdict['certificate_assembler'] == 'sdk_proposal_assembler_v1'
    a.require(named == {'recovery_started': ('canned_provider_response', sp['name'], None),
                        'certificate_assembled': ('canned_provider_response', None, 'openai_responses_http_fixture_v1'),
                        'recovery_finished': ('canned_provider_response', sp['name'], 'openai_responses_http_fixture_v1')}
              and assembled['certificate_assembler'] == 'sdk_proposal_assembler_v1' and verdict_ok,
              f'{name}:{kind}:attribution_passed_through', str(named))


def negative(a, run, name, rows, record, response, request_bytes):
    """The negative control: its rows have a feasible point, so no certificate exists; the canned witness is the well-formed non-certificate,
    the independent verifier rejects it and the episode stops before any reconstruction."""
    prepared = load(run/'prepared.json'); rows_ = prepared['rows']
    point = {k: Fraction(v) for k, v in record.get('feasible_point', {}).items()}
    a.require(record['class'] == 'posable_negative_control' and record['arithmetic_certificate'] is False and bool(point) and rep.check_point(rows_, point)
              and rep.farkas(rows_) is None and response['witness'] == {'coefficients': [{'hypothesis': 'neg_goal', 'coefficient': '1'}]}
              and response['request_sha256'] == sha(request_bytes), f'{name}:negative:witness_is_the_canned_non_certificate')
    cert, evidence = load(run/'certificate-verdict.json'), load(run/'evidence.json'); summary = load(run/'credential-summary.json')
    assembled = next(r['payload'] for r in rows if r['event'] == 'certificate_assembled'); finished = next(r['payload'] for r in rows if r['event'] == 'recovery_finished')
    a.require(cert['accepted'] is False and evidence['certificate']['payload']['witness_data'] == response['witness']
              and assembled['certificate_sha256'] == events.digest(evidence['certificate']) and assembled['response_sha256'] == sha((run/'validated-response.json').read_bytes())
              and load(run/'stages/assembly/output/evidence.json') == evidence
              and finished['ok'] is False and finished['reason'] == cert.get('reason') and finished['witness'] == response['witness']
              and not (run/'verdict.json').exists() and summary['failure_phase'] == 'certificate_verification' and summary['error'] == 'Farkas witness was not verified',
              f'{name}:negative:verifier_rejected_and_stopped')


def merged_directives(ir):
    """`buildExtractionPath`'s merge at e627efe: `getD` of an all-none record, then the tier preference; none fields are omitted in JSON."""
    ir = copy.deepcopy(ir); ir['user_directives'] = {**(ir.get('user_directives') or {}), 'tier_preference': ['1', '2']}
    return ir


def site_shared_checker(task, packet, verdict, rows, path, read, receipt):
    """`envelope_proof_audit.audit` (the frozen R6-001 proof-path checks), with the site's frozen identity and instrumentation in place of
    the registered task's; the reification comparison uses the tactic's directive merge, which creates the directive record when absent."""
    require = envelope_proof_audit.require
    _, expected = site_task.frozen_site(task)
    cert = packet['certificate']
    child_names = [e for (_, _, e) in CHILDREN]
    children = [r for r in rows if r['source'] == 'child_report']
    require([r['event'] for r in children] == child_names, 'unexpected reconstruction observations or hidden search route')
    start = next(r['sequence'] for r in rows if r['stage'] == 'reconstruct' and r['event'] == 'stage_started')
    finish = next(r['sequence'] for r in rows if r['stage'] == 'reconstruct' and r['event'] == 'stage_finished')
    require(all(start < r['sequence'] < finish and r['stage'] == 'reconstruct'
                and r['payload']['component'] == 'lean_bridge' for r in children), 'child observation boundary')
    observed = {r['event']: r['payload']['data'] for r in children}
    require(merged_directives(observed['reification_finished']['ir']) == packet['input_ir'] == observed['dispatch_started']['ir'], 'fresh reification differs from proposal input')
    require(observed['dispatch_started']['manifests'] == [] and observed['dispatch_started']['prefer_higher_tier'] is False, 'proposal delivery invoked solver dispatch')
    received = observed['dispatch_received']
    require(received['certificate'] == cert and received['final_ir'] == packet['final_ir'] and received['trace'] == packet['trace'], 'reconstruction received different evidence')
    for n in ['certificate_verification_started', 'certificate_verification_finished', 'reconstruction_started', 'closer_selected', 'reconstruction_finished']:
        require(observed[n]['certificate'] == cert, 'certificate changed at '+n)
    require(observed['certificate_verification_finished']['ok'] is True and observed['certificate_verification_finished']['envelope_ok'] is True, 'bridge verifier did not accept')
    require(observed['reconstruction_finished'] == {'certificate': cert, 'closer': observed['closer_selected']['closer'],
        'certificate_consumed': True, 'derivation_replayed': False, 'residual_closer': 'omega'}
        and observed['closer_selected']['closer'] in CONSUMING_CLOSERS and verdict['closer'] == observed['closer_selected']['closer'], 'consumption path changed')
    require(receipt('reconstruct', 'context_validated') == {
        'captured_context_sha256': r6.sha(path('stages/reconstruct/output/context.json')),
        'frozen_context_sha256': r6.sha(task.path/'context/local-context.json')}, 'reconstruction context receipt')
    pristine = site_task.census.pristine().decode()
    for directory, helper, preparation in [('preparation-input', 'PreparationCapture', True), ('input', 'ProposalCapture', False)]:
        source = site_task.instrumented(task, helper, 'r6_prepare' if preparation else 'r6_capture_proposal')
        require(path(f'{directory}/Frozen.lean').read_text() == source
                and path(f'{directory}/{helper}.lean').read_text() == site_task.capture_source(task, preparation), 'source differs from permitted extraction')
        require(path(f'{directory}/source.patch').read_text() == ''.join(difflib.unified_diff(
            pristine.splitlines(True), source.splitlines(True), fromfile='Pristine.lean', tofile='Frozen.lean')), 'reported source modification differs')
    baseline = {t['name']: t for t in expected['targets']}
    delta = {}; digest = hashlib.sha256(); length = 0
    with gzip.open(path('solution.ndjson.gz'), 'rb') as f:
        while block := f.read(1024**2):
            length += len(block); require(length <= 256*1024**2, 'proof export exceeds budget'); digest.update(block)
    require(digest.hexdigest() == verdict['solution_sha256'], 'proof hash mismatch')
    for kind, target, config_policy in [('local', task.local, episode.local_policy(task)), ('whole', task.whole, r6.policy([task.whole], True, task=task))]:
        require(read(f'validation-input/{kind}/policy.json') == config_policy, 'validation policy changed')
        with gzip.open(path(f'validation-{kind}.raw.json.gz'), 'rb') as f: raw_report = f.read(4*1024**2+1)
        require(len(raw_report) <= 4*1024**2, 'oversized replay report')
        report = json.loads(raw_report)
        require(report['accepted'] is True and report['stage'] == 'complete' and report['kernel_version'] == '4.32.2'
                and report['local_proof_binding_checked'] is True and report['checked_declarations'] > 0, 'independent kernel/reference check failed')
        require(len(report['targets']) == 1 and report['targets'][0]['name'] == target, 'missing expected declaration')
        t = report['targets'][0]
        require(all(t[k] is True for k in ['declaration_exists', 'statement_and_dependencies_match', 'kernel_accepted']), 'target validation')
        t['type_sha256'] = hashlib.sha256(t.pop('type_repr').encode()).hexdigest(); t['type_hash_format'] = 'Lean-4.32.2-reprStr-Expr-UTF8'
        require(t['type_sha256'] == baseline[target]['type_sha256'] and set(t['axioms']) <= set(r6.AXIOMS), 'frozen type/axiom policy')
        require(report == verdict['final_validation'][kind] == receipt('validation-'+kind, 'kernel_verdict'), 'replay report/receipt mismatch')
        delta[target] = {'added': sorted(set(t['axioms'])-set(baseline[target]['axioms'])), 'removed': sorted(set(baseline[target]['axioms'])-set(t['axioms']))}
    require(verdict['axiom_delta'] == delta, 'axiom delta mismatch')


def reconstruction_common(a, run, name, rows, sp, request_bytes, record, response, kind):
    """What proof and refused reconstruction share, each stage its own case: the generated witness verified and bound to the classification's
    exact certificate; the IR reconstruction reified equal to the prepared one (the guard passed); one closer selected, for this certificate."""
    evidence, cert = load(run/'evidence.json'), load(run/'certificate-verdict.json')
    assembled = next(r['payload'] for r in rows if r['event'] == 'certificate_assembled')
    verdict_ok = True
    if kind == 'proof':
        verdict = load(run/'verdict.json')
        verdict_ok = (verdict['certificate_validation'] == cert and verdict['request_sha256'] == sha(request_bytes) and verdict['schema_version'] == 'r6-cohort-proof-1'
                      and verdict['search_policy'] == sp['name'] and verdict['mode'] == 'rehearsal')
    a.require(response['witness'] == {'coefficients': record['certificate']} and rep.check_certificate(load(run/'prepared.json')['rows'],
              {c['hypothesis']: int(c['coefficient']) for c in record['certificate']})
              and evidence['certificate']['payload']['witness_data'] == response['witness'] and cert['accepted'] is True and cert['reason']['kind'] == 'verified_farkas'
              and cert['certificate_hash'] == 'sha256:'+assembled['certificate_sha256'] and assembled['response_sha256'] == sha((run/'validated-response.json').read_bytes())
              and load(run/'stages/assembly/output/evidence.json') == evidence and verdict_ok, f'{name}:certificate:verified_and_bound')
    observed = {r['event']: r['payload']['data'] for r in rows if r['source'] == 'child_report'}
    log = b''.join((run/'stages/reconstruct'/f'reconstruct.{s}').read_bytes() for s in ('stdout', 'stderr') if (run/'stages/reconstruct'/f'reconstruct.{s}').exists())
    reified, dispatched = observed['reification_finished']['ir'], observed['dispatch_started']['ir']
    a.require(merged_directives(reified) == evidence['input_ir'] == load(run/'input-ir.json') == load(run/'prepared.json')['input_ir'] == dispatched
              and GUARD.encode() not in log, f'{name}:reconstruction:preparation_ir_equal')
    selected = [r['payload']['data'] for r in rows if r['source'] == 'child_report' and r['event'] == 'closer_selected']
    verification = observed['certificate_verification_finished']
    a.require(len(selected) == 1 and selected[0]['certificate'] == evidence['certificate'] == observed['reconstruction_started']['certificate']
              and verification['ok'] is True and verification['envelope_ok'] is True and verification['certificate'] == evidence['certificate']
              and isinstance(selected[0]['goal'], str) and selected[0]['closer'] in ('term_mode_nat', 'term_mode_int', 'term_mode_poly', 'term_mode_case_split', 'term_mode_ext'),
              f'{name}:reconstruction:closer_selected', str(selected)[:300])
    return evidence, observed, selected[0]


def reconstruction_refused(a, run, name, rows, task, sp, request_bytes, record, response):
    """A refused reconstruction: the refusal recomputed from bound evidence by the driver's own rule equals the retained record and receipt,
    and names the predeclared diagnosis; nothing of a completed proof exists."""
    evidence, observed, selected = reconstruction_common(a, run, name, rows, sp, request_bytes, record, response, 'reconstruction_refused')
    retained = load(run/'reconstruction-refusal.json'); summary = load(run/'credential-summary.json')
    try: recomputed = driver.reconstruction_refusal(run, evidence)
    except (KeyError, OSError, ValueError): recomputed = None
    a.require(recomputed is not None and recomputed == retained and retained['diagnosis'] == RECONSTRUCTION_STRATUM[task.id]
              and selected['closer'] == retained['closer'] == 'term_mode_nat' and selected['comparison_type'] == retained['comparison_type']
              and summary['failure_category'] == 'reconstruction_refused' and summary['failure_phase'] == 'reconstruction'
              and summary['error'] == f"pinned term_mode_nat closer refused the goal ({retained['diagnosis']})",
              f'{name}:reconstruction:refusal_diagnosed', str(recomputed)[:300])
    completion = [r['event'] for r in rows if r['event'] in ('reconstruction_finished', 'closer_returned', 'residual_started', 'residual_finished', 'context_validated',
                                                             'kernel_verdict', 'proof_validated', 'episode_finished')]
    a.require(not completion and not any((run/f).exists() for f in ('verdict.json', 'solution.ndjson.gz', 'validation-input', 'validation-local.raw.json.gz',
                                                                     'validation-whole.raw.json.gz', 'stages/export', 'stages/validation-local', 'stages/validation-whole'))
              and summary['proof_accepted'] is False, f'{name}:reconstruction:no_completion_evidence', str(completion))


def proof(a, run, name, rows, task, sp, request_bytes, record, response, frozen):
    evidence, observed, selected = reconstruction_common(a, run, name, rows, sp, request_bytes, record, response, 'proof')
    verdict = load(run/'verdict.json')
    finished = observed.get('reconstruction_finished')
    a.require(finished == {'certificate': evidence['certificate'], 'closer': selected['closer'], 'certificate_consumed': True, 'derivation_replayed': False, 'residual_closer': 'omega'}
              and selected['closer'] in CONSUMING_CLOSERS and verdict['closer'] == selected['closer']
              and verdict['certificate_verified'] is True and verdict['certificate_consumed'] is True and verdict['derivation_replayed'] is False
              and verdict['residual_closer'] == 'omega' and verdict['proof_replayed'] is True and verdict['trust_tier'] == 1,
              f'{name}:proof:certificate_consumed', str(finished)[:300])
    def receipt(stage, event):
        hits = [r['payload'] for r in rows if r['source'] == 'supervisor' and r['stage'] == stage and r['event'] == event]
        if len(hits) != 1: raise ValueError(f'{stage}/{event}: {len(hits)} receipts')
        return hits[0]
    read = lambda n: load(run/n)
    try:
        challenge = json.loads(request_bytes)['binding']['challenge_sha256']
        context = read('stages/reconstruct/output/context.json')
        if not (context == read('stages/preparation/output/context.json') == load(task.path/'context/local-context.json')):
            raise ValueError('reconstruction context differs from the frozen context')
        if verdict['task_id'] != task.id or verdict['manifest_sha256'] != sha((task.path/'manifest.json').read_bytes()) \
                or not (verdict['challenge_sha256'] == frozen['challenge_sha256'] == challenge):
            raise ValueError('target identity differs (task, manifest or challenge)')
        site_shared_checker(task, evidence, verdict, rows, lambda n: run/n, read, receipt)
    except (ValueError, AssertionError, KeyError, OSError, gzip.BadGzipFile, EOFError) as error:
        a.require(False, f'{name}:proof:shared_checker', str(error))
    a.require(True, f'{name}:proof:shared_checker')
    baseline = {t['name']: t for t in frozen['targets']}; problems = []
    for kind, target in (('local', task.local), ('whole', task.whole)):
        report = verdict['final_validation'][kind]; t = report['targets'][0] if len(report['targets']) == 1 else {}
        if not (report['accepted'] is True and report['stage'] == 'complete' and report['local_proof_binding_checked'] is True and t.get('name') == target
                and all(t.get(k) is True for k in ('declaration_exists', 'statement_and_dependencies_match', 'kernel_accepted'))
                and t.get('type_sha256') == baseline[target]['type_sha256'] and set(t.get('axioms', ['?'])) <= set(r6.AXIOMS)
                and verdict['axiom_delta'].get(target) == {'added': [], 'removed': []}):
            problems.append(kind)
    a.require(not problems and sorted(verdict['axiom_delta']) == sorted([task.local, task.whole]) and verdict['local_obligation_closed'] is True
              and verdict['whole_declaration_validated'] is True, f'{name}:proof:original_declarations_validated', ', '.join(problems))
    proved = next(r['payload'] for r in rows if r['event'] == 'proof_validated')
    export = run/'stages/export/export.stdout'
    a.require(proved == {'verdict_sha256': sha((run/'verdict.json').read_bytes()), 'proof_accepted': True, 'solution_sha256': verdict['solution_sha256']}
              and export.is_file() and sha(export.read_bytes()) == verdict['solution_sha256'] == sha(gzip.decompress((run/'solution.ndjson.gz').read_bytes())),
              f'{name}:proof:export_recorded')
    return verdict['solution_sha256'], selected['closer']


# ---------------------------------------------------------------------------------------------------------------- cross-run

def cross_run(a, root, ledgers, expected, sp_by_run, policy, bodies, sent, identities, permits, reconciliations, priced, contract_digest):
    names = sorted(expected)
    campaign_ids = {sp['campaign_id'] for sp in sp_by_run.values()}
    a.require(campaign_ids == {policy['campaign']['id']}, 'campaign:single_identity', str(campaign_ids))
    campaign = policy['campaign']['id']
    site = RELEASE_RUN[1]; group = bodies[site]; distinct = {sha(b) for b in group.values()} | {sha(b) for b in sent.get(site, {}).values()}
    a.require(len(distinct) == 1 and sorted(group) == sorted([run_name(site), RELEASE_RUN[0]]) and len(sent.get(site, {})) == 1,
              f'input:identical_model_bytes_across_draws:{site}', f'{len(distinct)} distinct entity bodies across {sorted(group)}')
    per_task = {t: sha(next(iter(g.values()))) for t, g in bodies.items()}
    a.require(len(set(per_task.values())) == len(per_task) == len({t for (k, t, _, _) in expected.values() if k != 'interface_refused'}),
              'input:distinct_model_bytes_across_tasks', str(per_task))
    ids = [v['reservation_id'] for v in identities.values()]; grants = [v['grant_id'] for v in identities.values() if v['grant_id']]
    nonces = [v['nonce'] for v in identities.values()]; attempts = [v['attempt_id'] for v in identities.values()]
    canaries = [load(root/n/'credential-canary.json')['nonce'] for n in names]
    a.require(all(len(set(x)) == len(x) for x in (ids, grants, nonces, attempts, canaries)) and len(grants) == sum(k in SENT for (k, *_) in expected.values()),
              'receipts:distinct_across_runs')
    book = ledger.Ledger(ledgers/campaign/'rehearsal', campaign)
    try:
        if not book.head.exists() or not book.path.exists(): raise ledger.Failure('cohort_ledger_missing')
        head = load(book.head); rows = ledger.parse(book.path.read_bytes()); s = ledger.state(rows, campaign)
        if not (head['rows'] == len(rows) and rows[-1]['row_hash'] == head['last_hash'] and head['campaign_id'] == campaign): raise ledger.Failure('cohort_ledger_head')
    except ledger.Failure as error: a.require(False, 'ledger:continuous_single_revision', error.code)
    reserved = [n for n in names if expected[n][0] != 'interface_refused']
    prefixes = all(rows[:len(snap)] == snap for n in reserved
                   for snap in (ledger.parse((root/n/'transport-ledger.ndjson').read_bytes()), ledger.parse((root/n/'ledger-after.ndjson').read_bytes())))
    revision_rows = [r for r in rows if r['kind'] in ('activation', 'authorization_revision')]
    reservation_rows = [r for r in rows if r['kind'] == 'reservation']; terminal_rows = [r for r in rows if r['kind'] in ledger.TERMINAL]
    policy_digest = sha((ROOT/'policies'/POLICY).read_bytes())
    a.require(prefixes and [r['policy_sha256'] for r in revision_rows] == [policy_digest] and revision_rows[0]['kind'] == 'activation'
              and s['revisions'] == [policy_digest] and s['revision'] == 0
              and s['contract_sha256'] == contract_digest and s['open_reservations'] == [] and s['purpose'] == 'rehearsal'
              and sorted(r['row_hash'] for r in reservation_rows) == sorted(p['row_hash'] for p in permits.values())
              and sorted(r['row_hash'] for r in terminal_rows) == sorted(r['row_hash'] for r in reconciliations.values())
              and len(rows) == 1+2*len(reserved) and all(r['policy_sha256'] == policy_digest for r in reservation_rows)
              and revision_rows[0]['authorization'] == contract.REHEARSAL_AUTHORIZATION and not (ledgers/campaign/'live').exists(),
              'ledger:continuous_single_revision', str([r['kind'] for r in rows]))
    consumed = {f'{t}/{d}' for (k, t, d, _) in expected.values() if k in SENT}
    released = {f'{t}/{d}' for (k, t, d, _) in expected.values() if k == 'release'}
    committed = sum(priced[n] for n in priced if expected[n][0] in SENT)
    a.require({k for k, v in s['slots'].items() if v['consumed']} == consumed and s['transmissions_consumed'] == len(consumed)
              and {k for k, v in s['slots'].items() if v['released']} == released and all(s['slots'][k]['released'] == 1 for k in released)
              and s['committed_micro_usd'] == committed and s['maximum_transmissions'] == sum(contract.REHEARSAL_SCHEDULE.values()),
              'ledger:slots_match_population', str(s['slots']))
    refused = {t for (k, t, _, _) in expected.values() if k == 'interface_refused'}
    a.require(not any(r.get('task_id') in refused for r in rows) and not any((book.slots/t).exists() for t in refused)
              and not any(k.split('/')[0] in refused for k in s['slots']), 'ledger:no_rows_for_prereservation_refusals')
    return {'campaign_id': campaign, 'rows': len(rows), 'kinds': [r['kind'] for r in rows],
            'state': {k: s[k] for k in ('revision', 'revisions', 'transmissions_consumed', 'slots', 'committed_micro_usd')}}


# ---------------------------------------------------------------------------------------------------------------- history: cohort v4

def history_v4(a, v4_root, ledgers, expected_v6, v6_cases):
    """Bounded: the thirteen v4 runs as retained, what each recorded, and the v4 ledger's dispositions. Superseded, not invalid."""
    spec = HISTORY_V4; population = spec['expected']; result = {}
    present = sorted(p.name for p in v4_root.iterdir())
    a.require(present == sorted(population) and len(present) == 13, 'history_v4:population_exact', str(present))
    policy_path, lock_path = ROOT/'policies'/spec['policy'], ROOT/'policies'/spec['lock']; policy = load(policy_path)
    problems = []; rows_by = {}
    for n, (kind, site) in population.items():
        run = v4_root/n
        try:
            rows = events.read(run/'events.ndjson'); rows_by[n] = rows; s = load(run/'seal.json'); sp = load(run/'search-policy.json')
            files = {str(p.relative_to(run)) for p in run.rglob('*') if p.is_file()}
            if any(not (run/k).is_file() or sha((run/k).read_bytes()) != v for k, v in s['retained_sha256'].items()) \
                    or files-set(s['retained_sha256'])-set(s['ephemeral_sha256'])-{'seal.json'}: problems.append(f'{n}: seal hashes')
            if not (s['event_count'] == len(rows) and s['last_event_hash'] == rows[-1]['event_hash'] and s['accepted'] is (kind == 'proof')): problems.append(f'{n}: seal chain')
            if not all(r['task_id'] == site and r['run_id'] == rows[0]['run_id'] for r in rows): problems.append(f'{n}: identity')
            if rows[-1]['event'] != ('episode_finished' if kind == 'proof' else 'episode_rejected'): problems.append(f'{n}: terminal event')
            if not ((run/'provenance/cohort-harness/policies'/spec['policy']).read_bytes() == policy_path.read_bytes()
                    and (run/'provenance/cohort-harness/policies'/spec['lock']).read_bytes() == lock_path.read_bytes()
                    and sp['config_sha256'] == sha(policy_path.read_bytes()) and sp['name'] == spec['name'] and sp['task_id'] == site): problems.append(f'{n}: policy binding')
        except (ValueError, OSError, KeyError) as error: problems.append(f'{n}: {type(error).__name__}: {error}')
    a.require(not problems, 'history_v4:seals_and_chains', '; '.join(problems))
    problems = []; causes = {}
    for n, (kind, site) in population.items():
        run = v4_root/n; rows = rows_by[n]; path = run/'certificate-verdict.json'
        if kind in ('proof', 'reconstruction_guard', 'negative'):
            cert = load(path); event = [r['payload'] for r in rows if r['event'] == 'independent_certificate_verdict']
            record = load(ROOT/spec['representability']/site/'representability.json'); response = load(run/'response.json')
            if kind == 'negative': ok = cert['accepted'] is False and response['witness'] == {'coefficients': [{'hypothesis': 'neg_goal', 'coefficient': '1'}]}
            else: ok = cert['accepted'] is True and cert['reason']['kind'] == 'verified_farkas' and response['witness'] == {'coefficients': record['certificate']}
            if not (ok and event == [cert]): problems.append(n)
        elif path.exists(): problems.append(n+': unexpected certificate verdict')
    a.require(not problems, 'history_v4:verified_certificates', ', '.join(problems))
    problems = []
    for n, (kind, site) in population.items():
        run = v4_root/n; rows = rows_by[n]; summary = load(run/'credential-summary.json')
        log = b''.join((run/'stages/reconstruct'/f'reconstruct.{s}').read_bytes() for s in ('stdout', 'stderr') if (run/'stages/reconstruct'/f'reconstruct.{s}').exists())
        if kind == 'reconstruction_guard':
            children = [r for r in rows if r['source'] == 'child_report']; observed = {r['event']: r['payload']['data'] for r in children}
            packet = load(run/'evidence.json'); merged = merged_directives(observed['reification_finished']['ir'])
            process = load(run/'stages/reconstruct/reconstruct.process.json')
            failure_events = [r['payload'] for r in rows if r['event'] == 'stage_failure_recorded']
            ok = (GUARD.encode() in log and process['exit_code'] != 0 and [r['event'] for r in children] == ['reification_started', 'reification_finished', 'dispatch_started']
                  and failure_events == [{'category': 'stage_rejected', 'stage': 'reconstruct'}] and summary['failure_category'] == 'stage_rejected'
                  and summary['failure_phase'] == 'stage' and merged != packet['input_ir'] and not (run/'verdict.json').exists())
            differing = sorted(k for k in set(merged) | set(packet['input_ir']) if merged.get(k) != packet['input_ir'].get(k))
            names = lambda ir: [h['name'] for h in ir['context']['hypotheses']] + [v['name'] for v in ir['context']['free_vars']]
            causes[site] = {'differing_ir_fields': differing, 'directives_differ': merged.get('user_directives') != packet['input_ir'].get('user_directives'),
                            'names_differ': names(merged) != names(packet['input_ir'])}
            if not ok: problems.append(n)
        elif kind == 'proof':
            if not (GUARD.encode() not in log and load(run/'stages/reconstruct/reconstruct.process.json')['exit_code'] == 0 and summary['failure_category'] is None): problems.append(n)
        else:
            if (run/'stages/reconstruct').exists(): problems.append(n+': reconstructed')
            category = {'negative': 'certificate_verification', 'interface_refused': 'interface_refused', 'policy_refused': 'policy_refused', 'release': 'credential_format'}[kind]
            if summary['failure_category'] != category: problems.append(n+': '+str(summary['failure_category']))
            if kind == 'policy_refused' and [r['payload']['code'] for r in rows if r['event'] == 'request_refused'] != ['policy_ambiguous_reference']: problems.append(n+': refusal code')
    a.require(not problems and len(causes) == 5, 'history_v4:reconstruction_errors', ', '.join(problems))
    result['guard_causes'] = causes
    campaign = policy['campaign']['id']; book = ledger.Ledger(ledgers/campaign/'rehearsal', campaign); problems = []
    try:
        head = load(book.head); rows = ledger.parse(book.path.read_bytes()); s = ledger.state(rows, campaign)
        if not (head['rows'] == len(rows) and rows[-1]['row_hash'] == head['last_hash']): problems.append('head')
        reserved = {n for n, (k, _) in population.items() if k not in ('interface_refused', 'policy_refused')}
        by_episode = {}
        for r in rows:
            if r['kind'] in ('reservation', *ledger.TERMINAL): by_episode.setdefault(r['episode_id'], []).append(r)
        if set(by_episode) != reserved: problems.append(f'episodes {sorted(by_episode)}')
        for n in reserved:
            permit, terminal_row = by_episode[n][0], by_episode[n][-1]; kind = population[n][0]
            if not (len(by_episode[n]) == 2 and permit['kind'] == 'reservation' and terminal_row['kind'] == ('release' if kind == 'release' else 'send_grant')
                    and load(v4_root/n/'campaign-permit.json') == permit and load(v4_root/n/'campaign-reconciliation.json') == terminal_row):
                problems.append(n)
        if not (s['open_reservations'] == [] and s['transmissions_consumed'] == sum(k != 'release' for n, (k, _) in population.items() if n in reserved)
                and s['revisions'] == [sha(policy_path.read_bytes())]): problems.append('state')
        result['ledger'] = {'campaign_id': campaign, 'rows': len(rows), 'transmissions_consumed': s['transmissions_consumed']}
    except (ledger.Failure, OSError, KeyError) as error: problems.append(f'{type(error).__name__}: {error}')
    a.require(not problems, 'history_v4:ledger_dispositions', ', '.join(problems))
    repaired = sorted(site for (k, site) in population.values() if k in ('reconstruction_guard', 'policy_refused'))
    later = {t: (n, k) for n, (k, t, d, _) in expected_v6.items() if d == 1}
    # IR equality, from each v6 run's own case, whatever happened after it
    a.require(all(site in later and v6_cases.get(f'{later[site][0]}:reconstruction:preparation_ir_equal') is True for site in repaired),
              'history_v4:preparation_ir_equal_in_v6', str(repaired))
    outcomes = {}
    for site in repaired:
        n, k = later[site]
        if k == 'proof': ok = v6_cases.get(f'{n}:proof:certificate_consumed') is True and v6_cases.get(f'{n}:proof:original_declarations_validated') is True
        elif k == 'reconstruction_refused': ok = v6_cases.get(f'{n}:reconstruction:refusal_diagnosed') is True  # a later, different refusal: not the guard
        else: ok = False
        outcomes[site] = k if ok else f'{k} (unverified)'
    a.require(all(not v.endswith('(unverified)') for v in outcomes.values()) and len(outcomes) == 6, 'history_v4:later_outcomes_recorded_in_v6', str(outcomes))
    result.update(superseded=True, preparation_repaired=repaired, later_outcomes_in_v6=outcomes,
                  qualification='v4 is superseded (v5 supersedes it; v6 supersedes v5); its records are audited as retained, not as invalid')
    return result


def history_v5(a, v5_root, ledgers):
    """Bounded: the sixteen v5 runs as retained. l096/l099 are kernel successes whose consumption was never receipted: both replays
    accepted, the residual fold observed, no `reconstruction_finished` and no closer selection recorded — and none may appear. The four
    closer refusals were recorded as undifferentiated stage failures; the pinned closer's message is retained, the diagnosis is v6's."""
    spec = HISTORY_V5; population = spec['expected']; result = {}
    present = sorted(p.name for p in v5_root.iterdir())
    a.require(present == sorted(population) and len(present) == 16, 'history_v5:population_exact', str(present))
    policy_path, lock_path = ROOT/'policies'/spec['policy'], ROOT/'policies'/spec['lock']; policy = load(policy_path)
    problems = []; rows_by = {}
    for n, (kind, site) in population.items():
        run = v5_root/n
        try:
            rows = events.read(run/'events.ndjson'); rows_by[n] = rows; s_ = load(run/'seal.json'); sp = load(run/'search-policy.json')
            files = {str(p.relative_to(run)) for p in run.rglob('*') if p.is_file()}
            if any(not (run/k).is_file() or sha((run/k).read_bytes()) != v for k, v in s_['retained_sha256'].items()) \
                    or files-set(s_['retained_sha256'])-set(s_['ephemeral_sha256'])-{'seal.json'}: problems.append(f'{n}: seal hashes')
            accepted = kind in ('proof', 'kernel_success_unreceipted')
            if not (s_['event_count'] == len(rows) and s_['last_event_hash'] == rows[-1]['event_hash'] and s_['accepted'] is accepted): problems.append(f'{n}: seal chain')
            if not all(r['task_id'] == site and r['run_id'] == rows[0]['run_id'] for r in rows): problems.append(f'{n}: identity')
            if not ((run/'provenance/cohort-harness/policies'/spec['policy']).read_bytes() == policy_path.read_bytes()
                    and (run/'provenance/cohort-harness/policies'/spec['lock']).read_bytes() == lock_path.read_bytes()
                    and sp['config_sha256'] == sha(policy_path.read_bytes()) and sp['name'] == spec['name'] and sp['task_id'] == site): problems.append(f'{n}: policy binding')
        except (ValueError, OSError, KeyError) as error: problems.append(f'{n}: {type(error).__name__}: {error}')
    a.require(not problems, 'history_v5:seals_and_chains', '; '.join(problems))
    problems = []; qualified = {}
    for n, (kind, site) in population.items():
        rows = rows_by[n]; children = [r['event'] for r in rows if r['source'] == 'child_report']
        if 'closer_selected' in children: problems.append(n+': a v5 record carries a closer selection')
        if kind in ('proof', 'kernel_success_unreceipted'):
            verdict = load(v5_root/n/'verdict.json'); summary = load(v5_root/n/'credential-summary.json')
            replayed = all(verdict['final_validation'][k]['accepted'] is True for k in ('local', 'whole')) and summary['proof_accepted'] is True \
                       and all(v == {'added': [], 'removed': []} for v in verdict['axiom_delta'].values())
            receipted = 'reconstruction_finished' in children
            if kind == 'proof' and not (replayed and receipted): problems.append(n)
            if kind == 'kernel_success_unreceipted':
                if not (replayed and not receipted and children[-2:] == ['residual_started', 'residual_finished']): problems.append(n)
                qualified[site] = {'kernel_replays_accepted': replayed, 'consumption_receipt': False, 'residual_fold_observed': True,
                                   'qualification': 'kernel success; consumption not receipted by the v5 overlay; not a fully instrumented success'}
    a.require(not problems and len(qualified) == 2, 'history_v5:qualified_kernel_successes', ', '.join(problems))
    problems = []; refusals = {}
    for n, (kind, site) in population.items():
        if kind != 'closer_refused_undiagnosed': continue
        run = v5_root/n; rows = rows_by[n]; summary = load(run/'credential-summary.json')
        log = ''.join((run/'stages/reconstruct'/f'reconstruct.{x}').read_text() for x in ('stdout', 'stderr'))
        errors = [l for l in log.splitlines() if ': error: ' in l]
        observed = {r['event']: r['payload']['data'] for r in rows if r['source'] == 'child_report'}
        ok = (summary['failure_category'] == 'stage_rejected' and summary['failure_phase'] == 'stage' and len(errors) == 1 and driver.NAT_SHAPE_REFUSAL in errors[0]
              and GUARD not in log and observed['certificate_verification_finished']['ok'] is True
              and [r['event'] for r in rows if r['source'] == 'child_report'] == list(RECONSTRUCTED[:-1])
              and merged_directives(observed['reification_finished']['ir']) == load(run/'evidence.json')['input_ir'] == observed['dispatch_started']['ir'])
        if not ok: problems.append(n)
        refusals[site] = {'recorded_category': summary['failure_category'], 'guard_passed': GUARD not in log, 'certificate_verified': True,
                          'closer_message': errors[0][errors[0].index('proof_broker_term'):][:160] if errors else None,
                          'branch_evidence': False, 'diagnosed_in': REVISION}
    a.require(not problems and len(refusals) == 4, 'history_v5:closer_refusals_recorded', ', '.join(problems))
    campaign = policy['campaign']['id']; book = ledger.Ledger(ledgers/campaign/'rehearsal', campaign); problems = []
    try:
        head = load(book.head); rows = ledger.parse(book.path.read_bytes()); st = ledger.state(rows, campaign)
        if not (head['rows'] == len(rows) and rows[-1]['row_hash'] == head['last_hash']): problems.append('head')
        reserved = {n for n, (k, _) in population.items() if k != 'interface_refused'}
        by_episode = {}
        for r in rows:
            if r['kind'] in ('reservation', *ledger.TERMINAL): by_episode.setdefault(r['episode_id'], []).append(r)
        if set(by_episode) != reserved: problems.append(f'episodes {sorted(by_episode)}')
        for n in reserved & set(by_episode):
            permit, terminal_row = by_episode[n][0], by_episode[n][-1]; kind = population[n][0]
            if not (len(by_episode[n]) == 2 and permit['kind'] == 'reservation' and terminal_row['kind'] == ('release' if kind == 'release' else 'send_grant')
                    and load(v5_root/n/'campaign-permit.json') == permit and load(v5_root/n/'campaign-reconciliation.json') == terminal_row):
                problems.append(n)
        if not (st['open_reservations'] == [] and st['transmissions_consumed'] == sum(population[n][0] != 'release' for n in reserved)
                and st['revisions'] == [sha(policy_path.read_bytes())]): problems.append('state')
        result['ledger'] = {'campaign_id': campaign, 'rows': len(rows), 'transmissions_consumed': st['transmissions_consumed']}
    except (ledger.Failure, OSError, KeyError) as error: problems.append(f'{type(error).__name__}: {error}')
    a.require(not problems, 'history_v5:ledger_dispositions', ', '.join(problems))
    result.update(superseded=True, qualified_kernel_successes=qualified, closer_refusals=refusals,
                  qualification='v5 is superseded by v6 (policy supersedes field); audited as retained; no receipt is synthesized for it')
    return result


def strata(classes, expected, runs):
    """The report's denominators, each stated: fifteen primary sites; eleven posed; ten certificate-feasible; the negative control; the
    predeclared closer-reachable stratum; and the conditional six-positive-plus-negative-control diagnostic view (not a replacement population)."""
    feasible = sorted(classes['posable_certificate']); reachable = sorted(s for s in feasible if s not in RECONSTRUCTION_STRATUM)
    by_site = {r['task']: r for n, r in runs.items() if r['draw'] == 1}
    return {'primary': 15, 'posed': sorted(feasible+classes['posable_negative_control']), 'certificate_feasible': feasible,
            'negative_control': classes['posable_negative_control'], 'interface_refused': classes['interface_refused'],
            'closer_reachable': reachable, 'closer_unreachable': {s: RECONSTRUCTION_STRATUM[s] for s in sorted(RECONSTRUCTION_STRATUM)},
            'diagnostic_view': {'positives': reachable, 'negative_control': classes['posable_negative_control'], 'status': 'predeclared diagnostic, not a replacement population'},
            'outcomes': {s: {'kind': by_site[s]['kind'], 'closer': by_site[s]['closer'], 'diagnosis': by_site[s]['diagnosis']} for s in sorted(by_site)},
            'scope': 'canned witnesses; limitations of reconstruction are the pinned tactic\'s, per arm; certificate validity, consumption and kernel acceptance are separate cases'}


# ---------------------------------------------------------------------------------------------------------------- driver

def audit(root, ledgers, representability=None, v4_root=None, v5_root=None):
    representability = representability or ROOT/REPRESENTABILITY; v4_root = v4_root or ROOT/HISTORY_V4['runs']; v5_root = v5_root or ROOT/HISTORY_V5['runs']
    a = Audit(); result = {'runs': {}}
    classes = eligibility(a, representability)
    try: expected = derive_population(classes); derived = len({t for (_, t, _, _) in expected.values()}) == 15
    except ValueError as error: a.require(False, 'population:derived_from_eligibility', str(error))
    a.require(derived, 'population:derived_from_eligibility', 'the fifteen-site denominator is not covered')
    names = sorted(expected); present = sorted(p.name for p in root.iterdir())
    a.require(present == names and all((root/n).is_dir() for n in present), 'population:exactly_expected_runs', str(present))
    policy = load(ROOT/'policies'/POLICY)
    revision_bindings(a, root, expected, policy)
    contract_value = load(ROOT/CONTRACT_PATH); contract_digest = gate.check_contract(contract_value)
    tasks = {t: site_task.get(t) for t in sorted({t for (_, t, _, _) in expected.values()})}
    a.require(all(load(root/n/'search-policy.json')['manifest_sha256'] == sha((tasks[expected[n][1]].path/'manifest.json').read_bytes()) for n in names), 'tasks:manifests_bound')
    result['modules'] = modules(a, root, names)
    sp_by_run, bodies, sent, identities, permits, reconciliations, priced = {}, {}, {}, {}, {}, {}, {}
    for name in names:
        run = root/name; kind, task_id, draw, revision = expected[name]; task = tasks[task_id]
        sp, run_policy = versions(a, run, name, kind, task, draw, revision, contract_value, contract_digest); sp_by_run[name] = sp
        rows = chain(a, run, name, kind, task)
        frozen = site_identity(a, run, name, task, sp, run_policy)
        record = prepared_equals_classification(a, run, name, kind, task, representability)
        preparation_helper(a, run, name, task); original_context(a, run, name, kind, task)
        renamed = renaming(a, run, name, task, record)
        permit = reconciliation = http = None; request_bytes = body = None
        if kind != 'interface_refused':
            request_bytes, arguments, instruction, body, envelope = request(a, run, name, kind, sp, task, contract_value, contract_digest)
            admission = host_admission(a, run, name, run_policy, contract_value, instruction, request_bytes, arguments)
            book = ledger.Ledger(ledgers/sp['campaign_id']/'rehearsal', sp['campaign_id'])
            permit, reconciliation = ledger_rows(a, run, name, kind, sp, task, draw, revision, request_bytes, run_policy, admission, contract_digest, frozen)
            permits[name], reconciliations[name] = permit, reconciliation
            priced[name] = reservation_priced(a, run, name, run_policy, permit, admission, envelope)
            disposition(a, run, name, kind, permit, reconciliation, book); slot_contents(a, run, name, permit, reconciliation, book)
            layout_root = mounts(a, run, name, sp, task, draw, permit, book)
            command_reconstructed(a, run, name, sp, run_policy, task, draw, permit, load(run/'stages/proposal-1/output/http.json'), layout_root)
            receipts(a, run, name, rows, run_policy)
        s = seal(a, run, name); report, final = publication_recomputed(a, run, name)
        accepted = terminal(a, run, name, kind, rows, report, final)
        summary_bound(a, run, name, kind, task, draw, sp, contract_digest); chain_and_outcome(a, run, name, kind, rows, s, accepted)
        out = run/'stages/proposal-1/output'; http = load(out/'http.json') if (out/'http.json').exists() else None
        if kind != 'interface_refused':
            grant(a, run, name, kind, permit, http)
            serialized = transport(a, run, name, kind, run_policy, task, draw, permit, http, body, contract_digest)
            actor_check(a, run, name, run_policy, contract_value, instruction, request_bytes, arguments, permit, body)
            interpretation(a, run, name, request_bytes); commitment(a, run, name, http); slot_identity(a, run, name, sp, task, draw, permit, http, body)
            bodies.setdefault(task_id, {})[name] = serialized
            if kind in SENT: sent.setdefault(task_id, {})[name] = (out/'outbound-body.json').read_bytes()
            identities[name] = {'reservation_id': permit['reservation_id'], 'attempt_id': permit['attempt_id'], 'grant_id': http.get('grant_id'),
                                'commitment': http['credential_commitment_sha256'], 'nonce': http['commitment_nonce']}
        accounting(a, run, name, kind, run_policy, http, permit, reconciliation)
        payload_receipts(a, run, name, kind, rows, sp, task, permit, reconciliation, http, None, frozen)
        stage_outcomes(a, run, name, kind, run_policy)
        solution = closer = None
        if kind in SENT:
            response = response_bound(a, run, name, kind, request_bytes); attribution(a, run, name, kind, rows, sp)
            if kind == 'proof': solution, closer = proof(a, run, name, rows, task, sp, request_bytes, record, response, frozen)
            elif kind == 'reconstruction_refused':
                reconstruction_refused(a, run, name, rows, task, sp, request_bytes, record, response); closer = load(run/'reconstruction-refusal.json')['closer']
            else: negative(a, run, name, rows, record, response, request_bytes)
        elif kind == 'release': failure(a, run, name, http)
        else: interface_refused(a, run, name, rows, task, representability)
        result['runs'][name] = {'kind': kind, 'task': task_id, 'draw': draw, 'revision': revision, 'policy_sha256': sp['config_sha256'],
                                'ledger_outcome': reconciliation['kind'] if reconciliation else None, 'body_sha256': sha(body) if body else None,
                                'renamed': renamed, 'solution_sha256': solution, 'closer': closer,
                                'diagnosis': load(run/'reconstruction-refusal.json')['diagnosis'] if kind == 'reconstruction_refused' else None}
    result['campaign'] = cross_run(a, root, ledgers, expected, sp_by_run, policy, bodies, sent, identities, permits, reconciliations, priced, contract_digest)
    result['history_v4'] = history_v4(a, v4_root, ledgers, expected, a.cases)
    result['history_v5'] = history_v5(a, v5_root, ledgers)
    result['strata'] = strata(classes, expected, result['runs'])
    cases = expected_cases(expected)
    missing = sorted(set(cases)-set(a.cases)); extra = sorted(set(a.cases)-set(cases))
    if missing or extra or len(a.cases) != len(cases): raise Rejection('cases:population', f'missing {missing} extra {extra}')
    result.update(accepted=all(a.cases.values()) and len(a.cases) == len(cases), cases=a.cases, case_count=len(cases), revision=REVISION,
                  eligibility=classes, population={n: list(v) for n, v in expected.items()}, carried_forward=CARRIED_FORWARD,
                  contract_sha256=contract_digest, entity_body_sha256={t: sha(next(iter(g.values()))) for t, g in bodies.items()}, identities=identities,
                  live_model_calls=0, credentials_read=0, program_sha256=sha(Path(__file__).read_bytes()),
                  scope='audit over retained bytes, with the classification recomputed; no native execution, no inference')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runs', type=Path, default=ROOT/RUNS)
    parser.add_argument('--ledgers', type=Path, default=ROOT/'ledgers/campaigns')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output and args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    try: result = audit(args.runs.resolve(), args.ledgers.resolve())
    except Rejection as rejection:
        print(json.dumps({'accepted': False, 'rejected_case': rejection.case, 'detail': str(rejection)}, indent=1)); sys.exit(1)
    if args.output: r6.write_json(args.output, result)
    print(json.dumps({k: result[k] for k in ('accepted', 'case_count', 'revision', 'modules', 'strata', 'campaign', 'history_v4', 'history_v5')}, indent=1))
    sys.exit(0 if result['accepted'] else 1)


if __name__ == '__main__':
    main()
