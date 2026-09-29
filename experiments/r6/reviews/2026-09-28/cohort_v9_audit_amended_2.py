#!/usr/bin/env python3
"""R6-014 amendment 2 (post-collection): amendment 1's auditor (`reviews/2026-09-24/cohort_v9_audit_amended.py`, frozen by
`live-evaluation-v2` and retained byte-for-byte) with live pre-send releases and retried slots admitted, and nothing else changed.

Why and when: block 2 was collected under live-evaluation-v2 until it paused at l204 draw 6 (2026-09-28T23:34Z), a pre-send connection
failure the ledger released (`reviews/2026-09-28/R6-014-BLOCK2-PAUSE-1.md`, collection `ae1c8bbf`). Amendment 1's live mode fails closed on a
release (not among its reviewed live kinds) and refuses two runs for one slot, so no retry could ever be audited. The operator chose
"Amendment 2, then resume". Designed from the driver's and sender's code and exercised on synthetic evidence
(`fixtures/r6-014-v4-live-release`) before the collected release is read.

The amendment, each change stated:
* `LIVE_KINDS` gains `release`; `derive_live_population` classifies a run as a release when its ledger reconciliation is a release (read
  before the transport outcome, which a release shares with a provider error);
* `live_release` (in place of the rehearsal-only `failure`, which requires a credential-format release): the sender's connection-phase
  failure — one of the four categories `cohort_https.handoff` raises before the grant (`CONNECT_PHASE`) — agreed by the summary, the
  transport validation and the HTTPS record; one connection attempt, no verified TLS, no grant, zero header and body sends, no status, no
  response; the handled exception leaves exit 0 and an empty stderr; the pricing check admitted;
* the summary's failure category for a live release is its transport record's (`live_failure_category`), as for the other live failures;
* the case population: a live release evaluates the live transport case (`live_transport` runs for every reserved run in live mode);
* retried slots: a slot may hold attempts `<site>-draw<d>`, `<site>-draw<d>-attempt2`, … contiguously; every attempt but the last is a
  release; at most the reserving revision's `maximum_presend_attempts`; on the live ledger the attempts' reservations are in attempt order
  and the slot's `released` count equals its release runs. The frozen analysis already defines pre-send releases and exhaustion.

Amendment 1's docstring follows.

R6-014 amendment 1 (post-collection): the frozen cohort v9 auditor (`reviews/2026-09-23/cohort_v9_audit.py`, locked by
`policies/live-evaluation-v1.sha256.json` and retained byte-for-byte) with exactly one predicate amended.

Why and when: the frozen auditor was locked at ffab7cf4 (2026-09-24 10:34 +0200); block 1 was signed at c00247ed (10:56) and collected;
the frozen live audit then rejected it at `revision:history_bound` (6a361a3e, 11:12), because the check required the policy directory to
hold *only* the campaign's files. Every reviewed fixture had a dedicated directory; production signs into the shared `policies/`, beside
every earlier policy. The operator's decision (`reviews/2026-09-24/R6-014-AMENDMENT-1-DECISION.md`) treats this as a post-collection
amendment to the directory-layout check, not an unchanged preregistered evaluation.

The amendment (`campaign_files`): the campaign-owned file names are derived explicitly — the policy, its checkpoint, activation receipt,
progress floor and retained revisions (`<stem>.r<k>.json`, k < n), and the source lock, whose name (`cohort-harness-v9.sha256.json`) does
not share the policy's prefix. Every file in the directory that is campaign-specific (the policy's name or `<stem>.*`, the lock's name or
`<lock stem>.*`) must be exactly that expected set, and the complete set must be present; unrelated policies are ignored. Every other
predicate — content, revision chain, authorization, pricing, ledger and evidence — is the frozen auditor's, unchanged.

The frozen docstring follows.

R6-014 revision 3 auditor for cohort v9, in two modes. Non-locked; frozen with the live evaluation before any signature
(`policies/live-evaluation-v1.sha256.json`), only after review.

It is the revision 2 (cohort v8) auditor (`reviews/2026-09-23/cohort_v8_audit.py`, retained unchanged) with the R6-014 revision 2 review's
repairs:

* identity: revision `farkas_cohort_v9`, its runs, policy, lock and checkpoint; the supersession of v8;
* finding 1 — the progress floor (`<policy>.floor.json`) is one of the policy directory's records and equals the final live ledger's row
  count and last row hash;
* finding 2 — the stream coverage of every inventory entry is derived from the bytes the entry identifies, by the frozen scanner's own rule
  (`publication.scan_file`: a raw stream always, a gzip stream exactly when the bytes begin `1f 8b`), never from the file name; each entry's
  file must exist at its recorded digest and size; the aggregate gzip stream count must agree.

Revision 2 of this file (R6-014 revision 3 review, finding 2): an inventory path must be the scanner's own form — relative, normalized, no
`.`/`..`/empty component — and name a regular file reached through no symlink (the scanner reports symlinks as irregular and never follows
them) inside the declared scan root; anything else is rejected before any byte is read.

The revision 2 docstring follows, unchanged.

R6-014 revision 2 auditor for cohort v8, in two modes.

It is the R6-014 v7 auditor (`reviews/2026-09-23/cohort_v7_audit.py`, retained unchanged) carried to v8 with the R6-014 review's repairs:

* identity: revision `farkas_cohort_v8`, its runs, policy, lock and checkpoint; the supersession of v7;
* finding 2 — the production signing state: nothing reads the production policy directory for the audited policy (everything reads the
  configured layout); eligibility compares the *planned* design, never the execution schedule; a signed revision is its checkpoint but for
  its authority, schedule, money, revision chain and pricing, and each revision's pricing is bound to its own retained capture by the
  admission review recomputed (`pinned_admission`) and a capture age consistent with its approval; the revision history is every retained
  revision (`<policy>.r<n>.json`), chained, each a permitted successor (the same authority, or a larger scope under a later approval);
  each run is bound to the revision it was reserved under; the live ledger carries exactly those revisions in order, each reservation
  under the then-current one, and the activation receipt beside the policy names its activation row;
* finding 3 — the operator scan: cleanliness and completeness are reconstructed from every inventory entry (scanned, no error, no finding,
  every stream, no duplicate or unnamed entry, the counts), and the report's summary must agree.

The v7 docstring follows, unchanged.

R6-014 auditor for cohort v7 (the signing lifecycle), in two modes.

It is the R6-013 v6 auditor (`reviews/2026-09-22/cohort_v6_audit.py`, approved at revision 3, retained unchanged) carried to v7 by explicit
changes only, each stated here:

* identity: revision `farkas_cohort_v7`, runs, policy, lock; the supersession of v6 (same science, same site harness, a new campaign, the
  planned design recorded); the history checks of v4 and v5 unchanged;
* `--mode live` (reviewed before any signature, exercised on live-shaped canned evidence only):
  - the population is the runs present, each within the signed schedule, each run's kind derived from its own evidence among the reviewed
    live kinds (`LIVE_KINDS`: proof, reconstruction refused, witness rejected, response invalid, provider error); any other outcome
    (unknown send, pre-send release, refusal before reservation) fails closed, pending a reviewed revision that exercises it;
  - the signed policy is bound to its disabled checkpoint and differs from it only in its authority; the live ledger's activation and
    rows serve exactly that authority; the sender command is rebuilt in its live form (shared network, the resolver, the pinned public CA,
    an operator credential file outside the tree, no fixture);
  - transport, receipts, accounting, attribution and terminal records are checked in their live form: a use receipt, not an exact one;
    publication pending; nothing accepted until the operator scan binds;
  - a witness is checked by recomputation over the posed rows, never by equality with a canned certificate; a rejected witness must be
    invalid by that recomputation, and the negative control's rows admit no certificate at all;
  - the operator scan (`reviews/2026-09-13/operator_disclosure_scan.py`, run by the operator with the real credential) is bound: its full
    report is clean, carries the frozen commitment domain, was evaluated after every run finished, covers every file of every run and of
    the live ledger, and has one receipt per credential-bearing run whose four verdicts hold and whose digests are this run's bytes;
  - the audit emits the frozen analysis's input (`analysis_r6`, schema `r6-analysis-input-1`); the history checks are rehearsal-only.

Everything else is the v6 auditor's text, including its revision 1-3 repairs and the reviewed library inventory.
"""
import argparse
import copy
import difflib
import gzip
import hashlib
import inspect
import json
import os
from fractions import Fraction
from pathlib import Path
import stat
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
import provider_episode
import provider_payload
import publication
import run as r6
import consumption_overlay
import site_network
import site_representability as rep
import site_stage
import site_request
import site_task

REVISION = 'farkas_cohort_v9'
RUNS = 'cohort-runs-v9'
POLICY, LOCK = 'farkas-cohort-v9.json', 'cohort-harness-v9.sha256.json'
CHECKPOINT = 'farkas-cohort-v9.checkpoint.json'
ACTIVATION = 'farkas-cohort-v9.activation.json'
FLOOR = 'farkas-cohort-v9.floor.json'
SUPERSEDED = ('farkas-cohort-v8.json', 'cohort-harness-v8.sha256.json')
SUPERSEDES_REASON = ('v8 accepted a restored same-activation ledger snapshot and reset consumption (R6-014 revision 2 review, finding 1); revision 9 adds a '
                     'durable progress floor, with nothing model-visible changed')
HISTORY = {}  # revision number -> policy: every revision of the audited campaign (live), or the one disabled policy (rehearsal)
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
SENT = ('proof', 'negative', 'reconstruction_refused', 'witness_rejected', 'response_invalid', 'provider_error')
WITNESS_KINDS = ('proof', 'negative', 'reconstruction_refused', 'witness_rejected')  # a witness reached the independent checker
TERMINAL_KIND = {'proof': 'send_grant', 'negative': 'send_grant', 'reconstruction_refused': 'send_grant', 'release': 'release',
                 'witness_rejected': 'send_grant', 'response_invalid': 'send_grant', 'provider_error': 'send_grant'}
FAILURE_CATEGORY = {'proof': None, 'negative': 'certificate_verification', 'reconstruction_refused': 'reconstruction_refused',
                    'release': 'credential_format', 'interface_refused': 'interface_refused'}
ALLOWANCE = {'proof': 1, 'negative': 1, 'reconstruction_refused': 1, 'release': 0, 'interface_refused': None, 'witness_rejected': 1, 'response_invalid': 1, 'provider_error': 1}
FAILING_STAGE = {'negative': 'certificate-check', 'witness_rejected': 'certificate-check', 'interface_refused': 'pipeline-prepare', 'reconstruction_refused': 'reconstruct'}  # the one stage whose non-zero exit is the outcome
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
          'witness_rejected': (*PREPARATION_STAGES, 'proposal-1', 'assembly', 'certificate-check'),
          'response_invalid': (*PREPARATION_STAGES, 'proposal-1'), 'provider_error': (*PREPARATION_STAGES, 'proposal-1'),
          'proof': (*PREPARATION_STAGES, 'proposal-1', 'assembly', 'certificate-check', 'capture-build', 'reconstruct', 'export', 'validation-local', 'validation-whole')}
SENDER_PREFIX = ['bwrap', *network.NAMESPACES, '--unshare-net', '--die-with-parent', '--new-session', '--cap-drop', 'ALL',
                 '--clearenv', '--setenv', 'PATH', '/no-programs', '--setenv', 'LEAN_ABORT_ON_PANIC', '1',
                 '--symlink', 'usr/lib', '/lib', '--symlink', 'usr/lib64', '/lib64',
                 '--proc', '/proc', '--dev', '/dev', '--tmpfs', '/tmp', '--dir', '/work', '--chdir', '/work']
EPHEMERAL = ('/credential', '/ca.pem', '/server.pem', '/server.key')
LIVE_KINDS = ('proof', 'reconstruction_refused', 'witness_rejected', 'response_invalid', 'provider_error', 'release')  # amendment 2: release
CONNECT_PHASE = ('tls_certificate_verification', 'tls_protocol_failure', 'transport_timeout', 'transport_connection_failure')  # cohort_https.handoff, before the grant
MODE = 'rehearsal'
LAYOUT = {'policies': ROOT/'policies', 'ledger_prefix': 'ledgers/campaigns', 'operator_report': None, 'synthetic': False}


def configure(mode, runs=None, policies=None, ledger_prefix=None, operator_report=None, synthetic=False):
    """The mode and the recorded layout: where the runs, the policy files and the ledgers were recorded, relative to the repository."""
    global MODE, RUNS
    if mode not in ('rehearsal', 'live'): raise ValueError('mode')
    MODE = mode; RUNS = runs or RUNS
    LAYOUT.update(policies=Path(policies) if policies else ROOT/'policies', ledger_prefix=ledger_prefix or 'ledgers/campaigns',
                  operator_report=operator_report, synthetic=synthetic)


def purpose(): return 'live' if MODE == 'live' else 'rehearsal'
def authority(policy): return policy['authorization'] if MODE == 'live' else policy['campaign']['rehearsal_authorization']


def sequence(kind):
    """The expected event sequence: the rehearsal sequences, and in live mode the transport authorization after the reservation and a use
    receipt in place of the exact receipt."""
    if MODE != 'live': return SEQUENCES[kind]
    base = {'witness_rejected': 'negative', 'response_invalid': 'release', 'provider_error': 'release'}.get(kind, kind)
    seq = list(SEQUENCES[base]); seq.insert(seq.index(('supervisor', 'campaign-ledger', 'request_reserved'))+1, ('supervisor', 'proposal', 'live_transport_authorized'))
    return [('supervisor', 'credential-receipt', 'credential_use_checked') if x == RECEIPT[0] else x for x in seq]


SIGNED_FIELDS = ('live_enabled', 'authorization', 'live_model_calls_authorized', 'signed_from_checkpoint_sha256',
                 'revision', 'revision_reason', 'previous_policy_sha256', 'pricing_admission', 'pricing_sources')  # v8: bound by revision_history and revision_bindings


def signed_state_ok(policy):
    """Rehearsal: disabled, no authority. Live: signed, the authority well-formed, and the policy is its disabled checkpoint but for the authority,
    the authorized schedule and the matching money limit."""
    if MODE != 'live': return policy['live_enabled'] is False and policy['authorization'] is None
    try: ledger.authorization_scope(policy)
    except ledger.Failure: return False
    checkpoint_path = LAYOUT['policies']/CHECKPOINT
    if not checkpoint_path.is_file(): return False
    checkpoint = load(checkpoint_path)
    strip = lambda v: {k: (x if k not in ('campaign', 'limits') else {kk: xx for kk, xx in x.items() if kk not in ('schedule', 'total_micro_usd')})
                       for k, x in v.items() if k not in SIGNED_FIELDS}
    return (policy['signed_from_checkpoint_sha256'] == sha(checkpoint_path.read_bytes()) and checkpoint['live_enabled'] is False and checkpoint['authorization'] is None
            and strip(policy) == strip(checkpoint) and policy['limits']['total_micro_usd'] == contract.ATTEMPT_MICRO_USD*sum(policy['campaign']['schedule'].values())
            and policy['live_model_calls_authorized'] == sum(policy['campaign']['schedule'].values()) and within_plan(policy['campaign']['schedule']))


def within_plan(schedule):
    try: contract.within_plan(schedule)
    except ValueError: return False
    return True


def revision_history(a, policy):
    """Live: every retained revision of the signed campaign, from its first signature to the current policy, chained, each a permitted
    successor of the one before (the same authority, as a pricing revision, or a larger scope within the plan under a later approval), each
    its checkpoint but for the signed fields; the policy directory holds exactly the policy, its lock, checkpoint, activation receipt and
    retained revisions. Rehearsal: the one disabled policy."""
    if MODE != 'live': return {policy['revision']: policy}
    d = LAYOUT['policies']; problems = []; history = {}
    try:
        stem = POLICY.removesuffix('.json'); n = policy['revision']
        paths = {k: d/f'{stem}.r{k}.json' for k in range(1, n)} | {n: d/POLICY}
        history = {k: load(path) for k, path in paths.items()}
        expected, present = campaign_files(d, n)  # amendment 1: the campaign's own files, in a directory it may share
        if present != expected: problems.append(f'campaign files in the policy directory {present}, expected {expected}')
        checkpoint = load(d/CHECKPOINT)
        for k, value in history.items():
            if paths[k].read_bytes() != canonical(value)+b'\n' or value['revision'] != k or not signed_state_ok(value): problems.append(f'revision {k}: not a signed form of the checkpoint')
            if k == 1:
                if value['previous_policy_sha256'] != checkpoint['previous_policy_sha256'] or value['revision_reason'] is not None: problems.append('revision 1: chain')
                continue
            before = history[k-1]; now, then = value['authorization'], before['authorization']
            if value['previous_policy_sha256'] != sha(paths[k-1].read_bytes()) or not value['revision_reason']: problems.append(f'revision {k}: chain')
            same = now == then
            larger = (all(now['schedule'].get(t, 0) >= m for t, m in then['schedule'].items()) and now['schedule'] != then['schedule']
                      and contract.utc_unix(now['approved_utc']) > contract.utc_unix(then['approved_utc']))
            if not (same or larger): problems.append(f'revision {k}: neither the same authority nor a larger scope under a later approval')
    except (OSError, ValueError, KeyError, TypeError) as error: problems.append(f'{type(error).__name__}: {error}')
    a.require(not problems, 'revision:history_bound', '; '.join(problems))
    return history


def campaign_files(d, n):
    """Amendment 1. The expected campaign-owned names for revision n, and the campaign-specific names present: the policy's own name or its
    stem followed by a dot, and the source lock's own name or its stem followed by a dot. Anything else in the directory is unrelated."""
    stem, lock_stem = POLICY.removesuffix('.json'), LOCK.removesuffix('.sha256.json')
    expected = sorted([POLICY, LOCK, CHECKPOINT, ACTIVATION, FLOOR, *(f'{stem}.r{k}.json' for k in range(1, n))])
    owned = lambda name: name in (POLICY, LOCK) or name.startswith(stem+'.') or name.startswith(lock_stem+'.')
    return expected, sorted(x.name for x in d.iterdir() if owned(x.name))


def revision_of(run):
    """The revision a run was reserved under: its retained policy, which must be one of the campaign's revisions."""
    retained_policy = load(run/'provenance/cohort-harness/policies'/POLICY)
    return retained_policy if HISTORY.get(retained_policy.get('revision')) == retained_policy else None


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
                 'history_v4:later_outcomes_recorded_in_v6', 'history_v4:kernel_reports_bound',
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
    if MODE == 'live':
        names = ['eligibility:recomputed_fifteen_sites', 'revision:history_bound', 'population:derived_from_evidence', 'population:within_authorized_schedule',
                 'population:exactly_expected_runs', 'revision:superseded_v8_bound', 'revision:runtime_pricing_ledger_publication_bound', 'tasks:manifests_bound',
                 'modules:bound_to_retained_copies', 'modules:cohort_revision', 'campaign:single_identity', 'input:distinct_model_bytes_across_tasks',
                 'receipts:distinct_across_runs', 'ledger:continuous_across_revisions', 'ledger:slots_match_population', 'operator_scan:report_bound']
    else:
        names = ['eligibility:recomputed_fifteen_sites', 'population:derived_from_eligibility', 'population:exactly_expected_runs',
                 'revision:superseded_v8_bound', 'revision:runtime_pricing_ledger_publication_bound',
                 'tasks:manifests_bound', 'modules:bound_to_retained_copies', 'modules:cohort_revision', 'campaign:single_identity',
                 f'input:identical_model_bytes_across_draws:{RELEASE_RUN[1]}', 'input:distinct_model_bytes_across_tasks', 'receipts:distinct_across_runs',
                 'ledger:continuous_single_revision', 'ledger:slots_match_population', 'ledger:no_rows_for_prereservation_refusals', *HISTORY_CASES]
    for run, (kind, task, draw, revision) in expected.items():
        names += [f'{run}:versions:policy_lock_contract_campaign_bound', f'{run}:chain:valid', f'{run}:chain:expected_sequence',
                  f'{run}:site:identity_bound', f'{run}:site:prepared_equals_classification', f'{run}:site:preparation_is_the_repaired_helper',
                  f'{run}:site:original_context_bound', f'{run}:site:renaming_recorded',
                  f'{run}:seal:retained_hashes', f'{run}:publication:recomputed', f'{run}:terminal:commitments_bound',
                  f'{run}:summary:bound_to_audited_records', f'{run}:seal:chain_and_outcome', f'{run}:accounting:recomputed', f'{run}:credential_receipt:recorded',
                  f'{run}:receipts:payloads_bound_to_records', f'{run}:stages:every_stage_on_the_path_returned', f'{run}:stages:commands_reconstructed']
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
            names += [f'{run}:transport:local_send_and_remote_receipt', f'{run}:grant:ordered_before_first_header_byte']
        elif MODE == 'live' and kind == 'release':  # amendment 2: live transport is checked for every reserved run, the first unsent kind in live mode
            names += [f'{run}:transport:local_send_and_remote_receipt']
        if kind in WITNESS_KINDS:
            names += [f'{run}:{kind}:response_bound', f'{run}:{kind}:attribution_passed_through']
        if MODE == 'live':
            names += [f'{run}:operator_scan:receipt_bound']
        if kind in ('proof', 'reconstruction_refused'):
            names += [f'{run}:certificate:verified_and_bound', f'{run}:reconstruction:preparation_ir_equal', f'{run}:reconstruction:sources_bound',
                      f'{run}:reconstruction:evidence_bound',
                      f'{run}:reconstruction:closer_selected']
        if kind == 'proof':
            names += [f'{run}:proof:certificate_consumed', f'{run}:proof:shared_checker', f'{run}:proof:original_declarations_validated', f'{run}:proof:export_recorded']
        elif kind == 'reconstruction_refused':
            names += [f'{run}:reconstruction:refusal_diagnosed', f'{run}:reconstruction:no_completion_evidence']
        elif kind == 'negative':
            names += [f'{run}:negative:witness_is_the_canned_non_certificate', f'{run}:negative:verifier_rejected_and_stopped']
        elif kind == 'witness_rejected':
            names += [f'{run}:witness_rejected:recomputed_invalid_and_stopped']
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
        confirmation = contract.confirm_posable(); policy = load(LAYOUT['policies']/POLICY)  # v8: the configured layout, never the production file
        posable = sorted(recomputed['posable_certificate']+recomputed['posable_negative_control'])
        if not (policy['posable_confirmation'] == confirmation and confirmation['representability_sha256'] == sha((representability/'representability.json').read_bytes())
                and sorted(s for s, o in confirmation['outcome'].items() if o['posable']) == posable == sorted(contract.POSABLE)
                and sorted(s for s, o in confirmation['outcome'].items() if o['code'] == 'interface_refused') == sorted(recomputed['interface_refused'])
                and confirmation['denominator'] == 15 and policy['campaign']['planned_schedule'] == {s: contract.DRAWS for s in contract.POSABLE}):  # v8: the plan, not the execution scope
            problems.append('policy confirmation or POSABLE differs from the recomputed eligibility')
    except (ValueError, KeyError, OSError, site_request.Refusal, gate.Failure) as error:
        problems.append(type(error).__name__+': '+str(error)[:300])
    a.require(not problems, 'eligibility:recomputed_fifteen_sites', '; '.join(problems))
    return recomputed


# ---------------------------------------------------------------------------------------------------------------- revision bindings

def revision_bindings(a, root, expected, policy):
    """The revision's own supersession, runtime, pricing, ledger and publication, each bound to the bytes it names."""
    v4_policy = ROOT/'policies'/HISTORY_V4['policy']; v8_policy = ROOT/'policies'/SUPERSEDED[0]; v8_lock = ROOT/'policies'/SUPERSEDED[1]
    earlier = load(v8_policy)
    try: disabled = disabled_form(policy)
    except (OSError, ValueError) as error: a.require(False, 'revision:superseded_v8_bound', f'the signed policy\'s checkpoint: {type(error).__name__}')
    same_science = all(disabled[k] == earlier[k] for k in ('contract_sha256', 'pricing', 'pricing_admission', 'pricing_sources', 'request', 'model',
                                                          'runtime_lock_sha256', 'runtime_divergence', 'publication', 'attribution', 'posable_confirmation', 'site_lock_sha256')) \
                   and disabled['limits'] == earlier['limits'] and disabled['campaign']['schedule'] == earlier['campaign']['schedule']
    a.require(policy['name'] == REVISION == contract.NAME and disabled['revision'] == 1 and disabled['revision_reason'] is None
              and policy['supersedes'] == {'cohort_policy_sha256': sha(v8_policy.read_bytes()), 'cohort_lock_sha256': sha(v8_lock.read_bytes()),
                                           'reason': SUPERSEDES_REASON, 'contract_sha256': sha((ROOT/'contracts/farkas-proposal-contract-v1.json').read_bytes())}
              and earlier['supersedes']['cohort_policy_sha256'] == sha((ROOT/'policies/farkas-cohort-v7.json').read_bytes())
              and len({policy['campaign']['id'], earlier['campaign']['id'], load(v4_policy)['campaign']['id']}) == 3 and same_science
              and policy['campaign']['planned_schedule'] == contract.PLANNED and policy['campaign']['planned_micro_usd'] == contract.ATTEMPT_MICRO_USD*sum(contract.PLANNED.values())
              and policy['site_lock_sha256'] == sha((ROOT/'policies'/SITE_LOCK).read_bytes()),
              'revision:superseded_v8_bound')
    problems = []
    pin = ROOT/'policies'/(RUNTIME_PIN+'.json')
    if not (policy['runtime_lock_sha256'] == sha(pin.read_bytes()) and policy['runtime_divergence'] == contract.runtime_divergence()):
        problems.append('runtime pin or its recorded divergence')
    # v8: the checkpoint's capture is the reviewed capture 3; every revision's own capture is admitted by the recomputed review and its age
    captures = {}
    for number, revision_policy in sorted({**HISTORY, 0: disabled}.items()):
        capture = ROOT/revision_policy['pricing_sources']; captures[number] = capture
        try: review = contract.pinned_admission(capture)
        except (ValueError, OSError, KeyError) as error: review = None; problems.append(f'revision {number}: pricing review: {error}')
        if review is not None and not (revision_policy['pricing_admission'] == review and revision_policy['pricing_gate_sha256'] == sha((ROOT/'pricing_gate_v4.py').read_bytes())):
            problems.append(f'revision {number}: pricing admission or gate')
        if number == 0 and not (revision_policy['pricing_sources'] == PRICING_CAPTURE and (review or {}).get('source_review', {}).get('differing_extract_fields') == {'caching': [], 'model': ['snapshot_section']}):
            problems.append('checkpoint: not the reviewed capture')
        if number > 0 and MODE == 'live':
            rule = revision_policy['pricing_admission']; approved = contract.utc_unix(revision_policy['authorization']['approved_utc'])
            try: finished = [v['finished_unix'] for v in contract.v2.source_evidence(capture).values()]
            except (ValueError, OSError, KeyError) as error: finished = None; problems.append(f'revision {number}: capture evidence: {error}')
            if finished is not None and min(finished) < approved-rule['maximum_source_age_seconds']-rule['future_clock_tolerance_seconds']:
                problems.append(f'revision {number}: capture older than its approval allows')
    campaign = policy['campaign']['id']; directory = ROOT/LAYOUT['ledger_prefix']/campaign
    ledgers = sorted(p.name for p in directory.iterdir()) if directory.is_dir() else None
    if ledgers != (['live', 'rehearsal'] if MODE == 'live' else ['rehearsal']): problems.append(f'campaign ledger directory {ledgers}')
    site_lock = load(ROOT/'policies'/SITE_LOCK)
    if not (site_lock.get('consumption_overlay.py') == sha((ROOT/'consumption_overlay.py').read_bytes()) and consumption_overlay.REVISION == 2):
        problems.append('site lock does not bind the revision 2 overlay')
    for name in expected:
        run = root/name; sp = load(run/'search-policy.json')
        if not ((run/'provenance/cohort-harness/policies'/(RUNTIME_PIN+'.json')).read_bytes() == pin.read_bytes()
                and load(run/'provenance/roles.json')['runtime_pin'] == RUNTIME_PIN):
            problems.append(f'{name}: retained runtime pin')
        reserved_under = revision_of(run) if MODE == 'live' else HISTORY.get(1)
        capture = ROOT/reserved_under['pricing_sources'] if reserved_under else None
        if capture is None: problems.append(f'{name}: not reserved under a revision of this campaign')
        else:
            origin = sorted(p.name for p in (run/'pricing-origin').iterdir()); approved = sorted(p.name for p in capture.iterdir())
            if origin != approved or any((run/'pricing-origin'/f).read_bytes() != (capture/f).read_bytes() for f in origin):
                problems.append(f'{name}: pricing origin is not its revision\'s capture')
        if not (sp['ledger_path'] == f"{LAYOUT['ledger_prefix']}/{campaign}/{purpose()}/ledger.ndjson" and sp['campaign_id'] == campaign):
            problems.append(f'{name}: ledger binding')
        sources_record, patch = consumption_overlay.source_record()
        if not (load(run/'provenance/sources.json') == sources_record and (run/'provenance/instrumentation.patch').read_text() == patch):
            problems.append(f'{name}: bridge sources are not the revision 2 overlay')
        scan = load(run/'publication-scan.json')
        if scan.get('schema_version') != policy['publication']['scan_version'] or policy['publication'] != load(v4_policy)['publication']:
            problems.append(f'{name}: publication scan version')
    a.require(not problems, 'revision:runtime_pricing_ledger_publication_bound', '; '.join(problems))


def disabled_form(policy):
    """The disabled policy a signed one was made from (its checkpoint); a disabled policy is its own."""
    if policy.get('live_enabled') is not True: return policy
    return load(LAYOUT['policies']/CHECKPOINT)


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
              and HISTORY.get(policy.get('revision')) == policy and lock_path.read_bytes() == (LAYOUT['policies']/LOCK).read_bytes() == (ROOT/'policies'/LOCK).read_bytes()
              and sorted(lock) == sorted(contract.FILES) and all(lock[f] == sources[f] for f in files)
              and sp['name'] == policy['name'] == REVISION and sp['mode'] == MODE and sp['task_id'] == task.id and sp['draw'] == draw
              and sp['revision'] == policy['revision'] == revision and sp['campaign_id'] == campaign
              and sp['contract_sha256'] == policy['contract_sha256'] == contract_digest == sha(canonical(retained_contract)+b'\n')
              and retained_contract == contract_value and sp['manifest_sha256'] == sha((task.path/'manifest.json').read_bytes())
              and signed_state_ok(policy) and policy['prompt_sha256'] == contract_value['instruction']['sha256']
              and policy_path.read_bytes() == canonical(policy)+b'\n' and policy['campaign']['rehearsal_authorization'] == contract.REHEARSAL_AUTHORIZATION
              and sp['ledger_path'] == f"{LAYOUT['ledger_prefix']}/{campaign}/{purpose()}/ledger.ndjson" and sp['ledger_slots'] == f"{LAYOUT['ledger_prefix']}/{campaign}/{purpose()}/slots"
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
    a.require(observed == sequence(kind), f'{name}:chain:expected_sequence', f'{len(observed)} events')
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
        allowed = {'proof': ('posable_certificate',), 'reconstruction_refused': ('posable_certificate',), 'negative': ('posable_negative_control',),
                   'release': ('posable_certificate',)}.get(kind, ('posable_certificate', 'posable_negative_control'))  # live: any posed site can reject or fail
        if record['class'] not in allowed: problems.append('class')
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
              and before[0]['kind'] == 'activation' and before[0]['campaign_id'] == campaign and before[0]['purpose'] == purpose()
              and before[0]['authorization'] == authority(HISTORY[min(HISTORY)]) and s_before['authorization'] == authority(policy)
              and s_before['schedule'] == authority(policy)['schedule']
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
          and roles['ledger_directory'] == root+LAYOUT['ledger_prefix'] and roles['contract'] == root+CONTRACT_PATH
          and len(runtime) == 1 and roles['python'] in argv and command['records'] == run_dir+'/stages/proposal-1'
          and source('/out', '--bind') == command['records']+'/output' and source('/grant', '--ro-bind') is None and source('/ledger.ndjson', '--bind') is None
          and argv.count('--bind') == 2 and option('--task') == task.id and option('--draw') == str(draw) and option('--episode') == name
          and option('--contract') == '/contract.json' and option('--instruction') == '/instruction.txt' and option('--permit') == '/permit.json'
          and option('--ledger') == '/ledger.ndjson' and option('--grant') == '/grant' and option('--mode') == MODE)
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
    if MODE == 'live':  # the live sender: shared network, the resolver, the pinned public CA, the operator credential outside the tree, no fixture
        credential_source = source('/credential'); ca_path = str(Path(policy['tls']['public_ca_bundle']['path']).resolve())
        ephemeral_ok = (isinstance(credential_source, str) and credential_source.startswith('/') and not credential_source.startswith((root, run_dir))
                        and source('/ca.pem') == ca_path and sha(Path(ca_path).read_bytes()) == policy['tls']['public_ca_bundle']['sha256'])
        expected = ([x for x in SENDER_PREFIX if x != '--unshare-net'] + libraries + ['--ro-bind', network.RESOLVER, network.RESOLVER]
                    + ['--ro-bind', stdlib_source, pin['stdlib']] + modules_ + records + ['--ro-bind', root+sp['ledger_path'], '/ledger.ndjson']
                    + ['--ro-bind', credential_source or '', '/credential', '--ro-bind', ca_path, '/ca.pem']
                    + ['--ro-bind', pin['python'], '/runner/bin/program', '--bind', run_dir+'/stages/proposal-1/output', '/out',
                       '--bind', f"{root}{sp['ledger_slots']}/{task.id}/{draw}/{permit['reservation_id']}", '/grant', '/runner/bin/program',
                       '-I', '-S', '-B', '/adapter.py', '--mode', 'live', '--policy', '/policy.json', '--contract', '/contract.json', '--instruction', '/instruction.txt',
                       '--arguments', '/arguments.json', '--credential-file', '/credential', '--ca', '/ca.pem', '--out', '/out', '--request', '/request.json',
                       '--sources', '/pricing-sources', '--permit', '/permit.json', '--ledger', '/ledger.ndjson', '--episode', name, '--task', task.id, '--draw', str(draw),
                       '--grant', '/grant', '--commitment-nonce', http['commitment_nonce']])
        first = next((i for i, (x, y) in enumerate(zip(argv, expected)) if x != y), min(len(argv), len(expected)) if len(argv) != len(expected) else None)
        a.require(pinned and ephemeral_ok and argv == expected and command.get('network_namespace') == 'shared_with_host',
                  f'{name}:command:reconstructed_from_pinned_runtime_and_layout',
                  f'pinned {pinned}, ephemeral {ephemeral_ok}, first difference at {first}: {argv[first:first+3] if first is not None else None}')
        return
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
              and command['network_namespace'] == ('shared_with_host' if MODE == 'live' else 'unshared')
              and ('--unshare-net' in command['argv']) is (MODE != 'live') and '/grant' in command['argv'],
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


def stage_tools():
    """The pinned tools every site stage used: the D1 toolchain and environment and the revision 2 bridge, as `consumption_overlay.setup`
    assembles them, recomputed on this host. `run.build_tools` runs cached `lake build`s of the exporter and checker (no episode, no proof
    replay); the bridge paths are only named."""
    compiler, exporter, checker = r6.build_tools(task=r6.D1)
    mounts, lean_path, _ = r6.environment((ROOT.parents[1]/'lean-bridge/.lake/packages').resolve(), compiler, r6.D1)
    dest = consumption_overlay.DEST; native = dest/'bridge/.lake/build/lib/lean'
    modules = [native/f'r6_x2dproposal_ProofBroker_{m}.so' for m in BRIDGE_MODULES]
    ffi = dest/'sdk/_build/default/ffi/proof_broker_ffi.so'; glue = ROOT.parents[1]/'lean-bridge/.lake/build/lib/libpbglue.so'
    loads = ['--load-dynlib=/broker/lib/glue.so', '--load-dynlib=/broker/lib/ffi.so'] + [f'--load-dynlib=/broker/modules/{m.name}' for m in modules]
    return {'compiler': compiler, 'exporter': exporter, 'checker': checker, 'loads': loads, 'lean_path': lean_path+':/broker/modules',
            'mounts': [*mounts, (native, '/broker/modules'), (ffi, '/broker/lib/ffi.so'), (glue, '/broker/lib/glue.so')],
            'driver': dest/'sdk/_build/default/validate/proposal_driver.exe', 'verifier': dest/'sdk/_build/default/validate/verify_certificate.exe'}


def stage_specs(run, task, tools):
    """Each non-sender stage's (binary, argv, mounts, compiler?, env), exactly as `site_task.prepare`, `cohort_episode.consume` and
    `site_network.final_validation` pass them to `site_stage.stage`; `run` is the recorded run directory."""
    T = tools; lean = T['compiler']/'bin/lean'; out = lambda stage: run/'stages'/stage/'output'
    validation = lambda kind: (T['checker'], ['/challenge.ndjson', '/solution.ndjson', '/policy.json', '/out/verdict.json'],
                               [(None, '/challenge.ndjson'), (run/'stages/export/export.stdout', '/solution.ndjson'), (run/'validation-input'/kind/'policy.json', '/policy.json')], False, {})
    return {
        'preparation-build': (lean, [*T['loads'], '-R', '/input', '-o', '/out/PreparationCapture.olean', '/input/PreparationCapture.lean'],
                              [*T['mounts'], (run/'preparation-input', '/input')], True, {'LEAN_PATH': T['lean_path']+':/out'}),
        'preparation': (lean, [*T['loads'], '-R', '/input', '-o', '/out/Frozen.olean', '/input/Frozen.lean'],
                        [*T['mounts'], (run/'preparation-input', '/input'), (out('preparation-build'), '/capture')], True,
                        {'LEAN_PATH': T['lean_path']+':/capture', 'R6_CAPTURE_OUTPUT': '/out/context.json', 'R6_PREPARE_OUTPUT': '/out/reification.json'}),
        'pipeline-prepare': (T['driver'], ['prepare', '/input-ir.json', '/out/prepared.json'], [(run/'input-ir.json', '/input-ir.json')], False, {}),
        'assembly': (T['driver'], ['assemble', '/prepared.json', '/response.json', 'sha256:'+r6.sha(provider_episode.contract.CONFIG), '/out/evidence.json'],
                     [(run/'prepared.json', '/prepared.json'), (run/'validated-response.json', '/response.json')], False, {}),
        'certificate-check': (T['verifier'], ['/evidence.json', '/out/verdict.json'], [(run/'evidence.json', '/evidence.json')], False, {}),
        'capture-build': (lean, [*T['loads'], '-R', '/input', '-o', '/out/ProposalCapture.olean', '/input/ProposalCapture.lean'],
                          [*T['mounts'], (run/'input', '/input')], True, {'LEAN_PATH': T['lean_path']+':/out'}),
        'reconstruct': (lean, [*T['loads'], '-R', '/input', '-o', '/out/Frozen.olean', '/input/Frozen.lean'],
                        [*T['mounts'], (run/'input', '/input'), (out('capture-build'), '/capture'), (run/'evidence.json', '/evidence.json')], True,
                        {'LEAN_PATH': T['lean_path']+':/capture', 'R6_PROPOSAL_PACKET': '/evidence.json', 'PROOF_BROKER_EPISODE_TRACE': '1', 'R6_CAPTURE_OUTPUT': '/out/context.json'}),
        'export': (T['exporter'], ['Frozen', '--', task.whole, task.local, *r6.EXPORT_TARGETS], [*T['mounts'], (out('reconstruct'), '/objects'), (out('capture-build'), '/capture')],
                   True, {'LEAN_PATH': T['lean_path']+':/capture:/objects'}),
        'validation-local': validation('local'), 'validation-whole': validation('whole')}


SANDBOX = ['bwrap', '--unshare-all', '--die-with-parent', '--new-session', '--cap-drop', 'ALL',
           '--clearenv', '--setenv', 'PATH', '/no-programs', '--setenv', 'LEAN_ABORT_ON_PANIC', '1',
           '--symlink', 'usr/lib', '/lib', '--symlink', 'usr/lib64', '/lib64',
           '--proc', '/proc', '--dev', '/dev', '--tmpfs', '/tmp', '--dir', '/work', '--chdir', '/work']
LIBRARY_BLOCKS = {}
# The reviewed library inventory: every non-sender stage's (host, guest) library pairs, read from the stage commands of the commit that
# recorded the v6 runs and compared there with the pinned binaries' dependency closure (reviews/2026-09-23/library_inventory.py).
LIBRARY_INVENTORY = ROOT/'reviews/2026-09-23/R6-013-V3-LIBRARY-INVENTORY.json'
LIBRARY_INVENTORY_SHA256 = '562ad153446968c19434449f3fec4ab34f58e9166fe7f2aad45cf4b228e1bead'


def library_inventory():
    data = LIBRARY_INVENTORY.read_bytes()
    if sha(data) != LIBRARY_INVENTORY_SHA256: raise ValueError('library inventory differs from the reviewed one')
    return {stage: [tuple(pair) for pair in pairs] for stage, pairs in json.loads(data)['stages'].items()}


def contained(host, guest):
    """Lexical containment only: normalized absolute paths, the host under /usr/lib/, the guest under /usr/lib/ or /usr/lib64/."""
    import posixpath
    normal = lambda x: x.startswith('/') and posixpath.normpath(x) == x and '/../' not in x+'/' and '/./' not in x+'/'
    return normal(host) and normal(guest) and host.startswith('/usr/lib/') and guest.startswith(('/usr/lib/', '/usr/lib64/'))


def split_command(argv, stage, spec, tools, recorded_root, challenge=None):
    """The recorded command as (head equal, tail equal, library pairs) against the command `site_stage.stage` builds from `spec`."""
    binary, args, mounts, compiled, env = spec
    if challenge is not None: mounts = [(challenge, g) if h is None else (h, g) for h, g in mounts]
    compiler = tools['compiler'] if compiled else None
    head = list(SANDBOX)
    if compiler:
        head += ['--ro-bind', str(compiler/'lib'), '/toolchain/lib', '--ro-bind', str(compiler/'bin/lean'), '/toolchain/bin/lean',
                 '--setenv', 'LEAN_SYSROOT', '/toolchain', '--setenv', 'LD_LIBRARY_PATH', '/toolchain/lib/lean:/toolchain/lib']
    program = '/toolchain/bin/program' if compiler else '/runner/bin/program'
    tail = [x for host, guest in mounts for x in ('--ro-bind', str(Path(host).resolve()), guest)]
    tail += [x for k, v in env.items() for x in ('--setenv', k, v)]
    tail += ['--ro-bind', str(binary), program, '--bind', str(recorded_root/'stages'/stage/'output'), '/out', program, *args]
    middle = argv[len(head):len(argv)-len(tail)] if len(argv) >= len(head)+len(tail) else None
    pairs = None
    if middle is not None and len(middle) % 3 == 0 and all(middle[i] == '--ro-bind' for i in range(0, len(middle), 3)):
        pairs = [(middle[i+1], middle[i+2]) for i in range(0, len(middle), 3)]
    return argv[:len(head)] == head, argv[len(argv)-len(tail):] == tail, pairs


def stage_commands(a, run, name, kind, task, tools, root):
    """Every non-sender stage's recorded command, rebuilt as `site_stage.stage` builds it from that stage's call and compared exactly. The
    one host-dependent part, the shared-library closure, must be system libraries mounted at their own paths and equal for the same stage
    across runs; the challenge is a path claim only: both replays name one path of the driver's temporary pattern outside the recorded
    root, whose bytes were not retained."""
    problems = []; recorded_root = Path(root+RUNS)/name; challenge = {}
    specs = stage_specs(recorded_root, task, tools); inventory = library_inventory()
    for stage in sorted(p.name for p in (run/'stages').iterdir() if p.is_dir()):
        if stage == 'proposal-1': continue  # the sender: `command:reconstructed_from_pinned_runtime_and_layout`
        cmd = load(run/'stages'/stage/'command.json'); argv = cmd['argv']
        if stage not in specs or cmd['run'] != str(recorded_root) or cmd['stage'] != stage: problems.append(stage+': identity'); continue
        source = None
        if stage.startswith('validation-'):  # a path claim only: the temporary copy's bytes were not retained
            hits = [i for i, x in enumerate(argv) if x == '/challenge.ndjson' and argv[i-2] == '--ro-bind']
            source = Path(argv[hits[0]-1]) if len(hits) == 1 else None
            if source is None or source.name != 'challenge.ndjson' or not source.parent.name.startswith('r6-campaign-challenge-') or str(source).startswith(root):
                problems.append(stage+': challenge path'); continue
            challenge[stage] = source
        head_ok, tail_ok, pairs = split_command(argv, stage, specs[stage], tools, recorded_root, source)
        if not (head_ok and tail_ok and pairs is not None): problems.append(stage+': command differs from its rebuilt form'); continue
        if pairs != inventory.get(stage): problems.append(stage+': library pairs differ from the reviewed inventory')
        if not all(contained(h, g) for h, g in pairs): problems.append(stage+': a library mount is not contained in the system library directories')
        if LIBRARY_BLOCKS.setdefault(stage, pairs) != pairs: problems.append(stage+': library closure differs across runs')
    if len(set(challenge.values())) > 1: problems.append('the two replays read different challenge copies')
    a.require(not problems, f'{name}:stages:commands_reconstructed', '; '.join(problems))


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
    expect('episode', 'episode_started', {'policy_sha256': sha((run/'search-policy.json').read_bytes()), 'challenge_sha256': frozen['challenge_sha256'], 'nonce': nonce, 'mode': MODE})
    expect('credential-receipt', 'credential_use_checked' if MODE == 'live' else 'credential_receipt_checked', load(run/'credential-receipt.json'))
    if MODE == 'live' and kind != 'interface_refused':
        policy = load(run/'transport-policy.json')
        expect('proposal', 'live_transport_authorized', {'approved_by': policy['authorization']['approved_by'], 'approved_utc': policy['authorization']['approved_utc'],
            'ca_bundle_sha256': policy['tls']['public_ca_bundle']['sha256'], 'network_namespace': 'shared_with_host', 'reservation_id': permit['reservation_id'],
            'slot': {'task_id': task.id, 'draw': sp['draw']}, 'commitment_nonce': http['commitment_nonce'], 'credential_source': 'operator file; value never copied'})
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
    if kind in WITNESS_KINDS:
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
    if MODE == 'live':  # publication is pending the operator scan: nothing is accepted here, a proof still finishes
        publication_ok = None
    accepted = bool(summary['proof_accepted'] and summary['credential_use_accepted'] and publication_ok and evidence_ok)
    completed = summary['proof_accepted'] and summary['failure_category'] is None and (publication_ok is not False) and evidence_ok
    a.require(mirrors and last['summary_sha256'] == sha((run/'credential-summary.json').read_bytes())
              and last['publication_scan_sha256'] == sha((run/'publication-scan.json').read_bytes())
              and last['publication_final_sha256'] == sha((run/'publication-final.json').read_bytes())
              and last['proof_accepted'] is bool(summary['proof_accepted']) and last['credential_use_accepted'] is bool(summary['credential_use_accepted'])
              and last['publication_accepted'] is publication_ok and last['publication_pending'] is (MODE == 'live')
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
              and summary['failure_category'] == (live_failure_category(run) if kind in ('response_invalid', 'provider_error') or (MODE == 'live' and kind == 'release')
                                                  else FAILURE_CATEGORY.get(kind, 'certificate_verification')),
              f'{name}:summary:bound_to_audited_records', 'summary identity or embedded accounting differs from the audited records')


def chain_and_outcome(a, run, name, kind, rows, s, accepted):
    a.require(s['event_count'] == len(rows) and s['last_event_hash'] == rows[-1]['event_hash'] and s['accepted'] is accepted is (kind == 'proof' and MODE != 'live'),
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
    received_ok = (not (out/'received-body.json').exists()) if MODE == 'live' else ((out/'received-body.json').read_bytes() == body if sent else True)
    a.require(serialized == body and (not sent or ((out/'outbound-body.json').read_bytes() == body and received_ok
                                                   and http['outbound_body_sha256'] == sha(body))) and sent is (kind in SENT),
              f'{name}:transport:bodies_are_the_contract_rendering')
    a.require(http['schema_version'] == 'r6-cohort-observation-1' and http['mode'] == MODE and http['policy_sha256'] == sha((run/'transport-policy.json').read_bytes())
              and http['contract_sha256'] == contract_digest and http['task_id'] == task.id and http['draw'] == draw and http['slot'] == f'{task.id}/{draw}'
              and http['request_sha256'] == sha(serialized) and http['request_bytes'] == len(serialized) and http['retries'] == 0 and http['redirects_followed'] == 0
              and http['transport_scope'] == ('provider_request' if MODE == 'live' else 'isolated_loopback_https_fixture') and http['endpoint'] == policy['endpoint']
              and http['reservation_id'] == permit['reservation_id'] and http['authorization_present_in_policy'] is (True if MODE == 'live' else None)
              and http['maximum_response_bytes'] == policy['limits']['maximum_response_bytes'],
              f'{name}:transport:record_consistent')
    if MODE == 'live': return live_transport(a, run, name, kind, policy, http, server, body, serialized)
    if kind in SENT:
        nonce = load(run/'credential-canary.json')['nonce']; header = credential.header(credential.derive(nonce))
        a.require(http['http_status'] == 200 and http['body_sends_returned'] == 1 and http['body_sends_started'] == 1 and http['header_sends_started'] == 1
                  and len(server['requests']) == 1 and server['requests'][0]['body_sha256'] == sha(body)
                  and server['requests'][0]['authorization_sha256'] == sha(header.encode()) and server['server_names'] == [policy['endpoint']['host']]
                  and http['tls']['verified'] is True and http['tls']['server_hostname'] == policy['endpoint']['host']
                  and http['response_sha256'] == sha((out/'provider-response.json').read_bytes()),
                  f'{name}:transport:local_send_and_remote_receipt')
    return serialized


def live_transport(a, run, name, kind, policy, http, server, body, serialized):
    """The live transport record: no local receiver, the pinned public CA, verified TLS to the endpoint host, the response bound to its bytes;
    the remote receipt is unobservable in live mode and is not claimed."""
    out = run/'stages/proposal-1/output'
    ok = (http['fixture_tcp_port'] is None and server == {'requests': [], 'server_names': [], 'scope': 'no local receiver in live mode'}
          and http['ca_bundle_sha256'] == policy['tls']['public_ca_bundle']['sha256'])
    if kind in SENT:
        ok = ok and (http['body_sends_returned'] == 1 and http['body_sends_started'] == 1 and http['header_sends_started'] == 1 and http['tls']['verified'] is True
                     and http['tls']['server_hostname'] == policy['endpoint']['host'] and http['tls'].get('version') in ('TLSv1.2', 'TLSv1.3')
                     and http['response_sha256'] == sha((out/'provider-response.json').read_bytes()) and not (out/'received-body.json').exists()
                     and (kind == 'provider_error') is (http['http_status'] != 200))
    a.require(ok, f'{name}:transport:local_send_and_remote_receipt')
    return serialized


def live_failure_category(run):
    return load(run/'transport-validation.json').get('failure_category') or f"http_status_{load(run/'stages/proposal-1/output/http.json').get('http_status')}"


def commitment(a, run, name, http):
    nonce = load(run/'credential-canary.json')['nonce']; header = credential.header(credential.derive(nonce))
    expected = sha((COMMITMENT_DOMAIN+':'+http['commitment_nonce']+':'+header).encode())
    text = (run/'stages/proposal-1/output/http.json').read_text()
    if MODE == 'live':  # the value is bound to the operator's credential only by the operator scan (`operator_scan:*`)
        receipt = load(run/'credential-receipt.json'); recorded = http['credential_commitment_sha256']
        a.require(isinstance(recorded, str) and len(recorded) == 64 and all(c in '0123456789abcdef' for c in recorded) and 'Bearer' not in text
                  and receipt['credential_commitment_sha256'] == recorded and receipt['commitment_nonce'] == http['commitment_nonce'],
                  f'{name}:commitment:bound_to_mounted_canary'); return
    if http['failure_category'] == 'credential_format':
        a.require(http['credential_commitment_sha256'] is None and 'Bearer' not in text, f'{name}:commitment:bound_to_mounted_canary')
    else:
        a.require(http['credential_commitment_sha256'] == expected and credential.derive(nonce) not in text, f'{name}:commitment:bound_to_mounted_canary')


def interpretation(a, run, name, request_bytes):
    out = run/'stages/proposal-1/output'
    proposed, text, metadata, validation, error = budget.interpret(out, request_bytes, MODE == 'live')
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
    expected = driver.accounting_for(run, policy, MODE == 'live', http, server, lifecycle)
    a.require(acct == expected and acct['allowance_consumed'] == ALLOWANCE[kind], f'{name}:accounting:recomputed')
    if MODE == 'live':  # a use receipt: authenticated and processed, never a digest-matched receipt of a particular credential
        r = load(run/'credential-receipt.json'); status = None if http is None else http['http_status']
        a.require(r == {'schema_version': 'r6-campaign-credential-use-1', 'channel': 'operator_credential_file', 'http_status': status,
                        'credential_use_accepted': status is not None and 200 <= status < 300, 'exact_receipt': None,
                        'credential_commitment_sha256': None if http is None else http.get('credential_commitment_sha256'),
                        'commitment_nonce': None if http is None else http.get('commitment_nonce'), 'evidence_scope': r.get('evidence_scope')}
                  and isinstance(r.get('evidence_scope'), str), f'{name}:credential_receipt:recorded'); return
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


def live_release(a, run, name, http):
    """Amendment 2: a live pre-send release — the sender's connection-phase failure before its grant, nothing sent, the handled exception."""
    summary = load(run/'credential-summary.json'); validation = load(run/'transport-validation.json')
    stderr = (run/'stages/proposal-1/proposal-1.stderr').read_text(); process = load(run/'stages/proposal-1/proposal-1.process.json')
    tls = http.get('tls')
    a.require(http['failure_category'] in CONNECT_PHASE and summary['failure_category'] == validation['failure_category'] == http['failure_category']
              and summary['failure_phase'] == validation['failure_phase'] == 'https_transport' and validation.get('send_outcome') == http.get('send_outcome') == 'not_started'
              and http['connection_attempts'] == 1 and (tls is None or tls.get('verified') is not True) and http['grant_committed'] is False and not http.get('grant_id')
              and http['header_sends_started'] == 0 and http['body_sends_started'] == 0 and http['http_status'] is None and http.get('response_sha256') is None
              and process['exit_code'] == 0 and stderr == '' and load(run/'stages/proposal-1/output/pricing-check.json')['accepted'] is True
              and not (run/'response.json').exists() and (run/'seal.json').exists(), f'{name}:failure:classified_and_finalized')


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
        verdict_ok = verdict['witness_proposer'] == ('live_model_response' if MODE == 'live' else 'canned_provider_response') and verdict['consumer_route'] == 'openai_responses_http_fixture_v1' \
                     and verdict['certificate_assembler'] == 'sdk_proposal_assembler_v1'
    proposer = 'live_model_response' if MODE == 'live' else 'canned_provider_response'
    a.require(named == {'recovery_started': (proposer, sp['name'], None),
                        'certificate_assembled': (proposer, None, 'openai_responses_http_fixture_v1'),
                        'recovery_finished': (proposer, sp['name'], 'openai_responses_http_fixture_v1')}
              and assembled['certificate_assembler'] == 'sdk_proposal_assembler_v1' and verdict_ok,
              f'{name}:{kind}:attribution_passed_through', str(named))


def witness_rejected(a, run, name, rows, record, response, request_bytes):
    """Live: the proposed witness is invalid by recomputation over the posed rows, the independent checker rejected it, and the episode stopped
    before reconstruction. For the negative control the rows admit no certificate at all."""
    prepared = load(run/'prepared.json'); rows_ = prepared['rows']
    try: valid = rep.check_certificate(rows_, {c['hypothesis']: int(c['coefficient']) for c in response['witness'].get('coefficients', [])})
    except (rep.Ambiguous, KeyError, ValueError, TypeError): valid = False
    cert, evidence = load(run/'certificate-verdict.json'), load(run/'evidence.json'); summary = load(run/'credential-summary.json')
    finished = next(r['payload'] for r in rows if r['event'] == 'recovery_finished')
    negative_ok = record['class'] != 'posable_negative_control' or (rep.farkas(rows_) is None and record['arithmetic_certificate'] is False)
    a.require(valid is False and cert['accepted'] is False and finished['ok'] is False and evidence['certificate']['payload']['witness_data'] == response['witness']
              and response['request_sha256'] == sha(request_bytes) and not (run/'verdict.json').exists() and summary['failure_phase'] == 'certificate_verification'
              and negative_ok, f'{name}:witness_rejected:recomputed_invalid_and_stopped')


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


BRIDGE_MODULES = ('IR', 'Trace', 'Bridge', 'TermMode', 'Alethe', 'Tactic')


def no_extension_registered(run):
    """The pinned registry `reifierExt` starts empty and is set only by `ProofBrokerMathlib`: the reconstruction loads exactly the six core
    bridge modules and neither of its inputs imports the extension."""
    argv = load(run/'stages/reconstruct/command.json')['argv']
    loads = [x for x in argv if x.startswith('--load-dynlib=')]
    expected = ['--load-dynlib=/broker/lib/glue.so', '--load-dynlib=/broker/lib/ffi.so'] + [f'--load-dynlib=/broker/modules/r6_x2dproposal_ProofBroker_{m}.so' for m in BRIDGE_MODULES]
    imports = [l for f in ('input/Frozen.lean', 'input/ProposalCapture.lean') for l in (run/f).read_text().splitlines() if l.startswith('import ')]
    return loads == expected and not any('ProofBrokerMathlib' in l for l in imports)


def pinned_closer(ir, cert, extension=False):
    """`runTermModeOnGoal`'s branch at e627efe for this IR and certificate: `natModeOf` (a ℕ free variable or a `nat_nonlinear_atom` goal
    payload), then `polyModeOf` (type variables), then the case-split hint, then the extension's fragment, else the core ℤ closer. None
    where the pinned code throws before any closer (a case split over ℕ or α, or an extension path with no extension registered)."""
    payloads = ir['goal'].get('payloads') or {}
    nat = any(v.get('type') == 'Nat' for v in ir['context']['free_vars']) or \
          any(isinstance(v, dict) and v.get('kind') == 'nat_nonlinear_atom' for v in (payloads.values() if isinstance(payloads, dict) else ()))
    hint = ((cert.get('payload') or {}).get('strategy_hint')) or ''
    if nat: return None if hint == 'case_split_farkas' else 'term_mode_nat'
    if ir['context'].get('type_vars'): return None if (hint == 'case_split_farkas' or not extension) else 'term_mode_poly'
    if hint == 'case_split_farkas': return 'term_mode_case_split' if extension else None
    return 'term_mode_int'  # no extension: the core ℤ closer, whatever the fragment


def kernel_reports(task, verdict, path, read, receipt, frozen):
    """The retained raw replay reports, normalized as `final_validation` normalizes them, equal to the verdict and to both kernel receipts;
    each names the expected declaration, is accepted, keeps the frozen type and adds no axiom. Returns the problems found."""
    baseline = {t['name']: t for t in frozen['targets']}; problems = []; delta = {}
    for kind, target, config_policy in [('local', task.local, episode.local_policy(task)), ('whole', task.whole, r6.policy([task.whole], True, task=task))]:
        try:
            if read(f'validation-input/{kind}/policy.json') != config_policy: problems.append(kind+': validation policy'); continue
            with gzip.open(path(f'validation-{kind}.raw.json.gz'), 'rb') as f: raw = f.read(4*1024**2+1)
            report = json.loads(raw)
            if len(raw) > 4*1024**2 or len(report['targets']) != 1: problems.append(kind+': report shape'); continue
            t = report['targets'][0]; t['type_sha256'] = hashlib.sha256(t.pop('type_repr').encode()).hexdigest(); t['type_hash_format'] = 'Lean-4.32.2-reprStr-Expr-UTF8'
            if not (report['accepted'] is True and report['stage'] == 'complete' and report['kernel_version'] == '4.32.2' and report['local_proof_binding_checked'] is True
                    and report['checked_declarations'] > 0 and t['name'] == target and all(t[k] is True for k in ('declaration_exists', 'statement_and_dependencies_match', 'kernel_accepted'))
                    and t['type_sha256'] == baseline[target]['type_sha256'] and set(t['axioms']) <= set(r6.AXIOMS)):
                problems.append(kind+': report content')
            if not (report == verdict['final_validation'][kind] == receipt('validation-'+kind, 'kernel_verdict')): problems.append(kind+': report, verdict and receipt differ')
            delta[target] = {'added': sorted(set(t['axioms'])-set(baseline[target]['axioms'])), 'removed': sorted(set(baseline[target]['axioms'])-set(t['axioms']))}
        except (OSError, KeyError, ValueError, EOFError, gzip.BadGzipFile) as error: problems.append(f'{kind}: {type(error).__name__}: {error}')
    if verdict['axiom_delta'] != delta or any(v != {'added': [], 'removed': []} for v in delta.values()): problems.append('axiom delta')
    return problems


def receipts_of(rows):
    def receipt(stage, event):
        hits = [r['payload'] for r in rows if r['source'] == 'supervisor' and r['stage'] == stage and r['event'] == event]
        if len(hits) != 1: raise ValueError(f'{stage}/{event}: {len(hits)} receipts')
        return hits[0]
    return receipt


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
    delta = {}; digest = hashlib.sha256(); length = 0
    with gzip.open(path('solution.ndjson.gz'), 'rb') as f:
        while block := f.read(1024**2):
            length += len(block); require(length <= 256*1024**2, 'proof export exceeds budget'); digest.update(block)
    require(digest.hexdigest() == verdict['solution_sha256'], 'proof hash mismatch')
    problems = kernel_reports(task, verdict, path, read, receipt, expected)
    require(not problems, 'replay reports: '+', '.join(problems))


def record_task(record):
    return site_task.get(record['site_id'])


def reconstruction_common(a, run, name, rows, sp, request_bytes, record, response, kind):
    """What proof and refused reconstruction share, each stage its own case: the generated witness verified and bound to the classification's
    exact certificate; the IR reconstruction reified equal to the prepared one (the guard passed); one closer selected, for this certificate."""
    evidence, cert = load(run/'evidence.json'), load(run/'certificate-verdict.json')
    assembled = next(r['payload'] for r in rows if r['event'] == 'certificate_assembled')
    verdict_ok = True
    if kind == 'proof':
        verdict = load(run/'verdict.json')
        verdict_ok = (verdict['certificate_validation'] == cert and verdict['request_sha256'] == sha(request_bytes) and verdict['schema_version'] == 'r6-cohort-proof-1'
                      and verdict['search_policy'] == sp['name'] and verdict['mode'] == MODE)
    witness = record['certificate'] if MODE != 'live' else response['witness'].get('coefficients', [])
    try: valid = rep.check_certificate(load(run/'prepared.json')['rows'], {c['hypothesis']: int(c['coefficient']) for c in witness})
    except (rep.Ambiguous, KeyError, ValueError, TypeError): valid = False
    a.require((MODE == 'live' or response['witness'] == {'coefficients': record['certificate']}) and valid
              and evidence['certificate']['payload']['witness_data'] == response['witness'] and cert['accepted'] is True and cert['reason']['kind'] == 'verified_farkas'
              and cert['certificate_hash'] == 'sha256:'+assembled['certificate_sha256'] and assembled['response_sha256'] == sha((run/'validated-response.json').read_bytes())
              and load(run/'stages/assembly/output/evidence.json') == evidence and verdict_ok, f'{name}:certificate:verified_and_bound')
    observed = {r['event']: r['payload']['data'] for r in rows if r['source'] == 'child_report'}
    log = b''.join((run/'stages/reconstruct'/f'reconstruct.{s}').read_bytes() for s in ('stdout', 'stderr') if (run/'stages/reconstruct'/f'reconstruct.{s}').exists())
    reified, dispatched = observed['reification_finished']['ir'], observed['dispatch_started']['ir']
    a.require(merged_directives(reified) == evidence['input_ir'] == load(run/'input-ir.json') == load(run/'prepared.json')['input_ir'] == dispatched
              and GUARD.encode() not in log, f'{name}:reconstruction:preparation_ir_equal')
    # the reconstruction's inputs are the permitted extraction for this site, before any refusal is attributed or the extension registry is
    # read from imports (revision 3, review finding 1); neither a context output nor a receipt is required here
    pristine = site_task.census.pristine().decode(); problems = []
    for directory, helper, preparation in [('preparation-input', 'PreparationCapture', True), ('input', 'ProposalCapture', False)]:
        source = site_task.instrumented(record_task(record), helper, 'r6_prepare' if preparation else 'r6_capture_proposal')
        patch = ''.join(difflib.unified_diff(pristine.splitlines(True), source.splitlines(True), fromfile='Pristine.lean', tofile='Frozen.lean'))
        root_ = run/directory
        if sorted(p.name for p in root_.iterdir()) != ['Frozen.lean', f'{helper}.lean', 'source.patch']: problems.append(directory+': files')
        elif not ((root_/'Frozen.lean').read_text() == source and (root_/f'{helper}.lean').read_text() == site_task.capture_source(record_task(record), preparation)
                  and (root_/'source.patch').read_text() == patch): problems.append(directory+': contents')
    a.require(not problems, f'{name}:reconstruction:sources_bound', ', '.join(problems))
    # every observation the bridge made is bound to this run's packet, on the refused path as on the proof path (review finding 1)
    children = [r for r in rows if r['source'] == 'child_report']; cert = evidence['certificate']; problems = []  # evidence bindings
    start = next(r['sequence'] for r in rows if r['stage'] == 'reconstruct' and r['event'] == 'stage_started')
    finish = next(r['sequence'] for r in rows if r['stage'] == 'reconstruct' and r['event'] == 'stage_finished')
    if [r['event'] for r in children][:len(RECONSTRUCTED)] != list(RECONSTRUCTED): problems.append('observation sequence')
    if not all(start < r['sequence'] < finish and r['stage'] == 'reconstruct' and r['payload']['component'] == 'lean_bridge' for r in children): problems.append('child boundary')
    if not (observed['dispatch_started']['manifests'] == [] and observed['dispatch_started']['prefer_higher_tier'] is False): problems.append('dispatch settings')
    received = observed['dispatch_received']
    if not (received['certificate'] == cert and received['final_ir'] == evidence['final_ir'] and received['trace'] == evidence['trace']): problems.append('dispatch evidence')
    if evidence['final_ir'] != load(run/'prepared.json')['final_ir']: problems.append('packet final IR is not the prepared one')
    for event in ('certificate_verification_started', 'certificate_verification_finished', 'reconstruction_started', 'closer_selected', 'reconstruction_finished'):
        if event in observed and observed[event]['certificate'] != cert: problems.append('certificate at '+event)
    verification = observed['certificate_verification_finished']
    if not (verification['ok'] is True and verification['envelope_ok'] is True): problems.append('bridge verification')
    a.require(not problems, f'{name}:reconstruction:evidence_bound', ', '.join(problems))
    # the closer the pinned dispatch selects for this IR and certificate, derived, not read from the observations (review finding 2)
    selected = [r['payload']['data'] for r in children if r['event'] == 'closer_selected']
    extension = not no_extension_registered(run)
    derived = pinned_closer(dispatched, cert, extension)
    a.require(len(selected) == 1 and not extension and derived is not None and selected[0]['closer'] == derived and isinstance(selected[0]['goal'], str),
              f'{name}:reconstruction:closer_selected', f'derived {derived}, observed {selected}'[:300])
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
    policy_digest = sha((LAYOUT['policies']/POLICY).read_bytes())
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
    problems = []
    for n, (kind, site) in population.items():
        if kind != 'proof': continue
        run = v4_root/n; verdict = load(run/'verdict.json'); task = site_task.get(site)
        reports = kernel_reports(task, verdict, lambda f, r=run: r/f, lambda f, r=run: load(r/f), receipts_of(rows_by[n]), site_task.frozen_site(task)[1])
        proved = next((r['payload'] for r in rows_by[n] if r['event'] == 'proof_validated'), None)
        if reports or verdict['task_id'] != site or proved != {'verdict_sha256': sha((run/'verdict.json').read_bytes()), 'proof_accepted': True, 'solution_sha256': verdict['solution_sha256']}:
            problems.append(f'{n}: '+', '.join(reports or ['verdict identity or receipt']))
    a.require(not problems, 'history_v4:kernel_reports_bound', '; '.join(problems))
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
            verdict = load(v5_root/n/'verdict.json'); summary = load(v5_root/n/'credential-summary.json'); task = site_task.get(site)
            reports = kernel_reports(task, verdict, lambda f, r=v5_root/n: r/f, lambda f, r=v5_root/n: load(r/f), receipts_of(rows), site_task.frozen_site(task)[1])
            proved = next((r['payload'] for r in rows if r['event'] == 'proof_validated'), None)
            replayed = not reports and summary['proof_accepted'] is True and verdict['task_id'] == site and verdict['local_obligation_closed'] is True \
                       and verdict['whole_declaration_validated'] is True and proved == {'verdict_sha256': sha((v5_root/n/'verdict.json').read_bytes()),
                                                                                         'proof_accepted': True, 'solution_sha256': verdict['solution_sha256']}
            if reports: problems.append(f'{n}: '+', '.join(reports))
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


def derive_live_population(a, root, policy):
    """Live: each run's kind from its own evidence, among the reviewed live kinds; one run per signed slot. Anything else fails closed."""
    expected, problems = {}, []
    for run in sorted(p for p in root.iterdir() if p.is_dir()):
        kind = None
        try:
            sp = load(run/'search-policy.json'); summary = load(run/'credential-summary.json'); category = summary['failure_category']
            http_path = run/'stages/proposal-1/output/http.json'
            reconciliation = load(run/'campaign-reconciliation.json') if (run/'campaign-reconciliation.json').exists() else {}
            if reconciliation.get('kind') == 'release' and http_path.exists() and category is not None: kind = 'release'  # amendment 2, read first
            elif category is None and summary['proof_accepted'] is True: kind = 'proof'
            elif category == 'reconstruction_refused': kind = 'reconstruction_refused'
            elif category == 'certificate_verification': kind = 'witness_rejected'
            elif (run/'transport-validation.json').exists() and http_path.exists() and category == live_failure_category(run):
                kind = 'provider_error' if load(http_path)['http_status'] != 200 else 'response_invalid'
        except (OSError, KeyError, ValueError): kind = None
        if kind is None: problems.append(f'{run.name}: an outcome this revision has not reviewed for live audit'); continue
        expected[run.name] = (kind, sp['task_id'], sp['draw'], sp['revision'])
    a.require(not problems and bool(expected), 'population:derived_from_evidence', '; '.join(problems))
    schedule = lambda revision: (HISTORY.get(revision) or {'campaign': {'schedule': {}}})['campaign']['schedule']  # v8: the revision it was reserved under
    a.require(all(t in schedule(r) and 1 <= d <= schedule(r)[t] for (_, t, d, r) in expected.values()) and slot_attempts_ok(expected),
              'population:within_authorized_schedule', str(sorted((t, d) for (_, t, d, _) in expected.values())))
    return expected


def slot_attempts(expected):
    """Amendment 2: the runs of each slot, in attempt order."""
    slots = {}
    for name, (kind, t, d, r) in expected.items(): slots.setdefault((t, d), []).append(name)
    order = lambda name: int(name.rsplit('-attempt', 1)[1]) if '-attempt' in name else 1
    return {slot: sorted(names, key=order) for slot, names in slots.items()}


def slot_attempts_ok(expected):
    """Amendment 2: each slot's runs are its first attempt and contiguous retries, every one but the last a release, within the reserving
    revision's pre-send limit."""
    for (t, d), names in slot_attempts(expected).items():
        base = run_name(t, d); limit = min(HISTORY[expected[n][3]]['limits']['maximum_presend_attempts'] for n in names)
        if names != [base]+[f'{base}-attempt{k}' for k in range(2, len(names)+1)] or len(names) > limit: return False
        if any(expected[n][0] != 'release' for n in names[:-1]): return False
    return True


def live_failure(a, run, name, kind, http):
    """A sent request whose answer failed transport validation (or a non-200 status): classified from the validation record, nothing downstream."""
    summary = load(run/'credential-summary.json'); validation = load(run/'transport-validation.json')
    a.require(summary['failure_category'] == live_failure_category(run) and (validation.get('failure_category') is not None or kind == 'provider_error')
              and not (run/'stages/assembly').exists() and not (run/'verdict.json').exists() and (run/'seal.json').exists(),
              f'{name}:failure:classified_and_finalized')


def cross_run_live(a, root, ledgers, expected, sp_by_run, policy, bodies, identities, permits, reconciliations, priced, contract_digest):
    names = sorted(expected); campaign = policy['campaign']['id']
    a.require({sp['campaign_id'] for sp in sp_by_run.values()} == {campaign}, 'campaign:single_identity')
    per_task = {t: {sha(b) for b in g.values()} for t, g in bodies.items()}
    a.require(all(len(v) == 1 for v in per_task.values()) and len({next(iter(v)) for v in per_task.values()}) == len(per_task), 'input:distinct_model_bytes_across_tasks', str(per_task))
    ids = [v['reservation_id'] for v in identities.values()]; grants = [v['grant_id'] for v in identities.values() if v['grant_id']]
    nonces = [v['nonce'] for v in identities.values()]; attempts = [v['attempt_id'] for v in identities.values()]
    canaries = [load(root/n/'credential-canary.json')['nonce'] for n in names]
    a.require(all(len(set(x)) == len(x) for x in (ids, grants, nonces, attempts, canaries)) and len(grants) == sum(k in SENT for (k, *_) in expected.values()),
              'receipts:distinct_across_runs')
    book = ledger.Ledger(ledgers/campaign/'live', campaign); digests = [sha(canonical(HISTORY[k])+b'\n') for k in sorted(HISTORY)]
    try:
        head = load(book.head); rows = ledger.parse(book.path.read_bytes()); s = ledger.state(rows, campaign)
        if not (head['rows'] == len(rows) and rows[-1]['row_hash'] == head['last_hash'] and head['campaign_id'] == campaign): raise ledger.Failure('cohort_ledger_head')
    except (ledger.Failure, OSError) as error: a.require(False, 'ledger:continuous_single_revision', str(error))
    prefixes = all(rows[:len(snap)] == snap for n in names for snap in (ledger.parse((root/n/'transport-ledger.ndjson').read_bytes()), ledger.parse((root/n/'ledger-after.ndjson').read_bytes())))
    reservation_rows = [r for r in rows if r['kind'] == 'reservation']; terminal_rows = [r for r in rows if r['kind'] in ledger.TERMINAL]
    revision_rows = [r for r in rows if r['kind'] in ('activation', 'authorization_revision')]
    under_current = all(r['policy_sha256'] == ledger.state(rows[:i], campaign)['policy_sha256'] for i, r in enumerate(rows) if r['kind'] == 'reservation')
    revisions_bound = [r['policy_sha256'] for r in revision_rows] == digests and all(r['authorization'] == HISTORY[k]['authorization'] for r, k in zip(revision_rows, sorted(HISTORY)))
    try: receipt_ok = load(LAYOUT['policies']/ACTIVATION) == book.receipt_record(rows[0]) and load(LAYOUT['policies']/FLOOR) == book.floor_record(len(rows), rows[-1]['row_hash'])
    except (OSError, ValueError, KeyError): receipt_ok = False  # v9: the receipt names the activation row; the floor is the final ledger's progress
    a.require(prefixes and rows[0]['kind'] == 'activation' and rows[0]['purpose'] == 'live' and revisions_bound and under_current and receipt_ok
              and s['revisions'] == digests and s['authorization'] == policy['authorization'] and s['open_reservations'] == []
              and sorted(r['row_hash'] for r in reservation_rows) == sorted(p['row_hash'] for p in permits.values())
              and sorted(r['row_hash'] for r in terminal_rows) == sorted(r['row_hash'] for r in reconciliations.values())
              and len(rows) == len(revision_rows)+2*len(names),
              'ledger:continuous_across_revisions', str([r['kind'] for r in rows]))
    consumed = {f'{t}/{d}' for (k, t, d, _) in expected.values() if k in SENT}
    # amendment 2: each slot's released count is its release runs, and its attempts reserved on the ledger in attempt order
    order = {r['reservation_id']: i for i, r in enumerate(rows) if r['kind'] == 'reservation'}
    attempts_ok = all(s['slots'].get(f'{t}/{d}', {}).get('released') == sum(expected[n][0] == 'release' for n in ns)
                      and [order.get(permits[n]['reservation_id']) for n in ns] == sorted(order.get(permits[n]['reservation_id'], -1) for n in ns)
                      for (t, d), ns in slot_attempts(expected).items())
    a.require({k for k, v in s['slots'].items() if v['consumed']} == consumed and s['transmissions_consumed'] == len(consumed) and attempts_ok
              and s['maximum_transmissions'] == sum(policy['campaign']['schedule'].values()) and s['maximum_micro_usd'] == policy['limits']['total_micro_usd']
              and s['committed_micro_usd'] == sum(priced[n] for n in names if expected[n][0] in SENT) <= policy['limits']['total_micro_usd'],
              'ledger:slots_match_population', str(s['slots']))
    return {'campaign_id': campaign, 'rows': len(rows), 'state': {k: s[k] for k in ('transmissions_consumed', 'maximum_transmissions', 'committed_micro_usd', 'maximum_micro_usd', 'slots')}}


def operator_scan(a, root, ledgers, expected, policy):
    """The operator's disclosure scan with the real credential, bound: its report clean and complete, after every run, over every file."""
    report_path = LAYOUT['operator_report']; problems = []; receipts = {}
    try:
        report = load(report_path); scan = report['operator_scan']; scan_root = Path(LAYOUT['scan_root'])
        if not (report['accepted'] is True and report['disclosures'] == [] and report['unreadable_directories'] == [] and report['irregular_entries'] == []
                and report['incompletely_scanned'] == [] and all(report['per_root_accepted']) and len(report['per_root_accepted']) == 1):
            problems.append('report not clean')
        if not (scan['commitment_domain'] == COMMITMENT_DOMAIN and scan['credential_value_retained'] is False): problems.append('commitment domain')
        finished = max(events.read(root/n/'events.ndjson')[-1]['receipt_utc'] for n in expected)
        from datetime import datetime
        if scan['evaluated_at_unix'] < datetime.fromisoformat(finished.replace('Z', '+00:00')).timestamp(): problems.append('scanned before the runs finished')
        entries = report['inventory']; paths = [e.get('path') for e in entries]
        if None in paths or len(paths) != len(set(paths)): problems.append('unnamed or duplicate inventory entries')
        def contained(relative):  # revision 2: the declared boundary, checked before any read
            if not isinstance(relative, str) or not relative or relative.startswith('/') or '\\' in relative or '\x00' in relative: return None
            parts = relative.split('/')
            if any(part in ('', '.', '..') for part in parts): return None
            here = scan_root
            try:
                if stat.S_ISLNK(os.lstat(here).st_mode): return None
                for part in parts:
                    here = here/part; mode = os.lstat(here).st_mode
                    if stat.S_ISLNK(mode): return None
                if not stat.S_ISREG(mode): return None
            except OSError: return None
            real, root_real = os.path.realpath(here), os.path.realpath(scan_root)
            return here if real.startswith(root_real+os.sep) else None
        def streams_from_bytes(entry):  # v9: the frozen scanner's rule (`publication.scan_file`), applied to the bytes the entry names
            path = contained(entry.get('path'))
            if path is None: return None
            data = path.read_bytes()
            if sha(data) != entry.get('sha256') or len(data) != entry.get('bytes'): return None
            return ['raw', 'gzip'] if data[:2] == b'\x1f\x8b' else ['raw']
        unclean = [e.get('path') for e in entries if not (e.get('scanned') is True and e.get('error') is None and e.get('findings') == [] and e.get('root_index') == 0
                                                          and isinstance(e.get('path'), str) and e.get('streams') == streams_from_bytes(e))]
        if unclean: problems.append(f'{len(unclean)} entries not cleanly scanned, with findings, or not their bytes\' streams, e.g. {unclean[:2]}')
        if (report['files_scanned'] != len(entries) or report['extra_canary_count'] != 0 or report['exempted_files'] != []
                or report['gzip_streams_scanned'] != sum('gzip' in e.get('streams', []) for e in entries)): problems.append('counts')
        inventory = {e['path']: e['sha256'] for e in report['inventory'] if e['path']}
        files = [p for n in expected for p in (root/n).rglob('*') if p.is_file()] + [p for p in (ledgers/policy['campaign']['id']/'live').rglob('*') if p.is_file()]
        uncovered = [str(p) for p in files if inventory.get(str(p.relative_to(scan_root))) != sha(p.read_bytes())]
        if uncovered: problems.append(f'{len(uncovered)} files not covered at their digests, e.g. {uncovered[:2]}')
        for receipt in scan['run_receipts']: receipts.setdefault(receipt['run']['name_sha256'], []).append(receipt)
    except (OSError, KeyError, ValueError, TypeError) as error: problems.append(f'{type(error).__name__}: {error}')
    a.require(not problems, 'operator_scan:report_bound', '; '.join(problems))
    bound = {}
    for n in expected:
        run = root/n; http_path = run/'stages/proposal-1/output/http.json'; http = load(http_path) if http_path.exists() else {}
        hits = receipts.get(sha(n.encode()), [])
        if http.get('credential_commitment_sha256') is None:
            ok = not hits
        else:
            r = hits[0] if len(hits) == 1 else {}
            ok = (len(hits) == 1 and r['covered_by_scan'] is True and r['sealed_and_intact'] is True and r['commitment_record_sealed'] is True and r['commitment_bound'] is True
                  and r['read_failures'] == 0 and r['recorded_commitment_sha256'] == http['credential_commitment_sha256'] and r['commitment_nonce'] == http['commitment_nonce']
                  and r['seal_sha256'] == sha((run/'seal.json').read_bytes()) and r['http_sha256'] == sha(http_path.read_bytes()))
        a.require(ok, f'{n}:operator_scan:receipt_bound'); bound[n] = bool(hits)
    return {'report_sha256': sha(Path(report_path).read_bytes()), 'receipts_bound': bound}


def analysis_input(root, expected, policy, ledgers, scan_bound):
    """The frozen analysis's input, from audited records only; an unobserved fact is None."""
    campaign = policy['campaign']['id']; _, s = ledger.Ledger(ledgers/campaign/'live', campaign).snapshot(); slots = {}
    for n, (kind, task_id, draw, _) in sorted(expected.items()):
        run = root/n; permit = load(run/'campaign-permit.json'); reconciliation = load(run/'campaign-reconciliation.json')
        http = load(run/'stages/proposal-1/output/http.json'); acct = load(run/'accounting.json')
        response = load(run/'response.json') if (run/'response.json').exists() and kind in WITNESS_KINDS else None
        cert = load(run/'certificate-verdict.json') if kind in WITNESS_KINDS else None; verdict = load(run/'verdict.json') if kind == 'proof' else None
        refusal = load(run/'reconstruction-refusal.json') if kind == 'reconstruction_refused' else None
        usage = acct.get('usage') or {}
        slots[f'{task_id}/{draw}'] = {'task_id': task_id, 'draw': draw,
            'ledger': {'disposition': reconciliation['kind'], 'presend_attempts': s['slots'][f'{task_id}/{draw}']['released'], 'maximum_presend_attempts': policy['limits']['maximum_presend_attempts'],
                       'reserved_micro_usd': permit['reserved_micro_usd']},
            'transport': {'response_received': http['http_status'] is not None, 'failure_category': http['failure_category']},
            'witness': {'present': response is not None, 'coefficients': (response or {}).get('witness', {}).get('coefficients')},
            'verification': {'accepted': cert['accepted'] if cert else None},
            'reconstruction': {'attempted': kind in ('proof', 'reconstruction_refused'), 'closer': (verdict or refusal or {}).get('closer'),
                               'consumed': True if kind == 'proof' else False if kind == 'reconstruction_refused' else None, 'refusal': (refusal or {}).get('diagnosis')},
            'kernel': {'local': verdict['local_obligation_closed'] if verdict else None, 'whole': verdict['whole_declaration_validated'] if verdict else None,
                       'axioms_clean': all(v == {'added': [], 'removed': []} for v in verdict['axiom_delta'].values()) if verdict else None},
            'usage': {'input_tokens': usage.get('input_tokens'), 'output_tokens': usage.get('output_tokens'), 'cached_tokens': usage.get('cached_tokens')},
            'audit': {'accepted': True, 'publication': 'accepted' if scan_bound.get(n) else 'pending'}}
    return {'schema_version': 'r6-analysis-input-1', 'slots': slots, 'synthetic': LAYOUT['synthetic'],
            'campaign': {'authorized_schedule': policy['campaign']['schedule'], 'planned_schedule': policy['campaign']['planned_schedule'],
                         'authorized_micro_usd': policy['limits']['total_micro_usd'],
                         'ledger': {'consumed_slots': sorted(k for k, v in s['slots'].items() if v['consumed']), 'transmissions_consumed': s['transmissions_consumed'],
                                    'committed_micro_usd': s['committed_micro_usd']}}}


# ---------------------------------------------------------------------------------------------------------------- driver

def audit(root, ledgers, representability=None, v4_root=None, v5_root=None):
    representability = representability or ROOT/REPRESENTABILITY; v4_root = v4_root or ROOT/HISTORY_V4['runs']; v5_root = v5_root or ROOT/HISTORY_V5['runs']
    a = Audit(); result = {'runs': {}}; LIBRARY_BLOCKS.clear(); tools = stage_tools()
    classes = eligibility(a, representability); policy = load(LAYOUT['policies']/POLICY)
    HISTORY.clear(); HISTORY.update(revision_history(a, policy))
    if MODE == 'live':
        expected = derive_live_population(a, root, policy)
    else:
        try: expected = derive_population(classes); derived = len({t for (_, t, _, _) in expected.values()}) == 15
        except ValueError as error: a.require(False, 'population:derived_from_eligibility', str(error))
        a.require(derived, 'population:derived_from_eligibility', 'the fifteen-site denominator is not covered')
    names = sorted(expected); present = sorted(p.name for p in root.iterdir())
    a.require(present == names and all((root/n).is_dir() for n in present), 'population:exactly_expected_runs', str(present))
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
            book = ledger.Ledger(ledgers/sp['campaign_id']/purpose(), sp['campaign_id'])
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
        stage_commands(a, run, name, kind, task, tools, load(run/'provenance/roles.json')['actor_source'].removesuffix('cohort_https.py'))
        solution = closer = None
        if kind in WITNESS_KINDS:
            response = response_bound(a, run, name, kind, request_bytes); attribution(a, run, name, kind, rows, sp)
            if kind == 'proof': solution, closer = proof(a, run, name, rows, task, sp, request_bytes, record, response, frozen)
            elif kind == 'reconstruction_refused':
                reconstruction_refused(a, run, name, rows, task, sp, request_bytes, record, response); closer = load(run/'reconstruction-refusal.json')['closer']
            elif kind == 'witness_rejected': witness_rejected(a, run, name, rows, record, response, request_bytes)
            else: negative(a, run, name, rows, record, response, request_bytes)
        elif kind in ('response_invalid', 'provider_error'): live_failure(a, run, name, kind, http)
        elif kind == 'release': (live_release if MODE == 'live' else failure)(a, run, name, http)  # amendment 2
        else: interface_refused(a, run, name, rows, task, representability)
        result['runs'][name] = {'kind': kind, 'task': task_id, 'draw': draw, 'revision': revision, 'policy_sha256': sp['config_sha256'],
                                'ledger_outcome': reconciliation['kind'] if reconciliation else None, 'body_sha256': sha(body) if body else None,
                                'renamed': renamed, 'solution_sha256': solution, 'closer': closer,
                                'diagnosis': load(run/'reconstruction-refusal.json')['diagnosis'] if kind == 'reconstruction_refused' else None}
    if MODE == 'live':
        result['campaign'] = cross_run_live(a, root, ledgers, expected, sp_by_run, policy, bodies, identities, permits, reconciliations, priced, contract_digest)
        result['operator_scan'] = operator_scan(a, root, ledgers, expected, policy)
        result['analysis_input'] = analysis_input(root, expected, policy, ledgers, result['operator_scan']['receipts_bound'])
    else:
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
                  mode=MODE, synthetic=LAYOUT['synthetic'], live_model_calls=0, credentials_read=0, program_sha256=sha(Path(__file__).read_bytes()),
                  library_inventory_sha256=LIBRARY_INVENTORY_SHA256,
                  challenge_claim='both replays name one temporary path of the driver pattern outside the recorded root; the bytes were not retained, '
                                  'and the driver hashing the challenge before replay is a property of the pinned source, not a retained-byte check',
                  scope='audit over retained bytes, with the classification recomputed; no native episode or proof replay; cached tool build invoked (run.build_tools)')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode', choices=('rehearsal', 'live'), default='rehearsal')
    parser.add_argument('--runs', help='the recorded runs directory, relative to experiments/r6')
    parser.add_argument('--policies', type=Path, help='directory holding the policy, lock and checkpoint the runs were recorded under')
    parser.add_argument('--ledger-prefix', help='the recorded ledger directory, relative to experiments/r6')
    parser.add_argument('--operator-report', type=Path, help='live: the operator scan\'s full report')
    parser.add_argument('--scan-root', type=Path, help='live: the root the operator scanned (default experiments/r6)')
    parser.add_argument('--fixture', type=Path, help='live-shaped canned evidence: its runs, policies, ledgers and scan (SYNTHETIC)')
    parser.add_argument('--analysis-input', type=Path, help='live: write the frozen analysis input here')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    for path in (args.output, args.analysis_input):
        if path and path.exists(): raise SystemExit('Refusing to overwrite: '+str(path))
    if args.fixture:
        f = args.fixture.resolve()
        configure('live', str((f/'runs').relative_to(ROOT)), f/'policies', str((f/'ledgers/campaigns').relative_to(ROOT)), f/'operator-disclosure-scan.json', synthetic=True)
        LAYOUT['scan_root'] = f
    else:
        configure(args.mode, args.runs, args.policies, args.ledger_prefix, args.operator_report)
        LAYOUT['scan_root'] = (args.scan_root or ROOT).resolve()
    try: result = audit((ROOT/RUNS).resolve(), (ROOT/LAYOUT['ledger_prefix']).resolve())
    except Rejection as rejection:
        print(json.dumps({'accepted': False, 'rejected_case': rejection.case, 'detail': str(rejection)}, indent=1)); sys.exit(1)
    if args.output: r6.write_json(args.output, result)
    if args.analysis_input and 'analysis_input' in result: r6.write_json(args.analysis_input, result['analysis_input'])
    print(json.dumps({k: result.get(k) for k in ('accepted', 'case_count', 'revision', 'mode', 'synthetic', 'modules', 'strata', 'campaign', 'operator_scan', 'history_v4', 'history_v5')}, indent=1))
    sys.exit(0 if result['accepted'] else 1)


if __name__ == '__main__':
    main()
