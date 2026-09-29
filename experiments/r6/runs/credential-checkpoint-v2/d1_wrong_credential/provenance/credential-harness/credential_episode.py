#!/usr/bin/env python3
"""R6-004: credential delivery, exact receipt, and publication disclosure control.

Three predicates are recorded separately and never collapsed: the endpoint read
the exact synthetic canary, the complete publication bundle discloses nothing,
and the proof validated. A disclosure fails publication even when every
mathematical check passed, and the sealed evidence is preserved either way.
"""
import argparse
from pathlib import Path
import shutil

import admission
import credential
import credential_contract as contract
import episode
import events
import instrument
import provider_episode as previous
import provider_payload as wire
import publication
import run as r6

CASES = ('valid', 'http503', 'missing_credential', 'wrong_credential', 'reflected_canary')
CLEAN_SCAN_CASES = ('valid', 'http503', 'missing_credential', 'wrong_credential')
STAGES = previous.STAGES if hasattr(previous, 'STAGES') else (
    'preparation-build', 'preparation', 'pipeline-prepare', 'proposal-1', 'assembly',
    'certificate-check', 'capture-build', 'reconstruct', 'export', 'validation-local', 'validation-whole')


class Failure(wire.Failure):
    """Boundaries this policy adds, mapped through its own phase table."""
    def __init__(self, category, stage, detail, evidence=None):
        ValueError.__init__(self, detail)
        self.category, self.stage, self.evidence = category, stage, evidence
        self.phase = contract.PHASES[stage]


def require(condition, message):
    if not condition: raise ValueError('Credential episode: '+message)


def setup(run, task, packages):
    contract.verify_sources()
    tools = previous.setup(run, task, packages)
    roles = r6.read_json(run/'provenance/roles.json')
    roles['actor_source'] = str(r6.ROOT/'credential_http.py')
    roles['superseded_actor_source'] = str(r6.ROOT/'provider_http.py')
    roles['credential_channel'] = contract.GUEST_CREDENTIAL
    r6.write_json(run/'provenance/roles.json', roles)
    for source in [r6.ROOT/name for name in contract.FILES]+[contract.CONFIG, contract.LOCK]:
        target = run/'provenance/credential-harness'/source.relative_to(r6.ROOT)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    return tools


def receipt(run, server, canary, case):
    """Compare the endpoint's digest of the header it actually read."""
    expected = credential.commitment(canary)
    observed = server['requests'][0]['authorization_sha256'] if server['requests'] else None
    value = {'schema_version': 'r6-credential-receipt-1', 'channel': 'private_read_only_file',
        'declared_case': case, 'transmissions': len(server['requests']),
        'authorization_present': bool(server['requests']) and server['requests'][0]['authorization_present'],
        'expected_authorization_sha256': expected, 'observed_authorization_sha256': observed,
        'exact_receipt': observed == expected,
        'evidence_scope': 'endpoint digest of the incoming header; a presence bit or host echo '
                          'does not discharge it; synthetic canary commitment only'}
    r6.write_json(run/'credential-receipt.json', value)
    events.append(run, 'credential-receipt', 'credential_receipt_checked', value)
    return value


class Session(previous.Session):
    def invoke(self, tools, case, canary_path):
        c, root = contract.config(), self.run
        if self.reserved >= c['attempt_limit']:
            events.append(root, 'proposal', 'request_budget_exhausted', self.write_accounting())
            raise wire.Failure('request_budget_exhaustion', 'proposal', 'Frozen transmission budget exhausted')
        self.reserved += 1; self.write_accounting()
        request = (root/'request.json').read_bytes()
        require(r6.read_json(root/'client-arguments.json') == wire.arguments(request), 'client arguments changed before serialization')
        events.append(root, 'proposal', 'request_reserved', {'attempt': self.reserved, 'request_sha256': wire.sha(request),
            'prompt_sha256': r6.sha(root/'prompt.txt'), 'client_arguments_sha256': r6.sha(root/'client-arguments.json')})
        runtime = tools['runtime']
        stage_error = None
        try:
            out = episode.stage(root, 'proposal-1', tools['python'],
                ['-I', '-S', '-B', '/adapter.py', '--arguments', '/arguments.json', '--fixture', '/fixture.json',
                 '--credential-file', contract.GUEST_CREDENTIAL, '--case', case, '--out', '/out',
                 '--timeout', str(c['http_timeout_seconds']), '--maximum-body', str(c['maximum_request_bytes']),
                 '--maximum-response', str(c['maximum_provider_response_bytes'])],
                [(tools['runtime_path'], runtime['stdlib']), (r6.ROOT/'credential_http.py', '/adapter.py'),
                 (root/'client-arguments.json', '/arguments.json'), (root/'canned-provider.json', '/fixture.json'),
                 (canary_path, contract.GUEST_CREDENTIAL)],
                extra_binaries=[Path(p) for p in runtime['extension_binaries']],
                wall=c['request_wall_seconds'], cpu=c['request_cpu_seconds'],
                memory=c['request_memory_bytes'], output_limit=c['request_output_bytes'])
        except episode.StageFailure as error:
            stage_error, out = error, root/'stages/proposal-1/output'
        if stage_error:
            for name, attribute in [('http.json', 'http'), ('server.json', 'server')]:
                try: setattr(self, attribute, r6.read_json(out/name))
                except (OSError, ValueError): pass
            self.write_accounting()
            raise stage_error
        try: self.http, self.server = r6.read_json(out/'http.json'), r6.read_json(out/'server.json')
        except (OSError, ValueError) as error:
            raise wire.Failure('transport_capture_failure', 'proposal-1', 'HTTP actor lacks readable observations') from error
        self.write_accounting()
        require(self.http['connection_attempts'] <= self.reserved and self.http['body_sends_started'] <= self.reserved
            and len(self.server['requests']) <= self.reserved, 'hidden retry exceeded reserved budget')
        events.append(root, 'proposal', 'http_observed', {'http_sha256': r6.sha(out/'http.json'),
            'server_sha256': r6.sha(out/'server.json'), 'accounting': self.write_accounting()})
        outbound = (out/'outbound-body.json').read_bytes()
        captured = (out/'received-body-1.json').read_bytes() if (out/'received-body-1.json').exists() else None
        raw = (out/'provider-response.json').read_bytes() if (out/'provider-response.json').exists() else None
        response, text, metadata, validation, error = wire.transport(outbound, captured, raw, self.http, request)
        self.metadata = metadata
        r6.write_json(root/'provider-metadata.json', metadata)
        if text is not None: (root/'response.json').write_bytes(text)
        r6.write_json(root/'transport-validation.json', validation)
        events.append(root, 'proposal', 'transport_validated', validation)
        self.write_accounting()
        return response, error


def proof(run, task, tools, session, response, nonce, case):
    packet, report, reports, delta, solution_hash = previous.consume(run, task, tools, response)
    require(all(r6.sha(Path(p)) == h for p, h in r6.read_json(run/'provenance/binaries.json').items()), 'binary changed')
    r6.frozen_task(task)
    request = (run/'request.json').read_bytes()
    verdict = {'schema_version': 'r6-credential-episode-2', 'search_policy': contract.NAME, 'task_id': task.id,
        'proof_accepted': True, 'search_succeeded': True, 'certificate_type': 'farkas', 'trust_tier': 1,
        'witness_proposer': 'canned_provider_response', 'certificate_assembler': 'sdk_proposal_assembler_v1',
        'recovery_route': contract.NAME, 'certificate_verified': True, 'certificate_consumed': True,
        'derivation_replayed': False, 'residual_closer': 'omega', 'proof_replayed': True,
        'local_obligation_closed': True, 'whole_declaration_validated': True, 'axiom_delta': delta,
        'local_proof_required_reference': episode.FARKAS_HELPER,
        'accounting': session.write_accounting(), 'transport_validation': r6.read_json(run/'transport-validation.json'),
        'solution_sha256': solution_hash, 'challenge_sha256': tools['expected']['challenge_sha256'],
        'manifest_sha256': r6.sha(task.path/'manifest.json'), 'prompt_sha256': r6.sha(run/'prompt.txt'),
        'request_sha256': wire.sha(request), 'response_sha256': r6.sha(run/'response.json'),
        'canary_nonce': nonce, 'credential_receipt_sha256': r6.sha(run/'credential-receipt.json'),
        'final_validation': reports, 'certificate_validation': report,
        'resources': {p.parent.name: r6.read_json(p) for p in sorted((run/'stages').glob('*/*.process.json'))},
        'evidence_receipt_claim': 'local HTTP fixture, credential-channel receipt and proof checks; '
                                  'no remote receipt, TLS, compilation or inference attestation'}
    r6.write_json(run/'verdict.json', verdict)
    r6.jsonschema.validate(verdict, r6.read_json(r6.ROOT/'schema/credential-verdict.schema.json'))
    events.append(run, 'episode', 'proof_validated', {'verdict_sha256': r6.sha(run/'verdict.json'),
        'proof_accepted': True, 'solution_sha256': solution_hash})
    return verdict


def summarize(run, task, case, receipt_record, proof_error, proof_accepted):
    value = {'schema_version': 'r6-credential-summary-1', 'task_id': task.id, 'search_policy': contract.NAME,
        'case': case, 'proof_accepted': proof_accepted,
        'credential_receipt_accepted': receipt_record['exact_receipt'] if receipt_record else False,
        'failure_stage': getattr(proof_error, 'stage', None), 'failure_phase': getattr(proof_error, 'phase', None),
        'failure_category': getattr(proof_error, 'category', None),
        'error': None if proof_error is None else str(proof_error),
        'causal_attribution': 'unassigned; observed boundary only',
        'scope': 'proof and credential-receipt predicates only; publication is decided after this record'}
    r6.write_json(run/'credential-summary.json', value)
    return value


def finalize(run, canary, nonce, summary, outer_logs=()):
    """Scan last; every later write carries only digests, counts and booleans."""
    report = publication.scan([run, *outer_logs], canary, nonce)
    r6.write_json(run/'publication-scan.json', report)
    final = publication.final_record(run/'publication-scan.json', canary, nonce)
    r6.write_json(run/'publication-final.json', final)
    accepted = bool(summary['proof_accepted'] and summary['credential_receipt_accepted']
                    and report['accepted'] and final['report_clean'])
    payload = {'accepted': accepted, 'proof_accepted': bool(summary['proof_accepted']),
        'credential_receipt_accepted': bool(summary['credential_receipt_accepted']),
        'publication_accepted': bool(report['accepted'] and final['report_clean']),
        'summary_sha256': r6.sha(run/'credential-summary.json'),
        'publication_scan_sha256': r6.sha(run/'publication-scan.json'),
        'publication_final_sha256': r6.sha(run/'publication-final.json')}
    require(publication.safe_record(payload, publication.TERMINAL_KEYS), 'terminal receipt carries an unrestricted value')
    events.append(run, 'episode', 'episode_finished' if accepted else 'episode_rejected', payload)
    seal(run, accepted)
    return accepted, report, final


def seal(run, accepted, ephemeral=None):
    """`ephemeral` carries a frozen build-product inventory into a resealed copy."""
    rows = episode.observations(run)
    retained, ephemeral = {}, dict(ephemeral or {})
    for p in sorted(run.rglob('*')):
        if not p.is_file() or p.name == 'seal.json': continue
        name = str(p.relative_to(run))
        drop = ('.olean' in p.name or p.suffix in {'.ilean', '.c', '.o'}
                or (p.name in {'proof.ndjson', 'verdict.json'} and '/output/' in name)
                or name.endswith('/export/export.stdout'))
        (ephemeral if drop and name not in contract.RETAINED_SOURCES else retained)[name] = r6.sha(p)
    r6.write_json(run/'seal.json', {'schema_version': 'r6-credential-seal-1', 'accepted': accepted,
        'event_count': len(rows), 'last_event_hash': rows[-1]['event_hash'],
        'retained_sha256': retained, 'ephemeral_sha256': ephemeral})


def execute(run, task, case, packages, outer_logs=()):
    config, cohort = contract.config(), admission.verify()
    require(task.id in cohort['controls'] and task.id in contract.FIXTURES, 'task is outside frozen cohort')
    tools = setup(run, task, packages)
    seed = credential.nonce()
    r6.write_json(run/'credential-canary.json', credential.record(seed))
    policy = {**config, 'task_id': task.id, 'task_manifest_sha256': r6.sha(task.path/'manifest.json'),
              'contract_sha256': r6.sha(contract.CONFIG), 'case': case, 'sdk_base_commit': instrument.BASE}
    r6.write_json(run/'search-policy.json', policy)
    events.append(run, 'episode', 'episode_started', {'task_manifest_sha256': policy['task_manifest_sha256'],
        'search_policy_sha256': r6.sha(run/'search-policy.json'), 'challenge_sha256': tools['expected']['challenge_sha256'],
        'canary_nonce': seed, 'canary_derivation': credential.DOMAIN}, task_id=task.id)
    session, receipt_record, proof_error, verdict = Session(run), None, None, None
    try:
        previous.prepare(run, task, tools)
        request = (run/'request.json').read_bytes()
        r6.write_json(run/'canned-provider.json', previous.canned_provider(task, request, wire_case(case)))
        events.append(run, 'proposal', 'recovery_started', {'route': contract.NAME, 'proposer': 'canned_provider_response'})
        with credential.delivery(seed) as (canary, canary_path):
            response, transport_error = session.invoke(tools, case, canary_path)
        receipt_record = receipt(run, session.server, canary, case)
        if not receipt_record['exact_receipt']:
            raise Failure('credential_receipt_failure', 'credential-receipt',
                'Endpoint did not read the exact synthetic canary', receipt_record)
        if transport_error: raise transport_error
        verdict = proof(run, task, tools, session, response, seed, case)
    except (wire.Failure, episode.StageFailure) as error:
        proof_error = error
    except Exception as error:
        canary = credential.derive(seed)
        summary = summarize(run, task, case, receipt_record, error, False)
        finalize(run, canary, seed, {**summary, 'proof_accepted': False}, outer_logs)
        raise
    canary = credential.derive(seed)
    summary = summarize(run, task, case, receipt_record, proof_error, verdict is not None)
    accepted, report, final = finalize(run, canary, seed, summary, outer_logs)
    return {'accepted': accepted, 'proof_accepted': summary['proof_accepted'],
            'credential_receipt_accepted': summary['credential_receipt_accepted'],
            'publication_accepted': report['accepted'] and final['report_clean'],
            'failure_category': summary['failure_category'], 'failure_stage': summary['failure_stage'],
            'disclosures': len(report['disclosures']), 'verdict': verdict}


def wire_case(case):
    """The canned body follows R6-003 shapes; credential cases reuse `valid`."""
    return case if case in {'http503'} else 'valid'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['run', 'audit'])
    parser.add_argument('--task', choices=contract.FIXTURES)
    parser.add_argument('--case', choices=CASES, default='valid')
    parser.add_argument('--run-dir', type=Path, required=True)
    parser.add_argument('--packages-dir', type=Path, default=r6.ROOT.parents[1]/'lean-bridge/.lake/packages')
    parser.add_argument('--development-policy-dir', type=Path)
    args = parser.parse_args()
    if args.development_policy_dir: contract.development(args.development_policy_dir)
    run = args.run_dir.resolve()
    if args.action == 'audit':
        from credential_audit import audit
        task = r6.get_task(args.task or r6.read_json(run/'credential-summary.json')['task_id'])
        print('Credential episode audit accepted:', audit(run, task)['accepted'])
        return
    if not args.task: parser.error('run requires --task')
    task = r6.get_task(args.task)
    run.mkdir(parents=True, exist_ok=False)
    result = execute(run, task, args.case, args.packages_dir)
    print(f'Credential episode {"accepted" if result["accepted"] else "rejected"}: {run}')
    raise SystemExit(0 if result['accepted'] else 1)


if __name__ == '__main__':
    main()
