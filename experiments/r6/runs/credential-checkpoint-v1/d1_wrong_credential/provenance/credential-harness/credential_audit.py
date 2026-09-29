"""Audit credential receipt, publication non-disclosure and proof separately.

The publication scan is reproduced here from an independently walked inventory
and the canary re-derived from the retained nonce. A reported target list, a
reported zero count, or a reported component name is never trusted. The proof
block is the frozen shared checker; this module adds no second copy of it.
"""
from pathlib import Path

import admission
import credential
import credential_contract as contract
import credential_http
import envelope_proof_audit
import episode
import events
import instrument
import provider_audit as previous
import provider_payload as wire
import publication
import run as r6
from supervise import resource_violations

STAGES = ('preparation-build', 'preparation', 'pipeline-prepare', 'proposal-1', 'assembly',
          'certificate-check', 'capture-build', 'reconstruct', 'export', 'validation-local', 'validation-whole')
# Written after the scan, so they are absent from the recorded inventory.
POST_SCAN = ('publication-scan.json', 'publication-final.json', 'seal.json')


def require(condition, message):
    if not condition: raise ValueError('Credential audit: '+message)


def same(a, b, message):
    require(events.canonical(a) == events.canonical(b), message)


def audit(run, task):
    run = Path(run)
    seal = r6.read_json(run/'seal.json')
    require(seal['schema_version'] == 'r6-credential-seal-1', 'unexpected seal version')

    def path(name):
        p = run/name
        require(name in seal['retained_sha256'] and p.resolve().is_relative_to(run.resolve()), 'artifact not retained: '+name)
        return p

    def read(name): return r6.read_json(path(name))
    for name, digest in seal['retained_sha256'].items():
        require(r6.sha(path(name)) == digest, 'sealed artifact changed: '+name)
    rows = episode.observations(run)
    require(len(rows) == seal['event_count'] and rows[-1]['event_hash'] == seal['last_event_hash'], 'receipt seal mismatch')
    require(all(row['task_id'] == task.id for row in rows), 'task identity mismatch')

    def receipt_of(stage, event):
        matches = [r['payload'] for r in rows if r['source'] == 'supervisor' and r['stage'] == stage and r['event'] == event]
        require(len(matches) == 1, f'expected one receipt: {stage}/{event}')
        return matches[0]

    import credential_episode as harness
    config, policy = contract.config(), read('search-policy.json')
    summary, canary_record = read('credential-summary.json'), read('credential-canary.json')
    cohort = admission.verify()
    require(task.id in cohort['controls'] and task.id in contract.FIXTURES, 'task is outside frozen cohort')
    require(policy['case'] in harness.CASES, 'undeclared canned case')
    same(policy, {**config, 'task_id': task.id, 'task_manifest_sha256': r6.sha(task.path/'manifest.json'),
        'contract_sha256': r6.sha(contract.CONFIG), 'case': policy['case'], 'sdk_base_commit': instrument.BASE},
        'frozen credential policy changed')
    _, expected = r6.frozen_task(task)

    nonce = canary_record['nonce']
    canary = credential.derive(nonce)
    same(canary_record, credential.record(nonce), 'canary record differs from the frozen derivation')
    same(receipt_of('episode', 'episode_started'), {'task_manifest_sha256': r6.sha(task.path/'manifest.json'),
        'search_policy_sha256': r6.sha(path('search-policy.json')), 'challenge_sha256': expected['challenge_sha256'],
        'canary_nonce': nonce, 'canary_derivation': credential.DOMAIN}, 'admission/canary binding')

    check_provenance(path, read)
    # Disclosure is decided before any other comparison, so a leak is reported
    # as a publication failure rather than as an incidental artifact mismatch.
    scan, final = check_publication(run, seal, path, read, receipt_of, canary, nonce, summary)
    receipt_record = check_receipt(run, path, read, receipt_of, canary, policy['case'])
    transport, accounting, request, response, raw, transport_error = check_transport(path, read, receipt_of, task, policy, canary)
    check_command(read('stages/proposal-1/command.json'), read('provenance/python-runtime.json'),
                  read('provenance/roles.json'), policy['case'], canary)
    proof_ok = check_proof(run, task, seal, path, read, receipt_of, rows, policy, config, expected,
                           summary, transport, accounting, request, raw, transport_error, receipt_record)
    accepted = bool(proof_ok and receipt_record['exact_receipt'] and scan['accepted'] and final['report_clean'])
    check_order(rows, proof_ok, accepted)
    same(rows[-1]['payload'], {'accepted': accepted, 'proof_accepted': proof_ok,
        'credential_receipt_accepted': receipt_record['exact_receipt'],
        'publication_accepted': bool(scan['accepted'] and final['report_clean']),
        'summary_sha256': r6.sha(path('credential-summary.json')),
        'publication_scan_sha256': r6.sha(path('publication-scan.json')),
        'publication_final_sha256': r6.sha(path('publication-final.json'))}, 'terminal receipt differs')
    require(rows[-1]['event'] == ('episode_finished' if accepted else 'episode_rejected'), 'terminal event/acceptance mismatch')
    require(seal['accepted'] is accepted, 'seal acceptance differs from recomputed predicates')
    return {'accepted': accepted, 'proof_accepted': proof_ok, 'credential_receipt_accepted': receipt_record['exact_receipt'],
        'publication_accepted': bool(scan['accepted'] and final['report_clean']), 'disclosures': scan['disclosures'],
        'failure_category': summary['failure_category'], 'failure_stage': summary['failure_stage'],
        'files_scanned': scan['files_scanned'], 'canary_nonce': nonce,
        'scope': 'recorded credential-channel, publication and proof predicates; no remote receipt, '
                 'TLS, compilation or inference attestation'}


def check_order(rows, proof_ok, accepted):
    """Stages run in the frozen order; the terminal receipt comes last."""
    supervisor = [r for r in rows if r['source'] == 'supervisor']
    present = [s for s in STAGES if any(r['stage'] == s and r['event'] == 'stage_started' for r in supervisor)]
    require(present == list(STAGES[:len(present)]), 'stages are skipped or out of order')
    order = [('episode', 'episode_started')]
    for stage in present:
        if stage == 'proposal-1':
            order += [('payload', 'payload_validated'), ('proposal', 'recovery_started'), ('proposal', 'request_reserved')]
        order += [(stage, 'stage_started'), (stage, 'stage_finished')]
        if stage == 'proposal-1':
            order += [('proposal', 'http_observed'), ('proposal', 'transport_validated'),
                      ('credential-receipt', 'credential_receipt_checked')]
        if stage == 'assembly': order += [('assembly', 'certificate_assembled')]
        if stage == 'certificate-check':
            order += [('certificate-check', 'independent_certificate_verdict'), ('proposal', 'recovery_finished')]
        if stage == 'reconstruct': order += [('reconstruct', 'context_validated')]
        if stage.startswith('validation-'): order += [(stage, 'kernel_verdict')]
    if proof_ok: order.append(('episode', 'proof_validated'))
    order.append(('episode', 'episode_finished' if accepted else 'episode_rejected'))
    require([(r['stage'], r['event']) for r in supervisor] == order,
            'missing, extra, or reordered supervisor receipts')


def check_provenance(path, read):
    """R6-003 provenance, extended for the versioned adapter and its role."""
    import proposal_instrument as overlay
    sources, patch = overlay.source_record()
    same(read('provenance/sources.json'), sources, 'source overlay provenance changed')
    require(path('provenance/instrumentation.patch').read_text() == patch, 'source overlay patch changed')
    for name, digest in overlay.source_lock().items():
        require(r6.sha(path('provenance/harness/'+name)) == digest, 'downstream harness source differs: '+name)
    for section, module, extras in [('envelope-harness', contract.previous.previous, []),
                                    ('provider-harness', contract.previous, [contract.RUNTIME]),
                                    ('credential-harness', contract, [])]:
        for name, digest in module.source_lock().items():
            require(r6.sha(path('provenance/'+section+'/'+name)) == digest, 'retained harness source differs: '+section+'/'+name)
        for source in [module.CONFIG, module.LOCK, *extras]:
            require(r6.sha(path('provenance/'+section+'/'+str(source.relative_to(r6.ROOT)))) == r6.sha(source),
                    'retained policy lock differs: '+section)
    binaries, roles = read('provenance/binaries.json'), read('provenance/roles.json')
    runtime = read('provenance/python-runtime.json')
    same(runtime, r6.read_json(contract.RUNTIME), 'pinned runtime inventory differs')
    require(len(binaries) == 15 and all(isinstance(k, str) and k.startswith('/') and isinstance(v, str) and len(v) == 64
        for k, v in binaries.items()), 'binary inventory')
    suffixes = {'unused_legacy_responder': '/proposal-instrumented/fixture', 'assembler': '/validate/proposal_driver.exe',
                'verifier': '/validate/verify_certificate.exe', 'checker': '/r6-replay'}
    require(set(roles) == set(suffixes) | {'python', 'runtime_path', 'actor_source', 'downstream_setup',
                                           'superseded_actor_source', 'credential_channel'}, 'binary role inventory')
    for role, suffix in suffixes.items():
        require(roles[role] in binaries and roles[role].endswith(suffix), 'binary role differs: '+role)
    require(roles['python'] == runtime['python'] and binaries[roles['python']] == runtime['python_sha256'], 'Python binary binding')
    require(roles['actor_source'].endswith('/experiments/r6/credential_http.py')
            and roles['superseded_actor_source'].endswith('/experiments/r6/provider_http.py'), 'adapter role differs')
    require(roles['credential_channel'] == contract.GUEST_CREDENTIAL, 'credential channel role differs')
    return binaries, roles, runtime


def check_receipt(run, path, read, receipt_of, canary, case):
    """Re-derive the commitment; a presence bit never discharges the receipt."""
    record = read('credential-receipt.json')
    server = read('stages/proposal-1/output/server.json')
    expected = credential.commitment(canary)
    observed = server['requests'][0]['authorization_sha256'] if server['requests'] else None
    same(record, {'schema_version': 'r6-credential-receipt-1', 'channel': 'private_read_only_file',
        'declared_case': case, 'transmissions': len(server['requests']),
        'authorization_present': bool(server['requests']) and server['requests'][0]['authorization_present'],
        'expected_authorization_sha256': expected, 'observed_authorization_sha256': observed,
        'exact_receipt': observed == expected,
        'evidence_scope': record['evidence_scope']}, 'credential receipt differs from endpoint observations')
    require(record['expected_authorization_sha256'] == expected, 'receipt expectation is not the derived canary')
    same(receipt_of('credential-receipt', 'credential_receipt_checked'), record, 'receipt/receipt-event mismatch')
    if case == 'missing_credential':
        require(record['authorization_present'] is False and observed is None, 'missing-header control did not defeat receipt')
    if case == 'wrong_credential':
        require(record['authorization_present'] is True and observed == r6.hashlib.sha256(credential_http.WRONG.encode()).hexdigest()
                and observed != expected, 'wrong-value control did not defeat receipt')
    require(record['exact_receipt'] == (case not in {'missing_credential', 'wrong_credential'}), 'receipt outcome differs from the declared case')
    return record


def check_transport(path, read, receipt_of, task, policy, canary):
    import credential_episode as harness
    root = 'stages/proposal-1/output/'
    http, server = read(root+'http.json'), read(root+'server.json')
    require(http['schema_version'] == 'r6-http-observation-2', 'HTTP observation version')
    expected_files = {'http.json', 'server.json', 'outbound-body.json'} | {
        f'received-body-{i+1}.json' for i in range(len(server['requests']))}
    if http['response_sha256'] is not None: expected_files.add('provider-response.json')
    require({p.name for p in path(root+'http.json').parent.iterdir()} == expected_files,
            'HTTP observation file inventory differs; possible unreported capture')
    outbound = path(root+'outbound-body.json').read_bytes()
    require(http['request_bytes'] == len(outbound) and http['request_sha256'] == wire.sha(outbound), 'HTTP request body binding')
    require(http['mode'] == 'isolated_loopback_http_fixture' and http['method'] == 'POST'
        and http['request_path'] == '/v1/responses', 'HTTP method/path/mode differs')
    require(http['authorization_sent'] is (policy['case'] != 'missing_credential'), 'declared credential transmission differs')
    require(http['connection_attempts'] == 1 and http['body_sends_started'] in (0, 1)
        and http['body_sends_returned'] <= http['body_sends_started'] and len(server['requests']) <= 1, 'unreserved transmission/retry')
    request = wire.request(task, read('prepared.json'))
    require(path('request.json').read_bytes() == request, 'request differs from allowed arithmetic input')
    require(path('prompt.txt').read_bytes() == contract.PROMPT.read_bytes(), 'frozen semantic prompt changed')
    require(outbound == credential_http.serialize(wire.arguments(request), policy['case']), 'declared HTTP serialization differs')
    captured = path(root+'received-body-1.json').read_bytes() if server['requests'] else None
    if captured is not None:
        same(server['requests'], [{'method': 'POST', 'path': '/v1/responses', 'content_type': 'application/json',
            'declared_bytes': len(captured), 'observed_bytes': len(captured), 'complete': True,
            'body_sha256': wire.sha(captured), 'authorization_present': server['requests'][0]['authorization_present'],
            'authorization_sha256': server['requests'][0]['authorization_sha256']}], 'server receipt shape differs')
    same(read('canned-provider.json'), harness.previous.canned_provider(task, request, harness.wire_case(policy['case'])),
         'canned provider response differs')
    fixture = read('canned-provider.json')
    raw = path(root+'provider-response.json').read_bytes() if http['response_sha256'] is not None else None
    if raw is not None:
        require(http['response_sha256'] == wire.sha(raw) and http['response_bytes'] == len(raw), 'HTTP response body binding')
        if policy['case'] == 'reflected_canary':
            # Precondition for the production-path disclosure control: the value
            # really is in the bytes the ordinary failure path retained.
            require(http['http_status'] == 500 and credential.header(canary).encode() in raw,
                    'reflection precondition absent from the retained response')
        else:
            require(raw == fixture['body'].encode() and http['http_status'] == fixture['status'],
                    'retained response differs from the canned endpoint')
    response, text, metadata, validation, error = wire.transport(outbound, captured, raw, http, request)
    same(read('provider-metadata.json'), metadata, 'provider decode metadata differs')
    same(read('transport-validation.json'), validation, 'independently reconstructed transport diagnostics differ')
    same(receipt_of('proposal', 'transport_validated'), validation, 'transport diagnostic receipt differs')
    accounting = {'attempts_reserved': 1, 'client_connection_attempts': http['connection_attempts'],
        'body_sends_started': http['body_sends_started'], 'body_sends_returned': http['body_sends_returned'],
        'transmissions_observed': sum(r['complete'] is True for r in server['requests']),
        'reported_usage': (metadata or {}).get('usage', wire.usage({})), 'live_model_calls': 0, 'live_model_cost_usd': 0,
        'scope': 'local HTTP fixture; usage is synthetic or unreported, cost unknown; actual live calls/cost zero'}
    same(read('accounting.json'), accounting, 'accounting differs from HTTP observations')
    return validation, accounting, request, response, text, error


def check_command(spec, runtime, roles, case, canary):
    """The credential is a private mount; it never reaches argv or the environment."""
    prefix = ['bwrap', '--unshare-all', '--die-with-parent', '--new-session', '--cap-drop', 'ALL',
        '--clearenv', '--setenv', 'PATH', '/no-programs', '--setenv', 'LEAN_ABORT_ON_PANIC', '1',
        '--symlink', 'usr/lib', '/lib', '--symlink', 'usr/lib64', '/lib64',
        '--proc', '/proc', '--dev', '/dev', '--tmpfs', '/tmp', '--dir', '/work', '--chdir', '/work']
    for item in runtime['libraries']: prefix += ['--ro-bind', item['host'], item['guest']]
    original, c = Path(spec['run']), contract.config()
    require(original.is_absolute() and spec['records'] == str(original/'stages/proposal-1'), 'HTTP command record root')
    mounts = spec['argv'][len(prefix):]
    credential_host = None
    for index, item in enumerate(mounts):
        if item == contract.GUEST_CREDENTIAL and mounts[index-1] not in {'--credential-file'}:
            credential_host = mounts[index-1]
    require(credential_host is not None, 'no credential mount in the recorded command')
    require(not Path(credential_host).is_relative_to(original), 'credential file was materialized inside the artifact tree')
    require(not Path(credential_host).exists(), 'credential file survived the episode')
    prefix += ['--ro-bind', roles['runtime_path'], runtime['stdlib'],
        '--ro-bind', roles['actor_source'], '/adapter.py',
        '--ro-bind', str(original/'client-arguments.json'), '/arguments.json',
        '--ro-bind', str(original/'canned-provider.json'), '/fixture.json',
        '--ro-bind', credential_host, contract.GUEST_CREDENTIAL,
        '--ro-bind', runtime['python'], '/runner/bin/program', '--bind', str(original/'stages/proposal-1/output'), '/out',
        '/runner/bin/program', '-I', '-S', '-B', '/adapter.py', '--arguments', '/arguments.json', '--fixture', '/fixture.json',
        '--credential-file', contract.GUEST_CREDENTIAL, '--case', case, '--out', '/out',
        '--timeout', str(c['http_timeout_seconds']), '--maximum-body', str(c['maximum_request_bytes']),
        '--maximum-response', str(c['maximum_provider_response_bytes'])]
    require(spec['argv'] == prefix and spec['capture_events'] is False,
            'HTTP command permits extra inputs/capabilities or a different boundary')
    joined = '\x00'.join(spec['argv'])
    require(canary not in joined and credential.header(canary) not in joined, 'canary value appears in the command record')
    require(roles['actor_source'].endswith('/experiments/r6/credential_http.py'), 'credential actor source location')
    for key in ['wall_seconds', 'cpu_seconds', 'memory_bytes', 'output_bytes']:
        require(spec[key] == c['request_'+key], 'request budget differs from contract')


def check_publication(run, seal, path, read, receipt_of, canary, nonce, summary):
    """Reproduce the scan from a walked inventory, not the reported targets."""
    for name in POST_SCAN:
        require(name == 'seal.json' or name in seal['retained_sha256'], 'publication record is not retained: '+name)
    report, final = read('publication-scan.json'), read('publication-final.json')
    require(report['schema_version'] == publication.VERSION, 'publication scan version')
    require(report['canary_nonce'] == nonce and report['derivation_domain'] == credential.DOMAIN, 'scan canary binding')
    require(report['encoded_forms'] == sorted(publication.forms('x')), 'declared encoded forms differ')
    require(report['decompression_limit_bytes'] == publication.LIMIT, 'declared decompression limit differs')
    require(report['exempted_files'] == [], 'a derived canary requires an empty exemption list')

    present = {str(q.relative_to(run)) for q in run.rglob('*') if q.is_file()}
    recorded = {entry['path']: entry for entry in report['inventory']}
    require(len(recorded) == report['files_scanned'], 'reported scan count differs from its inventory')
    require(present - set(POST_SCAN) <= set(recorded), 'scan inventory omits a publication target')
    require(set(seal['retained_sha256']) - set(POST_SCAN) <= set(recorded), 'scan inventory omits a sealed artifact')

    patterns = publication.forms(canary)
    for name, entry in recorded.items():
        if name not in present:
            # A retained-only copy legitimately lacks non-publication build
            # products. An entry that cannot be recomputed may carry no evidence.
            require(entry['scanned'] is True and not entry['findings'], 'unverifiable scan entry: '+name)
            continue
        fresh = publication.scan_file(run/name, patterns, run)
        # Scan conclusions are cross-checked here; the seal binds the bytes.
        # events.ndjson grew by the terminal receipt after the scan, so a clean
        # superset implies its scanned prefix was clean too.
        require(fresh['findings'] == entry['findings'], 'recorded findings differ from recomputation: '+name)
        same({k: fresh[k] for k in ('streams', 'scanned', 'error')},
             {k: entry[k] for k in ('streams', 'scanned', 'error')},
             'recomputed scan status differs from the recorded entry: '+name)
    incomplete = [n for n, e in recorded.items() if not e['scanned']]
    disclosures = [{'path': n, **hit} for n, e in recorded.items() for hit in e['findings']]
    require(report['incompletely_scanned'] == incomplete, 'incomplete-scan list differs from its own inventory')
    require(report['gzip_streams_scanned'] == sum('gzip' in e['streams'] for e in recorded.values()),
            'reported gzip coverage differs from its own inventory')
    require(sorted(map(events.canonical, report['disclosures'])) == sorted(map(events.canonical, disclosures)),
            'reported disclosures differ from recomputation')
    require(report['accepted'] == (not incomplete and not disclosures), 'reported scan verdict differs from its own findings')

    same(final, publication.final_record(path('publication-scan.json'), canary, nonce), 'terminal publication record differs')
    require(final['finalization_order'] == list(publication.FINALIZATION), 'declared finalization order differs')
    for name in POST_SCAN:
        fresh = publication.scan_file(run/name, patterns, run)
        require(fresh['scanned'] and not fresh['findings'], 'post-scan artifact discloses the canary: '+name)
    require(publication.safe_record({k: v for k, v in final.items()
        if k not in {'schema_version', 'finalization_order'}}), 'terminal record shape is unrestricted')
    require(publication.safe_record(rows_payload(run)), 'terminal receipt shape is unrestricted')
    if summary['proof_accepted']:
        require('verdict.json' in seal['retained_sha256'], 'accepted proof is not retained')
    return report, final


def rows_payload(run):
    return episode.observations(run)[-1]['payload']


def check_proof(run, task, seal, path, read, receipt_of, rows, policy, config, expected,
                summary, transport, accounting, request, raw, transport_error, receipt_record):
    """Delegate mathematical acceptance to the frozen shared checker."""
    declared = summary['proof_accepted']
    same(summary, {'schema_version': 'r6-credential-summary-1', 'task_id': task.id, 'search_policy': contract.NAME,
        'case': policy['case'], 'proof_accepted': declared,
        'credential_receipt_accepted': receipt_record['exact_receipt'],
        'failure_stage': summary['failure_stage'], 'failure_phase': summary['failure_phase'],
        'failure_category': summary['failure_category'], 'error': summary['error'],
        'causal_attribution': 'unassigned; observed boundary only', 'scope': summary['scope']},
        'summary shape differs')
    if not declared:
        require('verdict.json' not in seal['retained_sha256'], 'rejected episode retains a proof verdict')
        boundary = transport_error if transport_error is not None else None
        if not receipt_record['exact_receipt']:
            require(summary['failure_category'] == 'credential_receipt_failure'
                and summary['failure_stage'] == 'credential-receipt', 'receipt failure boundary differs')
        else:
            require(boundary is not None and summary['failure_category'] == boundary.category
                and summary['failure_stage'] == boundary.stage, 'recorded failure boundary differs from recomputation')
        require(summary['failure_phase'] == contract.PHASES[summary['failure_stage']], 'failure phase mapping differs')
        return False
    require(transport_error is None and receipt_record['exact_receipt'], 'accepted proof over a rejected boundary')
    verdict = read('verdict.json')
    r6.jsonschema.validate(verdict, r6.read_json(r6.ROOT/'schema/credential-verdict.schema.json'))
    packet = read('evidence.json')
    same(packet, read('stages/assembly/output/evidence.json'), 'assembled packet changed')
    cert = packet['certificate']
    same(cert['payload']['witness_data'], read('validated-response.json')['witness'], 'proposed and assembled witnesses differ')
    # The assembler is the frozen R6-003 component, so its envelope binds that
    # policy; this policy chains to it through `previous_policy_sha256`.
    same(cert['backend'], {'name': config['certificate_backend'], 'version': '1',
        'config_hash': 'sha256:'+r6.sha(contract.previous.CONFIG)}, 'certificate envelope policy')
    require(config['previous_policy_sha256'] == r6.sha(contract.previous.CONFIG), 'assembler policy chain')
    report = read('certificate-verdict.json')
    require(report.get('accepted') is True and report.get('reason') == {'kind': 'verified_farkas'}
        and report.get('certificate_hash') == 'sha256:'+events.digest(cert), 'independent certificate verification')
    same(report, verdict['certificate_validation'], 'certificate report/verdict mismatch')
    envelope_proof_audit.audit(task, packet, verdict, rows, path, read, receipt_of)
    flags = {'proof_accepted': True, 'search_succeeded': True, 'certificate_type': 'farkas', 'trust_tier': 1,
        'certificate_verified': True, 'certificate_consumed': True, 'derivation_replayed': False,
        'residual_closer': 'omega', 'proof_replayed': True, 'local_obligation_closed': True,
        'whole_declaration_validated': True, 'witness_proposer': config['witness_proposer'],
        'certificate_assembler': config['certificate_assembler'], 'recovery_route': config['name'],
        'local_proof_required_reference': episode.FARKAS_HELPER, 'prompt_sha256': r6.sha(path('prompt.txt')),
        'request_sha256': wire.sha(request), 'response_sha256': wire.sha(raw),
        'canary_nonce': read('credential-canary.json')['nonce'],
        'credential_receipt_sha256': r6.sha(path('credential-receipt.json'))}
    for key, value in flags.items(): same(verdict[key], value, 'verdict evidence claim differs: '+key)
    same(verdict['transport_validation'], transport, 'verdict transport checks differ')
    same(verdict['accounting'], accounting, 'verdict accounting differs')
    require(set(verdict['resources']) == set(STAGES), 'stage resource inventory')
    for stage in STAGES:
        spec, stats = read(f'stages/{stage}/command.json'), read(f'stages/{stage}/{stage}.process.json')
        same(stats, verdict['resources'][stage], 'stage resource/verdict mismatch')
        same(stats, receipt_of(stage, 'stage_finished'), 'stage resource/receipt mismatch')
        require(stats['exit_code'] == 0 and stats['resource_exhausted'] is None and stats.get('monitor_error') is None
            and stats.get('observation_error') is None and stats.get('workload_empty_after_cleanup') is True, 'unhealthy stage')
        require(not resource_violations(spec, stats.get('execution_wall_seconds', stats['wall_seconds']),
            stats['cgroup_cpu_usec'], stats['memory_events'], stats['output_bytes']), 'stage exceeded budget')
    same(receipt_of('episode', 'proof_validated'), {'verdict_sha256': r6.sha(path('verdict.json')),
        'proof_accepted': True, 'solution_sha256': verdict['solution_sha256']}, 'proof receipt differs')
    return True
