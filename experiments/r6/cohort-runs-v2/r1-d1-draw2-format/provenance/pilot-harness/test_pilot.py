#!/usr/bin/env python3
"""R6-007 focused controls for the live boundary, before any provider request."""
import argparse
import copy
import json
from pathlib import Path
import types

import pilot_contract as contract
import pilot_https as actor
import pilot_network as netstage
import run as r6
from test_proposals import Suite, rejected, require

CASES = '''policy_frozen_disabled authorization_required authorization_scope authorization_subject
live_requires_flag_and_record ca_bundle_pinned live_refuses_fixture rehearsal_requires_fixture
ledger_ceiling_is_one_attempt attribution_versioned model_is_dated_snapshot
network_stage_keeps_every_other_namespace network_stage_shares_only_net network_stage_declares_scope
other_stages_stay_unshared no_environment_credential endpoint_allowlist_exact'''.split()


def units(output):
    suite = Suite(output, CASES)
    c = contract.config()

    def frozen_disabled():
        require(c['live_enabled'] is False and c['authorization'] is None, 'policy is not frozen disabled')
        require(c['live_model_calls_authorized'] == 0)
        return {'live_enabled': False, 'authorization': None,
                'scope': 'a live destination is unreachable until the author signs a new frozen policy'}
    suite.case('policy_frozen_disabled', frozen_disabled)

    def signed(**overrides):
        record = {'approved_by': 'author', 'approved_utc': '2026-09-10T00:00:00Z', 'model_id': contract.MODEL,
                  'maximum_attempts': 1, 'maximum_micro_usd': contract.ATTEMPT_MICRO_USD,
                  'scope': 'one provider request'}
        record.update(overrides)
        return {**copy.deepcopy(c), 'live_enabled': True, 'authorization': record}

    suite.case('authorization_required',
               lambda: rejected(lambda: actor.live_authorization({**copy.deepcopy(c), 'live_enabled': True}),
                                'pilot_authorization_absent'))
    suite.case('authorization_scope',
               lambda: rejected(lambda: actor.live_authorization(signed(maximum_attempts=2)),
                                'pilot_authorization_scope'))
    suite.case('authorization_subject',
               lambda: rejected(lambda: actor.live_authorization(signed(model_id='gpt-5.4')),
                                'pilot_authorization_subject'))

    def flag_and_record():
        rejected(lambda: actor.live_authorization(c), 'pilot_live_disabled')
        rejected(lambda: contract.live_permitted(c), 'pilot_live_disabled')
        require(actor.live_authorization(signed())['maximum_attempts'] == 1)
        require(contract.authorization(signed())['maximum_micro_usd'] == contract.ATTEMPT_MICRO_USD)
        return {'flag_alone_insufficient': True, 'record_alone_insufficient': True}
    suite.case('live_requires_flag_and_record', flag_and_record)

    def ca_pinned():
        path, described = contract.bundle()
        require(described['sha256'] == c['tls']['public_ca_bundle']['sha256'], 'pinned bundle digest drifted')
        require(described['certificates'] > 0 and described['bytes'] == c['tls']['public_ca_bundle']['bytes'])
        require(c['tls']['verify_mode'] == 'CERT_REQUIRED' and c['tls']['check_hostname'] is True
                and c['tls']['minimum_version'] == 'TLSv1.2')
        return {'bundle': str(path), 'certificates': described['certificates'],
                'sha256': described['sha256'], 'checked_inside_actor': True}
    suite.case('ca_bundle_pinned', ca_pinned)

    def parser_guards(argv, contains):
        parsed = types.SimpleNamespace()
        import argparse as ap
        try:
            saved = ap.ArgumentParser.error
            ap.ArgumentParser.error = lambda self, message: (_ for _ in ()).throw(ValueError(message))
            import sys
            saved_argv = sys.argv
            sys.argv = ['pilot_https.py', *argv]
            return rejected(actor.main, contains)
        finally:
            ap.ArgumentParser.error = saved
            sys.argv = saved_argv

    base = ['--policy', '/p', '--arguments', '/a', '--credential-file', '/c', '--ca', '/ca',
            '--out', '/o', '--sources', '/s', '--permit', '/pm', '--ledger', '/l',
            '--request', '/r', '--episode', 'e']
    suite.case('live_refuses_fixture',
               lambda: parser_guards(['--mode', 'live', *base, '--fixture', '/f'], 'refuses fixture'))
    suite.case('rehearsal_requires_fixture',
               lambda: parser_guards(['--mode', 'rehearsal', *base], 'requires --fixture'))

    def ceiling():
        require(c['limits']['total_micro_usd'] == contract.ATTEMPT_MICRO_USD == 102400)
        require(c['limits']['campaign_attempts'] == 1 and c['limits']['attempts_per_episode'] == 1)
        require(c['limits']['automatic_retries'] == 0 and c['limits']['redirects'] == 0)
        return {'ledger_ceiling_micro_usd': 102400, 'attempts': 1,
                'scope': 'the ledger cannot fund a second attempt even if something retries'}
    suite.case('ledger_ceiling_is_one_attempt', ceiling)

    def attribution():
        require(c['attribution']['witness_proposer'] == 'live_model_response')
        require(c['attribution']['witness_proposer'] != 'canned_provider_response', 'canned identity reused')
        return c['attribution']
    suite.case('attribution_versioned', attribution)

    def dated():
        require(c['model']['requested_id'] == c['model']['allowed_response_ids'][0] == 'gpt-5.4-2026-03-05')
        require(c['model']['model_computation_attested'] is False)
        return {'model': c['model']['requested_id'], 'revision_status': c['model']['revision_status']}
    suite.case('model_is_dated_snapshot', dated)

    run = Path('/tmp/r6-pilot-command-probe')
    cmd, spec = netstage.command(run, 'proposal-1', Path(__file__), ['--x'], [], wall=60, cpu=5,
                                 memory=1 << 28, output_limit=1 << 20)

    def keeps_namespaces():
        for flag in netstage.NAMESPACES:
            require(flag in cmd, 'dropped namespace: '+flag)
        for flag in ('--cap-drop', '--clearenv', '--new-session', '--die-with-parent'):
            require(flag in cmd, 'dropped hardening: '+flag)
        return {'namespaces_retained': list(netstage.NAMESPACES)}
    suite.case('network_stage_keeps_every_other_namespace', keeps_namespaces)

    def only_net():
        require('--unshare-net' not in cmd and '--unshare-all' not in cmd, 'network stage still unshares net')
        require(cmd.count('--ro-bind') >= 1 and netstage.RESOLVER in cmd, 'resolver not mounted')
        return {'network_namespace': 'shared', 'resolver_mounted': netstage.RESOLVER}
    suite.case('network_stage_shares_only_net', only_net)

    suite.case('network_stage_declares_scope',
               lambda: require(spec['network_namespace'] == 'shared_with_host'
                               and 'not an egress filter' in spec['network_scope']) or spec['network_scope'])

    def others_unshared():
        import episode
        source = Path(episode.__file__).read_text()
        require("'--unshare-all'" in source, 'shared stage builder changed')
        require('--unshare-all' not in cmd, 'pilot stage reused the shared builder')
        return {'shared_builder_unchanged': True, 'pilot_stage_is_separate': True}
    suite.case('other_stages_stay_unshared', others_unshared)

    def no_env_credential():
        text = Path(actor.__file__).read_text()
        require('environ' not in text and 'getenv' not in text, 'actor reads the environment')
        require(c['credential']['operator_supplied'] is True and c['credential']['retained'] is False)
        return {'environment_read': False, 'channel': c['credential']['channel']}
    suite.case('no_environment_credential', no_env_credential)

    def endpoint():
        require(c['endpoint'] == contract.ENDPOINT)
        require(c['network']['egress_restriction_enforced_by_harness'] is False,
                'the policy must not claim an egress filter it does not have')
        return {'endpoint': c['endpoint'], 'enforced_by': 'actor endpoint check and audited command'}
    suite.case('endpoint_allowlist_exact', endpoint)
    suite.finish()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise SystemExit('Refusing to overwrite: '+str(args.output))
    units(args.output.resolve())
    print(json.dumps({'passed': True, 'cases': len(CASES)}, indent=1))


if __name__ == '__main__':
    main()
