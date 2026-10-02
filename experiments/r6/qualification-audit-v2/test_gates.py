#!/usr/bin/env python3
"""The driver's gates, exercised without a lock, an export or a retained record:
- the regression gate (`regression_passed`; revision 3's review, finding 4), with each report validated (`report_invalid`;
  revision 4's review, finding 1);
- the toolchain-content binding (`tree_digest`; revision 3's review, finding 5), with the controls' environment resolved in Lean's
  search order (`resolve`, `controls_environment`; revision 4's review, finding 2).
Synthetic records and trees in a temporary directory; the driver's module globals are patched for each case and restored."""
import copy
import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location('qualification_audit_v2', HERE/'qualification_audit_v2.py')
q = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(q)


def slot(local, whole, hypotheses):
    return {'exit': 0, 'environment': {'mode': 'real', 'lean': '4.32.2'},
            'audit': {'binding': 'matches_residual', 'local': {'classification': local, 'locatable': True},
                      'whole': {'classification': whole, 'hypotheses': hypotheses, 'locatable': True}}}


V1 = {'k1': {'local': 'necessary', 'whole': 'necessary', 'whole_hypotheses': [{'name': 'h', 'path': ['parameter 1 of L']}]},
      'k2': {'local': 'unnecessary', 'whole': 'unnecessary', 'whole_hypotheses': []}}
FROZEN = {'selection': {'regression': {k: {'v1': v} for k, v in V1.items()}}}
RESULTS = {k: slot(v['local'], v['whole'], v['whole_hypotheses']) for k, v in V1.items()}


class RegressionGate(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix='r6-qual-v2-gates-'))
        self.lock = self.tmp/'lock.json'; self.lock.write_text('{"synthetic": true}\n')
        self.patch = mock.patch.object(q, 'LOCK', self.lock); self.patch.start()

    def tearDown(self):
        self.patch.stop(); shutil.rmtree(self.tmp)

    def record(self, name='record.json', **changes):
        r = {'application': 'regression', 'reproduced': True, 'invalid': {}, 'differences': {}, 'results': copy.deepcopy(RESULTS),
             'lock_sha256': q.sha(self.lock)}
        r.update(changes)
        p = self.tmp/name; p.write_text(json.dumps(r)); return p

    def refused(self, path, reason):
        with self.assertRaises(SystemExit) as e: q.regression_passed(path, FROZEN)
        self.assertIn(reason, str(e.exception))

    def test_passing_record_is_accepted_and_bound(self):
        p = self.record()
        self.assertEqual(q.regression_passed(p, FROZEN), q.sha(p))

    def test_another_application(self):
        self.refused(self.record(application='addendum2'), "not this lock's")

    def test_another_lock(self):
        self.refused(self.record(lock_sha256='0' * 64), "not this lock's")

    def test_missing_slot(self):
        results = copy.deepcopy(RESULTS); del results['k2']
        self.refused(self.record(results=results), 'cover exactly')

    def test_extra_slot(self):
        results = copy.deepcopy(RESULTS); results['k3'] = RESULTS['k1']
        self.refused(self.record(results=results), 'cover exactly')

    def test_a_difference_in_the_results_although_the_flags_say_passed(self):
        results = copy.deepcopy(RESULTS); results['k1']['audit']['whole']['classification'] = 'unnecessary'
        self.refused(self.record(results=results), 'did not pass')

    def test_a_mapping_difference(self):
        results = copy.deepcopy(RESULTS); results['k1']['audit']['whole']['hypotheses'][0]['path'] = ['internal to the local proof']
        self.refused(self.record(results=results), 'did not pass')

    def test_a_failed_report(self):
        results = copy.deepcopy(RESULTS); results['k2'] = {'error': 'no report', 'exit': 1}
        self.refused(self.record(results=results), 'did not pass')

    def test_flags_inconsistent_with_passing_results(self):
        self.refused(self.record(reproduced=False), 'did not pass')
        self.refused(self.record(name='r2.json', differences={'k1': {}}), 'did not pass')
        self.refused(self.record(name='r3.json', reproduced=None), 'did not pass')
        self.refused(self.record(name='r4.json', invalid={'k1': ['x']}), 'did not pass')
        r = json.loads(self.record(name='r5.json').read_text()); del r['invalid']
        (self.tmp/'r5.json').write_text(json.dumps(r)); self.refused(self.tmp/'r5.json', 'did not pass')

    # revision 4's review, finding 1: matching classifications and mappings in a report that is not a valid execution
    def invalid_report(self, change):
        results = copy.deepcopy(RESULTS); change(results['k1'])
        self.assertTrue(q.report_invalid(results['k1'], FROZEN['selection']['regression']['k1']))
        invalid, differences = q.regression_verdict(FROZEN, results)
        self.assertEqual((list(invalid), differences), (['k1'], {}))
        self.refused(self.record(results=results), 'did not pass')

    def test_exit_one(self): self.invalid_report(lambda r: r.update(exit=1))
    def test_boolean_exit(self):
        self.invalid_report(lambda r: r.update(exit=False))
        self.invalid_report(lambda r: r.update(exit=True))
    def test_missing_exit(self): self.invalid_report(lambda r: r.pop('exit'))
    def test_refused(self): self.invalid_report(lambda r: r.update(refused='constants differ'))
    def test_error(self): self.invalid_report(lambda r: r.update(error='no report'))
    def test_synthetic_mode(self): self.invalid_report(lambda r: r['environment'].update(mode='synthetic'))
    def test_another_lean(self): self.invalid_report(lambda r: r['environment'].update(lean='4.32.0'))
    def test_unbound(self): self.invalid_report(lambda r: r['audit'].update(binding='residual_mismatch'))
    def test_renamed_binding_without_a_rename(self):
        self.invalid_report(lambda r: r['audit'].update(binding='matches_residual_after_renaming'))
    def test_local_not_locatable(self): self.invalid_report(lambda r: r['audit']['local'].update(locatable=False))
    def test_whole_not_locatable(self): self.invalid_report(lambda r: r['audit']['whole'].pop('locatable'))
    def test_no_audit(self): self.invalid_report(lambda r: r.pop('audit'))

    def test_a_valid_report(self):
        self.assertEqual(q.report_invalid(RESULTS['k1'], FROZEN['selection']['regression']['k1']), [])
        self.assertEqual(q.regression_verdict(FROZEN, RESULTS), ({}, {}))


class ToolchainContents(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix='r6-qual-v2-trees-'))

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def test_tree_digest_sees_content_names_and_additions(self):
        root = self.tmp/'tree'; (root/'lib').mkdir(parents=True)
        (root/'lib/a.olean').write_bytes(b'a'); (root/'bin').mkdir(); (root/'bin/lean').write_bytes(b'lean')
        base = q.tree_digest(root)
        self.assertEqual(base, q.tree_digest(root))
        (root/'lib/a.olean').write_bytes(b'b'); self.assertNotEqual(base, q.tree_digest(root))
        (root/'lib/a.olean').write_bytes(b'a'); self.assertEqual(base, q.tree_digest(root))
        (root/'lib/a.olean').rename(root/'lib/b.olean'); self.assertNotEqual(base, q.tree_digest(root))
        (root/'lib/b.olean').rename(root/'lib/a.olean'); (root/'lib/c.olean').write_bytes(b'')
        self.assertNotEqual(base, q.tree_digest(root))

    def bridge(self, *extra):
        """A copy of the bridge's `TermMode.olean` alone, with `extra` (path, content or None for a directory) added."""
        bridge = self.tmp/'bridge'
        shutil.copytree(q.BRIDGE_ENVIRONMENT/'ProofBroker', bridge/'ProofBroker',
                        ignore=lambda d, names: [n for n in names if n != 'TermMode.olean'])
        for rel, content in extra:
            if content is None: (bridge/rel).mkdir(parents=True)
            else: (bridge/rel).write_bytes(content)
        return bridge

    def build(self, *extra):
        """A copy of the build's controls directory: the controls' `.olean` alone, with `extra` added."""
        build = self.tmp/'build'; (build/'controls').mkdir(parents=True)
        shutil.copyfile(q.BUILD/'controls/R6AuditControlsV2.olean', build/'controls/R6AuditControlsV2.olean')
        for rel, content in extra:
            if content is None: (build/'controls'/rel).mkdir(parents=True)
            else: (build/'controls'/rel).write_bytes(content)
        return build

    def environment(self, bridge, build):
        with mock.patch.object(q, 'BRIDGE_ENVIRONMENT', bridge), mock.patch.object(q, 'BUILD', build), \
             mock.patch.object(q, 'REPO', self.tmp):
            return q.controls_environment()

    def refuses(self, bridge, build, reason):
        with self.assertRaises(SystemExit) as e: self.environment(bridge, build)
        self.assertIn(reason, str(e.exception))

    def test_the_controls_environment_is_bound_by_content(self):
        bridge, build = self.bridge(), self.build()
        env = self.environment(bridge, build)
        self.assertEqual({m: e['directory'] for m, e in env['modules'].items()},
                         {'Init': 'toolchain', 'Lean': 'toolchain', 'ProofBroker.TermMode': 'bridge', 'R6AuditControlsV2': 'build/controls'})
        self.assertEqual(env['modules']['ProofBroker.TermMode']['imports'], ['Init'])
        self.assertEqual(env['modules']['R6AuditControlsV2']['imports'], ['Init', 'Lean', 'ProofBroker.TermMode'])
        with open(bridge/'ProofBroker/TermMode.olean', 'ab') as f: f.write(b'\0')
        self.assertNotEqual(env, self.environment(bridge, build))

    def test_a_part_beside_the_olean_is_bound(self):
        bridge, build = self.bridge(), self.build()
        env = self.environment(bridge, build)
        (bridge/'ProofBroker/TermMode.olean.private').write_bytes(b'')
        self.assertNotEqual(env, self.environment(bridge, build))

    # revision 4's review, finding 2: a toolchain package shadowed earlier in the search path
    def test_a_bridge_side_init_olean_refuses(self):
        self.refuses(self.bridge(('Init.olean', b'')), self.build(), "toolchain's packages are shadowed")

    def test_a_bridge_side_package_directory_refuses(self):
        self.refuses(self.bridge(('Lean', None)), self.build(), "toolchain's packages are shadowed")

    def test_a_controls_side_shadow_refuses(self):
        self.refuses(self.bridge(), self.build(('Init', None)), "toolchain's packages are shadowed")
        shutil.rmtree(self.tmp/'bridge'); shutil.rmtree(self.tmp/'build')
        self.refuses(self.bridge(), self.build(('Std.olean', b'')), "toolchain's packages are shadowed")

    def test_the_controls_module_shadowed_by_the_bridge_refuses(self):
        olean = (q.BUILD/'controls/R6AuditControlsV2.olean').read_bytes()
        self.refuses(self.bridge(('R6AuditControlsV2.olean', olean)), self.build(), "resolves outside the controls' directory")

    def test_no_fallthrough_past_the_root_package(self):
        # Lean picks the first directory holding the root package; a module missing there is not looked for further on
        a, b = self.tmp/'a', self.tmp/'b'; (a/'Foo').mkdir(parents=True); (b/'Foo').mkdir(parents=True); (b/'Foo/Bar.olean').write_bytes(b'')
        self.assertEqual(q.resolve('Foo.Bar', [a, b]), (a, a/'Foo/Bar.olean'))
        self.assertEqual(q.resolve('Foo.Bar', [self.tmp/'c', b]), (b, b/'Foo/Bar.olean'))
        self.assertEqual(q.resolve('Baz', [a, b]), (None, None))
        bridge = self.tmp/'bridge'; (bridge/'ProofBroker').mkdir(parents=True)
        build = self.build(('ProofBroker', None))
        shutil.copyfile(q.BRIDGE_ENVIRONMENT/'ProofBroker/TermMode.olean', build/'controls/ProofBroker/TermMode.olean')
        self.refuses(bridge, build, 'ProofBroker.TermMode does not resolve')

    def test_an_import_found_nowhere_refuses(self):
        self.refuses(self.tmp/'empty', self.build(), 'ProofBroker.TermMode does not resolve')


if __name__ == '__main__':
    unittest.main()
