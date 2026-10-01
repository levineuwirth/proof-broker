#!/usr/bin/env python3
"""The driver's two gates, exercised without a lock, an export or a retained record: the regression gate
(`regression_passed`, the build review's finding 4) and the toolchain-content binding (`tree_digest` and
`controls_bridge_environment`, finding 5). Synthetic records and trees in a temporary directory; the driver's module globals are
patched for each case and restored."""
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
    return {'audit': {'local': {'classification': local}, 'whole': {'classification': whole, 'hypotheses': hypotheses}}}


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
        r = {'application': 'regression', 'reproduced': True, 'differences': {}, 'results': copy.deepcopy(RESULTS),
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

    def test_the_controls_bridge_import_is_bound_by_content(self):
        bridge = self.tmp/'bridge'
        shutil.copytree(q.BRIDGE_ENVIRONMENT/'ProofBroker', bridge/'ProofBroker',
                        ignore=lambda d, names: [n for n in names if n != 'TermMode.olean'])
        with mock.patch.object(q, 'BRIDGE_ENVIRONMENT', bridge):
            env = q.controls_bridge_environment()
            self.assertEqual(env['header'], ['Lean', 'ProofBroker.TermMode'])
            self.assertEqual(list(env['modules']), ['ProofBroker.TermMode'])
            self.assertEqual(env['modules']['ProofBroker.TermMode']['imports'], ['Init'])
            with open(bridge/'ProofBroker/TermMode.olean', 'ab') as f: f.write(b'\0')
            self.assertNotEqual(env, q.controls_bridge_environment())

    def test_an_import_found_nowhere_refuses(self):
        with mock.patch.object(q, 'BRIDGE_ENVIRONMENT', self.tmp/'empty'):
            with self.assertRaises(SystemExit) as e: q.controls_bridge_environment()
        self.assertIn('ProofBroker.TermMode, found nowhere bound', str(e.exception))


if __name__ == '__main__':
    unittest.main()
