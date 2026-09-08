"""Recheck the September 8 review's preserved evidence and publication selection."""
import ast
from collections import Counter
import inspect
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import run as r6
import episode
import instrument
import audit_episode
import events
import c8_control
import test_review
import test_task_initialization


def main():
    review = Path(__file__).resolve().parent
    output = review/'final-checks.json'
    r6.write_json(output, {'passed': False, 'status': 'running'})
    snapshot = r6.read_json(review/'pre-review-files.sha256.json')
    supplement = r6.read_json(review/'preservation-supplement.sha256.json')
    earlier = r6.read_json(review.parent/'2026-09-07/pre-c8-files.sha256.json')
    notice = 'tasks/verinf-d1-70/NOTICE.md'
    assert supplement == {notice: earlier['experiments/r6/'+notice]}
    assert not snapshot.keys() & supplement.keys()
    preserved = {**snapshot, **supplement}
    # Preserve the earlier non-bytecode guard as well as the reviewed snapshot.
    for name, digest in earlier.items():
        path = Path(name)
        if '__pycache__' not in path.parts:
            assert preserved[str(path.relative_to('experiments/r6'))] == digest, name
    changed = [name for name, digest in preserved.items()
               if not (ROOT/name).is_file() or r6.sha(ROOT/name) != digest]
    assert not changed, changed

    modules = {m.__name__: m for m in [r6, episode, instrument, audit_episode, events, c8_control]}
    modules['r6'] = r6
    call_count = 0
    for path in [*ROOT.glob('*.py'), *(ROOT/'reviews/2026-09-07').glob('*_probe.py'), Path(__file__).resolve()]:
        tree = ast.parse(path.read_text(), filename=str(path))
        compile(tree, str(path), 'exec')
        local = modules.get(path.stem)
        for node in ast.walk(tree):
            if (not isinstance(node, ast.Call) or any(isinstance(a, ast.Starred) for a in node.args)
                    or any(k.arg is None for k in node.keywords)):
                continue
            fn, target = node.func, None
            if isinstance(fn, ast.Attribute) and isinstance(fn.value, ast.Name) and fn.value.id in modules:
                target = getattr(modules[fn.value.id], fn.attr, None)
            elif isinstance(fn, ast.Name) and local:
                target = getattr(local, fn.id, None)
            if not inspect.isfunction(target) or 'task' not in inspect.signature(target).parameters:
                continue
            inspect.signature(target).bind(*[None for _ in node.args], **{k.arg: None for k in node.keywords})
            call_count += 1

    checks, required = {}, set()
    for name, suite in [('further-review-v3', test_review), ('task-initialization-v1', test_task_initialization)]:
        path = ROOT/'runs'/name
        report = r6.read_json(path/'tests.json')
        counts = Counter(r['case'] for r in report['checks'])
        assert report['passed'] is True and set(counts) == suite.EXPECTED_CASES
        assert set(report['expected_cases']) == suite.EXPECTED_CASES
        assert all(n == 1 for n in counts.values()) and all(r['passed'] is True for r in report['checks'])
        for relative, digest in report['artifact_sha256'].items():
            file = path/relative
            assert r6.sha(file) == digest, file
            required.add(str(file.relative_to(ROOT.parents[1])))
        for source in (path/'provenance').rglob('*'):
            if source.is_file():
                assert source.read_bytes() == (ROOT/source.relative_to(path/'provenance')).read_bytes(), source
        checks[name] = {'passed': True, 'cases': len(counts), 'artifacts': len(report['artifact_sha256']),
                        'tests_sha256': r6.sha(path/'tests.json'), 'provenance_matches_current_sources': True}
        required.add(str((path/'tests.json').relative_to(ROOT.parents[1])))
    for name in ['golden-broker-v1', 'golden-broker-v2', 'golden-broker-v3', 'golden-c8-v1']:
        path = ROOT/'runs'/name
        for relative in [*r6.read_json(path/'seal.json')['retained_sha256'], 'seal.json']:
            required.add(str((path/relative).relative_to(ROOT.parents[1])))
    for task in r6.TASKS.values():
        manifest, _ = r6.frozen_task(task)
        for relative in [*manifest['artifacts_sha256'], 'manifest.json']:
            required.add(str((task.path/relative).relative_to(ROOT.parents[1])))
    selected = subprocess.check_output(['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard',
                                        '--', 'experiments/r6'], cwd=ROOT.parents[1]).split(b'\0')
    # Exclude this self-describing output to avoid circular byte counts.
    selected = sorted({ROOT.parents[1]/p.decode() for p in selected if p} - {output})
    # Include every selected run's declared inputs, including historical suites.
    # This checks packaging without comparing historical sources to today's code.
    publication_reports = 0
    for path in selected:
        if not path.is_relative_to(ROOT/'runs') or path.name not in {'tests.json', 'seal.json'}:
            continue
        report = r6.read_json(path)
        publication_reports += 1
        required.add(str(path.relative_to(ROOT.parents[1])))
        inventories = [(path.parent, report.get('artifact_sha256', {})),
                       (path.parent, report.get('retained_sha256', {}))]
        if 'native_artifact_sha256' in report:
            inventories.append((Path(report['native_resource_run']), report['native_artifact_sha256']))
        for base, inventory in inventories:
            for name, digest in inventory.items():
                file = base/name
                assert r6.sha(file) == digest, file
                required.add(str(file.relative_to(ROOT.parents[1])))
    ignored = subprocess.run(['git', 'check-ignore', '--no-index', '--stdin'], cwd=ROOT.parents[1],
                             input='\n'.join(sorted(required))+'\n', text=True, capture_output=True)
    assert ignored.returncode == 1 and not ignored.stdout, ignored.stdout+ignored.stderr

    docs = [ROOT/'PROTOCOL.md', ROOT/'tasks/c1-c8-2p18/NOTICE.md',
            ROOT/'reviews/2026-09-07/C8-CONTROL.md', review/'REVIEW.md']
    for path in docs:
        for target in re.findall(r'\]\(([^)]+)\)', path.read_text()):
            if '://' in target or target.startswith('#'):
                continue
            dest = (path.parent/target.split('#')[0]).resolve()
            assert dest.exists() or dest == output, (path, target)
    subprocess.run(['git', 'diff', '--check'], cwd=ROOT.parents[1], check=True)

    unique = {r6.sha(p): p.stat().st_size for p in selected}
    result = {'passed': True, 'preserved_files': len(preserved), 'changed_or_missing': changed,
              'original_snapshot_files': len(snapshot), 'supplemental_files': len(supplement),
              'preservation_snapshot_sha256': r6.sha(review/'pre-review-files.sha256.json'),
              'preservation_supplement_sha256': r6.sha(review/'preservation-supplement.sha256.json'),
              'preservation_exclusions': ['tasks/c1-c8-2p18/NOTICE.md (explicitly amended)',
                                          '__pycache__ entries (regenerable bytecode)'],
              'python_compile': 'passed', 'explicit_task_call_sites_bound': call_count,
              'test_reports': checks, 'publication_reports_checked': publication_reports,
              'required_publication_paths': len(required), 'ignored_required_paths': [],
              'documentation_links': 'passed', 'git_diff_check': 'passed',
              'publication_selection': {'files': len(selected), 'apparent_bytes': sum(p.stat().st_size for p in selected),
                                       'unique_contents': len(unique), 'unique_content_bytes': sum(unique.values()),
                                       'excludes': [str(output.relative_to(ROOT))],
                                       'qualification': 'uncompressed content bytes, not Git pack, disk, or transfer size'},
              'kernel_reexecuted': False, 'golden_episode_reexecuted': False,
              'conformance_reexecuted': False, 'completion_mutations_reexecuted': False,
              'native_positive_stages_reexecuted': 2, 'compilation_or_inference_attestation': False}
    r6.write_json(output, result)
    print(result)


if __name__ == '__main__':
    main()
