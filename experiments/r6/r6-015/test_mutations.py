#!/usr/bin/env python3
"""R6-015 step 3, revision 2: regression tests for the review of step 3 (`reviews/2026-10-01/R6-015-STEP-3-REVIEW.md`).

Reads retained evidence only; nothing is replayed and no closer runs. Run: `python3 r6-015/test_mutations.py` (or under pytest).
"""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
R6 = HERE.parent
if str(R6) not in sys.path: sys.path.insert(0, str(R6))
if str(HERE) not in sys.path: sys.path.insert(0, str(HERE))

import mutations  # noqa: E402
import replay_episode  # noqa: E402


def test_seal_failure_propagates():
    """The review's probe: a seal failure at deterministic l069 must not read as an absent certificate."""
    original = replay_episode.sealed
    def broken(run, name):
        if Path(run).name == 'bracket-l069': raise ValueError('synthetic seal failure')
        return original(run, name)
    replay_episode.sealed = broken
    try:
        src = mutations.source('l069', 'deterministic')
        for call in (mutations.deterministic_absence, mutations.packet_of):
            try:
                call(src)
            except ValueError as caught:
                assert 'synthetic seal failure' in str(caught)
            else:
                raise AssertionError(f'{call.__name__} accepted a seal failure')
    finally:
        replay_episode.sealed = original


def test_absence_is_explicit():
    for site in ('l096', 'l099'):
        assert mutations.deterministic_absence(mutations.source(site, 'deterministic')) is not None, site
    for site in ('l069', 'l070', 'l071', 'l078', 'l166', 'l175', 'l178', 'l204'):
        assert mutations.deterministic_absence(mutations.source(site, 'deterministic')) is None, site


def test_deterministic_maps():
    """The review's corrected maps, read from the sealed deterministic packets."""
    assert mutations.map_of(mutations.source('l070', 'deterministic')) == {'hZ': '2', 'neg_goal': '1'}
    assert mutations.map_of(mutations.source('l071', 'deterministic')) == {'hZ': '2', 'hzsum': '1', 'neg_goal': '1'}


if __name__ == '__main__':
    for test in (test_seal_failure_propagates, test_absence_is_explicit, test_deterministic_maps):
        test(); print(test.__name__, 'passed')
