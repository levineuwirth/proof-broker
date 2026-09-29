"""Explicit identities for the two frozen deterministic controls.

Task selection chooses a registered identity, never a candidate-supplied path,
declaration name, source transform, or acceptance policy.
"""
from dataclasses import dataclass
from pathlib import Path

ROOT=Path(__file__).resolve().parent


@dataclass(frozen=True)
class Task:
    id: str
    path: Path
    local: str
    whole: str
    source_hash: str
    anchor: str
    goal: str
    capture: Path
    manifest_schema: str
    required_route: str
    weaker_numeral: tuple[str,str]


D1=Task('verinf-d1-70',ROOT/'tasks/verinf-d1-70',
        'Bracket.lift_cell.r6_d1_70','Bracket.lift_cell',
        '03b4d5ca39f435b0eed7d79fe70e9cc33c401fc7ec240a4120a194b54de722a2',
        '    have hle : (2:ℕ)^24 + 2 * Zmax ≤ P := by omega',
        '(2:ℕ)^24 + 2 * Zmax ≤ P',ROOT/'capture/Capture.lean',
        'task-manifest.schema.json','bounded_enumeration',('16777216','16777215'))
C8=Task('c1-c8-2p18',ROOT/'tasks/c1-c8-2p18',
        'R6.C8.coefficient_bound.r6_c8','R6.C8.coefficient_bound',
        '42d55407f02d104db111a21d1bfbc0a70ea7e3b9bdd8386169d8f7180e06670e',
        '  have hlt : 2^18 * g_hi.val < P := by omega',
        '2^18 * g_hi.val < P',ROOT/'tasks/c1-c8-2p18/Capture.lean',
        'task-control.schema.json','exact_support_bounded',
        ('18446744069414584321','18446744069414584322'))
TASKS={task.id:task for task in [D1,C8]}


def get(task_id):
    try:
        return TASKS[task_id]
    except (KeyError,TypeError) as error:
        raise ValueError(f'Unregistered R6 task: {task_id}') from error
