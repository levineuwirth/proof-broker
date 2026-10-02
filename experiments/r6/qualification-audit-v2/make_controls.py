#!/usr/bin/env python3
"""Generate `R6AuditControlsV2.lean`: `qualification-audit-v1`'s controls (its generator, `../qualification-audit/make_controls.py`,
imported unchanged: the pinned fold copied byte for byte from `e627efe`, and C1-C6), plus the synthetic controls of amendment 1
(`R6-QUALIFICATION-1-AUDIT-AMENDMENT-1-PROPOSAL.md`, revision 3): R1-R6 and R4b (one export with a binder named `c'`, audited
against several rename inputs), R7 in two variants, R7b, R7d, R8, R9, R9b and R10. Each local theorem is closed by the pinned fold; each whole
declaration refers to it by name, as R6's exports do.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('v1_make_controls', HERE.parent/'qualification-audit/make_controls.py')
v1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(v1)

ELABS = '''
-- amendment 1's controls: the review's probe pattern (`neg_goal` doubled), so that contextual `omega` refers to a hypothesis, and
-- the valid pattern
elab "fold_r_probe" : tactic => runComparison [("h", 1), ("neg_goal", 2)]
elab "fold_r_valid" : tactic => runComparison [("h", 1), ("neg_goal", 1)]
elab "fold_r_probe_hn" : tactic => runComparison [("hn", 1), ("neg_goal", 2)]
/-- R8's `False` goal: `h : x ≤ 0` and `hp : 0 < x`. -/
elab "fold_r8" : tactic => do
  let g ← getMainGoal
  closeViaTermModeFalse g [("h", 1), ("hp", 1)]
  replaceMainGoal []

end R6AuditFold'''

AMENDMENT = '''
/-! ## Amendment 1's controls -/

/-- R1-R6: a binder named `c'`. Audited against several rename inputs (the driver's `RENAMES`). -/
theorem r1_local (x c' : Int) (h : x ≤ c') : x ≤ c' := by fold_r_valid
theorem r1_whole (x c' : Int) (h : x ≤ c') : x ≤ c' := r1_local x c' h

/-- R7, with a declaration `let`: parameters `x`, `h`, `hn`; the value puts an internal `_q` between `x` and `h`. -/
theorem r7l_local : ∀ (x : Int), let y : Int := x + 0; ∀ (h : x ≤ 5) (hn : 0 ≤ y), x ≤ 5 :=
  fun x => let y : Int := x + 0; (fun (_q : True) => fun (h : x ≤ 5) (hn : 0 ≤ y) => by fold_r_probe) True.intro
theorem r7l_whole (x : Int) (h : x ≤ 5) (hn : 0 ≤ x + 0) : x ≤ 5 := r7l_local x h hn

/-- R7, without the `let`. -/
theorem r7n_local : ∀ (x : Int) (h : x ≤ 5) (hn : 0 ≤ x), x ≤ 5 :=
  fun x => (fun (_q : True) => fun (h : x ≤ 5) (hn : 0 ≤ x) => by fold_r_probe) True.intro
theorem r7n_whole (x : Int) (h : x ≤ 5) (hn : 0 ≤ x) : x ≤ 5 := r7n_local x h hn

/-- R7b, a value-only `let` between `x` and `h`. -/
theorem r7b_local : ∀ (x : Int) (h : x ≤ 5) (hn : 0 ≤ x), x ≤ 5 :=
  fun x => let _r : Int := 0; fun (h : x ≤ 5) (hn : 0 ≤ x) => by fold_r_probe
theorem r7b_whole (x : Int) (h : x ≤ 5) (hn : 0 ≤ x) : x ≤ 5 := r7b_local x h hn

/-- R7d, a dependent binder: an applied lambda's binder `q := x`, on which the next binders' types depend. -/
theorem r7d_local : ∀ (x : Int) (h : 0 < x) (hn : x ≤ 5), x ≤ 5 :=
  fun x => (fun (q : Int) => fun (h : 0 < q) (hn : q ≤ 5) => (show q ≤ 5 by fold_r_probe_hn)) x
theorem r7d_whole (x : Int) (h : 0 < x) (hn : x ≤ 5) : x ≤ 5 := r7d_local x h hn

/-- R10, a second fold in an applied lambda's argument (the build review's case): two fold applications in the value. -/
theorem r10_local : ∀ (x : Int) (h : x ≤ 5) (hn : 0 ≤ x), x ≤ 5 :=
  fun x => (fun (_q : x ≤ 5 → x ≤ 5) => fun (h : x ≤ 5) (hn : 0 ≤ x) => (show x ≤ 5 by fold_r_probe))
    (fun (h : x ≤ 5) => (show x ≤ 5 by fold_r_valid))
theorem r10_whole (x : Int) (h : x ≤ 5) (hn : 0 ≤ x) : x ≤ 5 := r10_local x h hn

/-- R8, an arity mismatch: the local's conclusion is `¬ (0 < x)`, two parameters; the whole applies it to three arguments. -/
theorem r8_local (x : Int) (h : x ≤ 0) : ¬ (0 < x) := by
  intro hp
  fold_r8
theorem r8_whole (x : Int) (h : x ≤ 0) (hp : 0 < x) : False := r8_local x h hp

/-- R9, an eta-reduced value: the local's value is a constant. -/
theorem r9_aux (x : Int) (h : x ≤ x) : x ≤ x := by fold_r_valid
theorem r9_local : ∀ (x : Int) (h : x ≤ x), x ≤ x := r9_aux
theorem r9_whole (x : Int) (h : x ≤ x) : x ≤ x := r9_local x h

/-- R9b, a declaration `let` met by a value `let` with a different value (unused, so both typecheck). -/
theorem r9b_local : ∀ (x : Int), let y : Int := 0; ∀ (h : x ≤ 5), x ≤ 5 :=
  fun x => let y : Int := 1; fun (h : x ≤ 5) => by fold_r_probe
theorem r9b_whole (x : Int) (h : x ≤ 5) : x ≤ 5 := r9b_local x h

end R6Audit
'''


def main():
    source = subprocess.run(['git', '-C', str(v1.REPO), 'show', f'{v1.PIN}:lean-bridge/ProofBroker/Tactic.lean'],
                            capture_output=True, text=True, check=True).stdout
    region = v1.fold_region(source)
    controls = v1.CONTROLS
    assert controls.count('\nend R6AuditFold') == 1 and controls.endswith('end R6Audit\n')
    controls = controls.replace('\nend R6AuditFold', ELABS, 1)
    controls = controls[:-len('end R6Audit\n')] + AMENDMENT.lstrip('\n')
    header = ('import Lean\nimport ProofBroker.TermMode\n\n'
              '/-! Generated by `qualification-audit-v2/make_controls.py`. The region between the markers is copied byte for byte from\n'
              f'    `lean-bridge/ProofBroker/Tactic.lean` at `{v1.PIN}`. -/\n\n'
              'set_option linter.unusedVariables false\n\n'
              'namespace R6AuditFold\n\nopen Lean Lean.Elab.Tactic Lean.Meta\n\n-- BEGIN pinned fold\n')
    text = header + region + '-- END pinned fold\n' + controls
    out = HERE/'R6AuditControlsV2.lean'
    out.write_text(text)
    (HERE/'R6AuditControlsV2.provenance.json').write_text(json.dumps({
        'pin': v1.PIN, 'source': 'lean-bridge/ProofBroker/Tactic.lean', 'declarations': v1.FOLD_DECLS,
        'region_sha256': hashlib.sha256(region.encode()).hexdigest(),
        'generated_sha256': hashlib.sha256(text.encode()).hexdigest(),
        'v1_generator_sha256': hashlib.sha256((HERE.parent/'qualification-audit/make_controls.py').read_bytes()).hexdigest()}, indent=1) + '\n')
    print(out, len(region.splitlines()), 'fold lines')


if __name__ == '__main__':
    main()
