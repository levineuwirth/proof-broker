# The axiom guard, for a Lean project that is not this one

`tools/check_axioms.py` + `tools/axiom_allowlist.json` are a
standalone proof-carrying-claims gate: they read a Lean build log and
fail if any pinned theorem's `#print axioms` footprint grew. This page
is what an external project needs; nothing here is proof-broker
specific.

This is the "axiom-guard script" of verinf's
`analysis/claim-uniqueness-verification.md` §12.4.

## 1. What it checks

For every theorem named in the allowlist:

* the footprint parsed from the build log is a **subset** of the
  allowed list — a smaller footprint passes (the proof got tighter),
  a larger one fails;
* the footprint contains nothing in `HARD_DENY` — currently
  `sorryAx`, `sorry`, `lcProof`, `Lean.ofReduceBool`,
  `Lean.ofReduceNat`, `Lean.trustCompiler` (one shared set, applied
  to both bridges). This fires **regardless of the allowlist**: you
  cannot allowlist your way past a `sorry` or a `native_decide`;
* the theorem is actually present in the log. A theorem that is in
  the allowlist but absent from the build (renamed, deleted, or its
  module silently not built) is a FAILURE, not a pass. This is the
  check that stops a gate from going vacuous.

What it does **not** check: theorems you did not list. Adding a
theorem to the source does not automatically gate it — see §4.

## 2. Wiring it up

Emit the footprints, capture the log, check it:

```lean
-- Audit.lean
import YourProject.Whatever
#print axioms your_theorem
#print axioms your_other_theorem
```

```bash
# `pipefail` is not optional: without it a failed `lake build` is
# swallowed by `tee` and the gate reads a truncated log.
set -o pipefail
lake build 2>&1 | tee build.log
python3 check_axioms.py --build-output build.log --bridge lean
```

`--bridge lean` reads Lean's `#print axioms` lines; `--bridge rocq`
reads Rocq's paired `Print` / `Print Assumptions` blocks; `--bridge
both` does both. Only Python 3 and the two files are needed.

## 3. Allowlist format

```json
{
  "_comment": "free text, ignored",
  "lean": {
    "Your.Namespace.your_theorem": ["propext", "Classical.choice", "Quot.sound"],
    "Your.Namespace.axiom_free_one": []
  },
  "rocq": {}
}
```

Lean keys are fully qualified. Rocq keys are unqualified, because
Rocq's `Print Assumptions` does not print the qualifier. `[]` means
axiom-free and is worth using wherever it holds — it is the
tightest possible pin.

Point the script at your own file with `--allowlist path/to/it.json`.

## 4. Using it honestly

The gate is only as good as the allowlist, so:

* **Pin the measured footprint, not the ceiling.** If a theorem comes
  out `[propext, Quot.sound]`, write that, not the three-axiom
  classical set. A later proof that starts using `Classical.choice`
  is then a visible, reviewable change rather than a silent one.
* **Every new theorem needs an entry**, or it is ungated. There is no
  "everything must be listed" mode; a missing entry is invisible.
  Adding entries is a deliberate act — that is the point, but it
  means a review step, not a habit.
* **Widening an entry is a decision to explain.** The allowlist diff
  is the record of it.
* A `#print axioms` line only reports what that theorem's proof term
  reaches. It says nothing about whether the statement is the one you
  meant.

## 5. Failure output

```
FAIL: axiom-check found 2 regression(s):
  * trust-footprint regression on 'Your.Namespace.thm':
    actual axioms = ['Classical.choice', 'propext']; allowed = ['propext'];
    new (must justify or revise allowlist) = ['Classical.choice']
  * missing: 'Your.Namespace.gone' is in the allowlist but no #print
    axioms output found for it (theorem renamed or deleted without
    updating the allowlist?)
```

Exit status is non-zero on any failure, so it drops straight into CI.
