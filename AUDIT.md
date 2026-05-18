# Proof-Broker — Comprehensive Repository Audit

**Date:** 2026-05-17
**Branch / HEAD:** `main` @ `8d1241a` (clean working tree)
**Scope:** full repository — SDK (OCaml), Lean bridge, Rocq bridge, Python
tooling, schemas, registry, CI, documentation. ~30.7 kLOC.
**Method:** from-scratch toolchain build on a fresh Gentoo host + dynamic
build/test of every CI surface + six parallel deep static-review passes.
The highest-severity findings were re-verified by hand against source
(noted inline as *verified*).

---

## 1. Status summary

The project is in genuinely good shape. 4 of 5 CI surfaces pass
end-to-end from a clean environment; the shipped trust footprint is
exactly the documented 5 core axioms with **no `sorryAx`/`sorry`/admit**.
The findings below concern *robustness of the soundness guarantee* and
*latent risk*, not evidence of current unsoundness.

| CI surface | Result | Evidence |
|---|---|---|
| **schemas** — `validate.py`, `check.py`, `test_check.py` | ✅ PASS | all artifacts valid; cross-doc OK; 28/28 negative tests |
| **sdk** — `dune build sdk`, `dune runtest sdk`, FFI smoke, cross-tool | ✅ PASS | 21 test suites green; 5/5 FFI smoke incl. 100k round-trips; 3/3 cross-tool agree |
| **lean-bridge** — `lake build`, axiom gate, `roundtripTest` | ✅ PASS | 16692 jobs OK; **0 `sorryAx`**; axiom gate exit 0; real cvc4/z3/cvc5 dispatch + independent Farkas re-verification green |
| **rocq-bridge** | ⚠️ NOT BUILT | environmental opam/`rocq-core` blocker (§2); **source statically audited clean** (§6) |
| **sdk-cross-platform** (macOS/ARM matrix) | N/A | no macOS/ARM runner on audit host; Linux-x86 covered by `sdk` |

Current Lean trust footprint observed in the live build: every
`*_axiom_free` theorem depends only on `[propext, Classical.choice,
Quot.sound]`; allowlist gate exits 0; zero `sorryAx`/`sorry` in build log.

### Issue tracker & pass status

All findings are filed as GitHub issues; umbrella **#19**. Severity →
issue map: C1 #1 · C2 #2 · C3 #3 · H1 #4 · H2 #5 · H3 #6 · H4 #7 ·
H5 #8 · M1 #9 · M2 #10 · M3 #11 · M4 #12 · M5 #13 · M6 #14 · M7 #15 ·
M8 #16 · ROCQ-ENV #17 · LOW-batch #18.

**Pass 1 (done):** C1, C2, C3 fixed — `validate.yml` `pipefail`;
`check_axioms.py` parsers hardened (anchored Lean matchers,
conflict/empty-block poisoning, `HARD_DENY`); new
`tools/test_check_axioms.py` (11 cases) wired into the `schemas` CI
job; verified no regression against the real 61-theorem Lean build
log (gate EXIT 0, 0 poisoned). Remaining findings open for subsequent
passes.

---

## 2. Environment / toolchain notes

Installed to reproduce CI locally: `dev-lang/ocaml-5.4.0`,
`dev-ml/opam-2.5.1`, `sci-mathematics/z3-4.16.0`,
`sci-mathematics/cvc4-1.8` (Portage); opam switch `proof-broker` on
system OCaml 5.4 with `dune/yojson/zarith/digestif/alcotest`; `cvc5
1.3.0` static; `elan 4.2.1` + Lean `v4.30.0-rc2` + Mathlib cache;
Python venv (`jsonschema 4.26`, `referencing 0.37`).

Two snags, **both environmental — not repo defects**:

1. `alcotest` required `CHECK_IF_PREINSTALLED=false` because Gentoo's
   system OCaml ships `ocamlbuild`.
2. **`rocq-core 9.1.1` will not build under an opam `ocaml-system`
   switch.** `make dunestrap COQ_SPLIT=1` fails with `Uncaught
   exception Invalid_argument("failed to locate Coq kernel package in
   split build mode: rocq-runtime.kernel")`, reproducibly, independent
   of dune version (tried 3.23.0 and pinned 3.21.1) and install
   ordering. CI avoids this only because `ocaml/setup-ocaml` uses
   opam's *own* compiler. A dedicated opam-compiler switch would
   resolve it; the Rocq bridge was statically audited instead.

---

## 3. Findings — CRITICAL / HIGH

### C1 — Lean trust gate is defeatable: piped `lake build` swallows the exit code
**✅ FIXED pass 1 (#1).** *Verified.* `.github/workflows/validate.yml:260`
`run: lake build 2>&1 | tee ../lake_build.log`. GitHub Actions runs
`run:` as `bash -e` **without `pipefail`** (confirmed: no `pipefail`
anywhere in the workflow). Pipeline status is `tee`'s (always 0), so a
failing `lake build` — including the "solver missing → Lean inserts
`sorry`" mode the job exists to catch — does not fail the job. The
Rocq job (`:325`) already uses the correct `… || (cat; exit 1)`
pattern.
**Fix:** `set -o pipefail` + explicit RC assertion (one line). Highest
leverage in the report.

### C2 — `check_axioms.py` Lean parser: unconditional overwrite + non-anchored regex
**✅ FIXED pass 1 (#2).** *Verified verbatim.* `tools/check_axioms.py:65-78`. `parse_lean_axioms`
runs the "depends on axioms" loop, then a second loop
`for m in RE_AXIOMS_NONE.finditer(text): out[name] = set()` that
**unconditionally overwrites**. `RE_AXIOMS_NONE` (`:60`) is not
line-anchored and `finditer` scans the whole log, so any occurrence of
`'<name>' does not depend on any axioms` anywhere (a source echo in a
diagnostic, a docstring) resets that theorem to axiom-free — masking a
real `sorryAx`.
**Fix:** single line-anchored pass; conflicting signals for one name =
hard fail.

### C3 — `check_axioms.py` Rocq parser likely blind to Coq 9.x `Print Assumptions` format
**✅ FIXED pass 1 (#3)** — live-Rocq confirmation pending #17.
*Verified regex; live format unconfirmed (Rocq build blocked).*
`tools/check_axioms.py:95` `RE_ROCQ_AXIOM_NAME = r"^([A-Za-z_][\w'.]*)
:\s*$"` requires the axiom *type* to be absent (line ends right after
`name :`). Modern Coq/Rocq prints `Name : <type>` on one line; such
lines fall to the `else` branch and the theorem is flushed as
**axiom-free**, potentially nullifying the entire 79-entry Rocq
allowlist. The parser has **zero unit tests** (`test_check.py` covers
only `check.py`); given C2 is confirmed, the gate code needs a
fixture-based test suite regardless.
**Fix:** handle same-line `name : type`; add Rocq parser fixtures.

### H1 — Inconsistent fallback axiom in the Lean tactic
*Verified.* `lean-bridge/ProofBroker/Tactic.lean:56`
`axiom proofBrokerCertSound : ∀ (P : Prop), P` — proves `False`. It is
the unconditional `catch _ =>` fallback for BV/UF/LRA-without-extension/
other (`:694,725,735,737`). Authors are aware (comments `:17-52`); it
is gated by the allowlist and the **live gate confirms no shipped
theorem reaches it**. But kernel soundness for non-LIA/LRA-term
fragments rests entirely on the (per-C1/C2 porous) CI gate, not on
Lean's kernel.
**Fix:** replace the fallthrough with `throwError` so an unclosable
goal is a tactic error, never an admitted theorem.

### H2 — Tier-2 case-split verifier under-validates the disjunction (SDK)
*Verified.* `sdk/lib/verifier.ml:325-424` +
`sdk/lib/alethe_farkas.ml:395-398`. `disjuncts_of` returns `[s]` for
any non-`Or` term, and case↔disjunct matching is by *positive-scaled*
equality, not equality. A certificate whose
`structural_hint.disjunctive_hypothesis` names a non-disjunctive
hypothesis can satisfy the "partition" check with a single
trivially-closing lemma and yield `Verified_case_split` without the
disjunction ever being shown valid. Highest-severity *soundness*
finding in the SDK. (The Tier-1 Farkas arithmetic core was audited and
found correct: signs, +1 trick, rational sum, strict/loose
contradiction all sound.)
**Fix:** require the named hypothesis to be syntactically `Or`-rooted;
require exact case↔disjunct equality.

### H3 — Adapter subprocess spawn uses the shell; comment claims the opposite
*Verified.* `sdk/lib/adapter_{z3,cvc4,cvc5}.ml` (`:60/:71/:62`) call
`Unix.open_process_full cmd …` where `cmd` is a concatenated **string**
→ runs via `/bin/sh -c`. `adapter_cvc4.ml:17-18` explicitly and
falsely states *"fixed argv (no shell parsing)"*. Today every argv
element is a constant or integer, so **not currently injectable** —
severity is "latent, one refactor from RCE" + "dangerously wrong
comment". Binaries are unqualified (PATH-trust).
**Fix:** `Unix.open_process_args_full` (true `execvp`); absolute paths
or documented PATH trust; correct the comment.

### H4 — Untrusted-input robustness in the Alethe/SMT parsers (SDK)
*Verified by inspection.* `sdk/lib/alethe.ml:88-105` (recursive S-expr
parse, no depth bound), `sdk/lib/z3_proof.ml:58-101`,
`sdk/lib/linear_arith.ml:136` (`Z.pow 10 frac_len`, `frac_len` taken
verbatim from solver output, no length cap),
`sdk/lib/adapter.ml:110-135` (buffers entire solver stdout unbounded).
A malicious/buggy solver build, or a goal crafted to make a solver
emit a deeply-nested or huge-literal proof, can stack-overflow or OOM
the SDK — and through the FFI, the host Lean process. FFI handlers
catch only `Decode_error`/`Json_error`; anything else (`Stack_overflow`,
`failwith`, `assert false`) escapes to an opaque shim `-3`.
**Fix:** depth/length/size bounds; catch-all internal-error envelope in
every FFI handler.

### H5 — Cross-platform / signing jobs unenforced; PR secret-exposure shape
*Verified.* `validate.yml:85-188`. `fail-fast:false` + no `needs:`
out-edge ⇒ macOS-aarch64 / linux-aarch64 / `dune install` / code-sign
breakage **never blocks merge**. Signing secrets injected via `env:`
into `macos-sign.sh` on `pull_request` (`:6`): withheld for fork PRs
(silent coverage loss) and exposed to PR-controlled code on same-repo
PRs (classic exfiltration shape).
**Fix:** gate signing to non-fork or move out of the PR matrix; add an
aggregating required job.

---

## 4. Findings — MEDIUM

- **No cross-document hash linkage check** (`tools/check.py`): cert ↔
  trace ↔ IR hash equality — the core "same proof" invariant the
  schemas explicitly promise — is never verified; fixture placeholder
  hashes don't even match across files.
- **Schema under-constraint**: `schemas/v1.0/ir.schema.json:311`
  `TypeConstructor` and `schemas/v1.0/refinement-record.schema.json:39`
  `Specialization` lack `additionalProperties:false` (every other
  object closes itself) — the soundness-relevant quotient/inductive +
  lifting-inversion metadata. `Payload_Tier4`
  (`certificate.schema.json:297-301`) is `additionalProperties:true`
  with no required fields though Tier 4 is "reserved/unimplemented".
- **Open string enums** for `features_used`/`first_order_fragment`
  (`ir.schema.json:83-95`): `validate.py` alone passes a bogus
  fragment; only the separate `check.py` step (registry) catches it —
  schema and registry are not co-enforced; vocab is triplicated across
  two schemas + registry with no single source of truth.
- **Spec §12 ↔ fixtures drift**: spec mandates a Tier-3 Alethe
  certificate for Example 1; only `cert-example1-tier1-farkas.json`
  (tier 1, *verified*) ships. No Tier-2/Tier-3 example cert exists;
  the Alethe/trace path is never validated against a real artifact.
- **FFI thread-safety / init**: `sdk/ffi/proof_broker_shim.c:41-54`
  and `lean-bridge/c/glue.c:31-39` — `g_initialized`/`g_inited`
  non-atomic; `pb_ffi_init` rc ignored. Degrades fail-safe (yields a
  `shimFailure` envelope → tactic throws) so no soundness impact;
  robustness only.
- **`rat_of_string` accepts Zarith-extended literals** (`0x`, `0b`,
  underscores) `sdk/lib/linear_arith.ml:98-141` — not a soundness
  break (sum re-checked) but breaks coefficient
  reproducibility/auditing.
- **`check.py` advertises more than it enforces**: explicit-axiom
  shells, non-type-variable theory tags, abstract-signature subterms,
  Tier-0/2 payload registry checks are skipped vs the docstring.
- **Stale docstring**: `tools/check_axioms.py:35-38` claims the Rocq
  CI gate "doesn't exist yet" when `validate.yml:327` runs it — risks
  treating a load-bearing gate as non-load-bearing.
- **Supply chain**: floating action tags (`@v4`, `@v3`); `curl | sh`
  for elan; **unauthenticated cvc5 download** `sudo install`ed to
  `/usr/local/bin` with no checksum — the solver that establishes the
  trust footprint is fetched unverified. cvc5 version skew
  (CI 1.3.0 / manifest 1.3.3 / cert 1.2.0) asserted safe only in a
  comment; nothing in `tools/` checks version compatibility.

---

## 5. Findings — LOW / quality

- Duplicated trust-critical scale-factor logic
  (`sdk/lib/verifier.ml:273-304` vs `alethe_farkas.ml`).
- `assert false` as "unreachable" on attacker-influenced lists
  (`verifier.ml:363,384`).
- O(n²) `@`-append accumulators (`dispatch.ml:115`, `smtlib.ml:186`,
  `propositional_simplify.ml:145`).
- Hard-coded all-zero `config_hash`/`rewrite_trace_hash` in every
  adapter — defeats provenance correlation and cert identity.
- **`FFI_CONVENTIONS.md` describes a `Codec.to_wire`/`Codec.of_wire`
  CBOR toggle that does not exist** — code is JSON-only, no codec
  abstraction seam; the Phase-0 retrospective repeats the false claim.
  Most material doc/reality gap.
- Reifier nits: `rocq-bridge/src/reifier.ml:217` uses `Global.env ()`
  instead of the passed `env` in one error path; stale "arity-2"
  comments vs arity-N code (`term_mode.ml:982`).
- delta.md staleness (self-disclosed): §2.5.1 "6 Lean + 11 Rocq" axiom
  counts (Phase-4 snapshot; now 61/79); §2.1 macOS-x86 platform list
  (macos-13 dropped per commit `39ffd0f`).
- **Correction to an agent finding:** a committed
  `tools/__pycache__/*.pyc` was flagged but is **not tracked by git**
  (`git ls-files` confirms) — that finding is **invalid**.

---

## 6. Rocq bridge — static audit (clean)

No build was possible (§2), but deep source review found **no path
that closes a Rocq goal without a kernel-checked proof**. Term-mode
uses `Refine.refine ~typecheck:true` + `ring` + `Qed`, keeping the
SDK's witness arithmetic *out of the trust base* (SDK selects, kernel
verifies; a wrong witness ⇒ `ring` fails ⇒ goal stays open — fails
closed). No `admit`/`Admitted`/`Axiom`/`Parameter` in any `.v` file;
the `whd_all`/folded-definition traps from `RETROSPECTIVES/phase-4.md`
are correctly avoided; the allowlist is a tight, correct ceiling
(Z-side `[]`, R-side exactly the standard Stdlib `Reals` pair). Minor
issues folded into §5.

---

## 7. Documentation accuracy

Independently verified and **substantially accurate**: the
phase-status claims hold; the term-mode Tier-1+Tier-2 vocabulary
claims (all comparison goals, four hypothesis shapes + negations,
signed-coefficient equalities, rationals, arity-N premises and
disjunctions) each map to real `*_axiom_free` tests on both bridges;
the allowlist has **exactly 140 entries / 5 distinct core axioms** as
the README states; README "Layout" matches the tree; retrospective
fixes are present in code. Genuinely contradicted: the CBOR-toggle
claim (§5). Stale-but-self-disclosed: the delta.md items in §5.

---

## 8. Recommended fix priority

1. ~~`validate.yml:260` — `set -o pipefail` + RC check (**C1**)~~ ✅ done pass 1 (#1).
2. ~~Rewrite `check_axioms.py` parsers + fixture-based test suite
   (**C2/C3**)~~ ✅ done pass 1 (#2, #3) — `tools/test_check_axioms.py`,
   wired into CI. Rocq live confirmation tracked by #17.
3. Tier-2 case-split hardening in `verifier.ml` (**H2**) — the only
   confirmed SDK soundness gap.
4. Replace `proofBrokerCertSound` fallthrough with `throwError`
   (**H1**).
5. `Unix.open_process_args_full` + bounds/guards in the Alethe parsers
   + FFI catch-all envelope (**H3/H4**).
6. CI hygiene: enforce or stop implying cross-platform/signing
   coverage; SHA-pin actions; checksum the cvc5 download (**H5**); add
   cross-doc hash-linkage to `check.py`; close the two schemas
   (**MED**).

---

## 9. Appendix — commands used to reproduce status

```
# OCaml SDK
opam exec --switch=proof-broker -- dune build sdk
opam exec --switch=proof-broker -- dune runtest sdk
opam exec --switch=proof-broker -- bash sdk/ffi/test/run.sh

# Python tooling (venv)
~/.venvs/proof-broker-tools/bin/python tools/validate.py
~/.venvs/proof-broker-tools/bin/python tools/check.py
~/.venvs/proof-broker-tools/bin/python tools/test_check.py
~/.venvs/proof-broker-tools/bin/python tools/test_cross_tool.py

# Lean bridge
cd lean-bridge && lake update && lake exe cache get && lake build
~/.venvs/proof-broker-tools/bin/python tools/check_axioms.py \
  --build-output /tmp/lake_build.log --bridge lean
cd lean-bridge && lake exe roundtripTest

# Rocq bridge — blocked: rocq-core 9.1.1 COQ_SPLIT build fails on
# an opam ocaml-system switch (environmental; needs a dedicated
# opam-compiler switch).
```
