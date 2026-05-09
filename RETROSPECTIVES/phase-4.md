# Phase 4 retrospective (Rocq architectural probe)

Phase 4 closed with a Rocq plugin that direct-links the OCaml SDK,
reifies LIA + LRA goals into the same `Ir.t` Lean produces, dispatches
through the same broker, verifies the same way, and closes via
cert-gated `lia`/`lra` under the same trust discipline Lean uses for
`omega`/`linarith`. The architectural question the language flip to
OCaml rests on — *is the IR genuinely cross-system or accidentally
Lean-shaped?* — is answered: the IR survived a second source language
intact. Phase 4.5 (closer) and 4.6 (LRA reach) extended the surface
without revealing IR-level cracks. This note captures what surprised,
what held, and the durable Rocq-plugin gotchas that bit me twice and
will bite anyone who follows.

## Easier than expected

The IR's symbol vocabulary ported verbatim. Lean's typeclass-flavored
shell (`HAdd.hAdd`, `LE.le`, `Neg.neg`, …) maps onto Rocq's `Z.add`/
`Z.le`/`Z.opp` (and the matching `Rplus`/`Rle`/`Ropp`) with no
schema change — the broker's Farkas linearizer already accepted both
spellings, and matching Lean's emission rather than emitting `Z.add`
directly turned out to cost nothing. That's the load-bearing data
point of the whole probe: the IR isn't accidentally Lean-shaped.

The `.mlg` / `TACTIC EXTEND` machinery was less arcane than feared.
Once I found `dev/doc/parsing.md`, the bracket-list grammar
(`ne_ident_list_sep(names, ",")`) was a one-line suffix and the
existing `wit_ident` from `Stdarg` supplied the genarg witness. The
only caveat is that Rocq tactic identifiers can't end in `?`, so
`proof_broker?` becomes `proof_broker_verbose` — the only
intentionally asymmetric piece of the surface.

Trust-footprint symmetry held cleanly. LIA closes "Closed under the
global context" — strictly cleaner than Lean's `[propext, Quot.sound]`
because Rocq's `lia` is constructively axiom-free where Lean's
`omega` carries propositional extensionality + `Quot.sound`. LRA
inherits Stdlib's `Reals` axioms (`ClassicalDedekindReals.sig_forall_dec`,
`FunctionalExtensionality.functional_extensionality_dep`), the same
shape of dependency Lean's `linarith` picks up from Mathlib's reals
(`[propext, Classical.choice, Quot.sound]`). Cert-gating introduces
no extra axiom on either side.

## Harder than expected

Two `whd_all` traps, with the same root cause showing up twice.
The first (Phase 3) was `Z.ge x y` unfolding through the head reducer
into `(x ?= y) = Lt -> False` — by the time the reifier saw it, the
`Z.ge` head had vanished and the head-match in `reify_app` couldn't
fire. The second (Phase 4.6) was `IZR z` unfolding into a `match z
with | Z0 => 0%R | Zpos p => IPR p | …`, similarly destroying the
`IZR` head the literal walker depended on. Each cost me a build
iteration to diagnose. The lesson generalizes: a reflexive
`let t = Reductionops.whd_all env sigma t in` at the top of a
recognizer is bug-bait. Standard scope notations elaborate to
constructor applications directly; reduction is only earned, not
default.

Lib-ref resolution against optional libraries (`reals.R.*`) failed at
`Lazy.force` time when the user hadn't `Require Import`-ed the
backing library. Even on a LIA-only goal, the head-match chain in
`reify_app` touches every R ref's lazy as it walks down the
`else if` cascade — there's no short-circuit on "this branch isn't
relevant for this goal type", because branches are checked
sequentially. The fix is a `safe_constr_of_ref` returning `option`
so missing refs degrade to "no match" instead of crashing the
plugin. I rolled this on first encounter rather than baking it in
from the start, which cost one extra iteration.

The `Global.env`-during-syntactic-interpretation rule is a Rocq
plugin invariant, not a bug. Plugin module-init code (top-level
`let bindings`) is evaluated before the proof-state environment
exists, and Rocq actively rejects calls that try to access it
prematurely — `"Anomaly: The global environment cannot be accessed
during the syntactic interpretation phase"`. The `invoke_lia` /
`invoke_lra` helpers had to be wrapped in `Proofview.Goal.enter`
not for goal access but to defer the `Procq.parse_string` /
`intern_pure_tactic` evaluation to tactic-run time. Worth knowing
upfront for any future plugin: anything touching the env goes
inside `Goal.enter`.

Dune's `(using rocq …)` extension is announced and warned-toward
in dune 3.22, but not actually implemented — `(using rocq 0.1)`
errors out. The `(using coq 0.8)` form is deprecated but live, with
a noisy `deprecated_coq_lang` warning that needed silencing. I
parked on the deprecated form with a comment in `dune-project`
explaining why; the future move to `rocq` is a one-line flip when
dune ships it.

CWD-depth assumed by the manifest-loading fallback differed from
Lean. Lean's `<cwd>/../examples` works because `lake build` runs
from `lean-bridge/`, one level under the repo root. Dune-driven
`rocq compile` runs from `_build/default/` (or deeper, depending on
the rule), so any fixed `..` count was wrong. The fix is an upward
walk searching for `examples/manifest-cvc4.json`, which is also
robust against the workspace-merge change in Phase 1.

## Assumptions that held up

The architectural claim from `delta.md §1.1` — direct OCaml linking
from Rocq is cleaner than the C-FFI shim Lean has to use — held in
practice. The Rocq plugin calls `Proof_broker.Codec`, `Manifest`,
`Dispatch`, `Verifier` as ordinary OCaml functions; no JSON envelope,
no `pb_dispatch_call` indirection. That's the qualitative payoff
the language flip was supposed to deliver, and on the Rocq side
it's just *true* — there's no friction layer to manage.

The IR survived the second source language. The probe's premise
was that a Lean-only IR might have absorbed Lean idioms without us
noticing. It didn't: the same `Codec.of_json` that Lean writes against
deserializes Rocq-emitted IRs unchanged, and the broker accepts
them on the first try. No schema patches, no special-cased fields.
That's the rare assumption that costs nothing to validate when it
holds and would have been expensive to discover violated late.

The cert-gating discipline transferred verbatim. The shape "OCaml
verifier accepts → fragment-keyed closer fires → trust footprint =
closer's intrinsic axioms" works the same on both sides. The
implementations differ (Lean's `omega` / `linarith` vs Rocq's `lia` /
`lra`), the axiom signatures differ slightly, but the architectural
contract is identical.

## What I'd do differently

`safe_constr_of_ref` from the start, not the third iteration.
The pattern of treating lib_refs as fallible lookups is obvious in
hindsight — the `_R` family was always going to be conditionally
present. Designing for it upfront would have saved one rebuild and
left the LIA-only-when-Reals-isn't-imported case obviously safe
rather than retroactively.

No top-level `whd_all` in the reifier. The reifier should match raw
Constr shapes by default and only reduce in the narrow places where
a recognizer specifically needs it (probably never, in this
fragment). The two debugging cycles spent finding `Z.ge` and `IZR`
unfolding under reflexive reduction would have been zero. The
generalizable form: in plugin code, reduction is opt-in per
recognizer, not a top-of-function default.

## Carried forward

Term-mode reconstruction is the next direction the user signaled.
The tactic currently routes verified certs to `lia` / `lra`; the
principled finish is to translate the cert's Farkas witness or
Alethe trace into a literal Rocq proof term. That eliminates the
decision-procedure dependency entirely — the cert *is* the proof,
not just a certificate that one exists. Same play for Lean.

Other open carries:

- BV / UF reach: the SDK adapters' capability matchers already
  declare the fragments. The Rocq reifier doesn't have to grow
  symmetrically — a future bridge to a non-arithmetic theory
  surfaces the next batch of cross-system stress.
- A `coq.theory` → `rocq.theory` flip when dune's new build language
  ships. One-line change, no new lessons.
- The `#print axioms` / `Print Assumptions` discipline is the lever
  that keeps the trust footprint honest as future closers grow. A
  CI rule that fails the build if any `_axiom_free` theorem starts
  carrying a non-allowlisted axiom would harden this; not yet in
  place on either bridge.
