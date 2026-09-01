#!/usr/bin/env python3
"""Cross-document soundness checks for every fixture in examples/.

The JSON Schemas validate structure. This pass validates invariants that
span multiple documents or require domain knowledge:

  IR documents
    - Every TypeRef resolves to type_metadata, type_vars, or a known shell
      primitive (Int, Nat, Bool, String, Prop, Type, Real, Rat, Bitvec(n),
      or a function arrow type).
    - Every unbound Var(name) is declared in context.free_vars.
    - Every unbound App.symbol / Const.name resolves to definitional_metadata,
      library_provenance, or context.free_vars.
    - Every Opaque.payload_id is present in goal.payloads.
    - logic_classification.features_used and .first_order_fragment are
      registered (features list / first-order-fragment ids).
    - definitional_metadata[*].concept_tag is a registered concept tag.
    - type_metadata type_variable instances' theory_classification_tags
      and primitive entries' theory_tags are registered theory tags —
      or (R3-M1) `embedding_witness:<name>` tags whose <name> resolves
      in library_provenance.
    - definitional_metadata specialization_targets' soundness_witness
      entries resolve in library_provenance (R3-M1).
    - abstract_axioms given in the *string* "shape:detail" form have a
      registered shape id. (The explicit-object form
      {"shape": "explicit", ...} is NOT registry-checked — see below.)
    - Every entity referenced by name (class names, equivalence_proofs,
      elimination/equality principles, lifting witnesses, underlying
      function names) has a library_provenance entry. (Warning, not error.)
    - Every declared free_var is referenced. (Warning, not error.)

  Certificates
    - refinement_record.fragment is a registered fragment.
    - Tier 1 witness_kind / Tier 3 trace_format are in the registry.
    - Strict-identity hash linkage (check_cert_hashes, run here and
      from validate.py): dispatch_context_hash == canonical SHA-256 of
      the paired IR and backend.config_hash == canonical SHA-256 of the
      paired manifest (tools/canonical_hash.py reproduces the OCaml
      codec canonicalization).
    - backend.version vs the paired manifest's adapter_version: a
      mismatch is a WARNING (printed with a `WARNING:` prefix), not an
      error — the config_hash is the binding identity, the version
      string is only the adapter's declared label (never cross-checked
      before, so shipped fixtures can carry a stale one).
    - refinement_record.specializations[].soundness_witness tokens
      (comma-split) resolve to library_provenance entries of the
      paired IR (R3-M1).

  Adapter manifests
    - logic_fragments, type_constructions, witness_kinds_produced,
      trace_formats_produced are registered.

  Rewrite traces
    - Each entry's pass name is in registry.rewriter_passes. (Warning.)
    - Hash-chain continuity: initial -> per-entry before/after chain ->
      final, and a failed/no_op pass leaves the IR unchanged.

  Fixture pairing completeness (C2 round 1)
    - Every cert-*.json in examples/ must key into all three cert
      pairing maps (CERT_MANIFEST_PAIRS, CERT_IR_PAIRS,
      CERT_TRACE_PAIRS), and every rewrite-trace-*-identity.json into
      TRACE_IR_PAIRS. The hash/sentinel gates above are driven by
      those maps, so an unpaired fixture would silently skip them; an
      unpaired fixture is an ERROR in both drivers. A non-identity
      trace (rewrite-trace-example3.json) has no IR pairing by design
      — only chain continuity applies to it.

NOT enforced (known, scoped gaps — documented so this docstring does
not overclaim; audit M7. Closing these is behaviour-affecting and is
tracked separately, not silently asserted here):
  - Explicit-object abstract_axioms ({"shape": "explicit", ...}): the
    shape id and any embedded shell term are not validated.
  - collect_subshells does not descend into instances[].abstract_signature,
    explicit abstract_axiom shells, or lifting_obligation subterms, so an
    unresolved TypeRef/symbol hiding only there is not caught.
  - Tier-0 and Tier-2 payload contents (e.g. Tier-2 library-lemma
    content_hash) get no registry/hash cross-check; only the
    refinement_record.fragment is validated for those tiers.
  - backend.version != adapter_version never fails the run (see above);
    neither label is checked against the installed binary.

Errors fail the run; warnings are surfaced but do not.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXAMPLES = ROOT / "examples"
REGISTRY_FILE = ROOT / "registry" / "patterns-v1.json"

SHELL_PRIMITIVE_TYPES = {"Int", "Nat", "Bool", "String", "Prop", "Type", "Real", "Rat"}


def is_known_type_primitive(typeref: str) -> bool:
    if typeref in SHELL_PRIMITIVE_TYPES:
        return True
    if typeref.startswith("Bitvec("):
        return True
    if "->" in typeref:
        return True
    return False


def shell_iter(term, bound=frozenset()):
    """Yield (subterm, bound) pairs in document order, with bound names in scope."""
    yield term, bound
    node = term["node"]
    if node in ("Forall", "Exists"):
        yield from shell_iter(term["body"], bound | {term["var"]})
    elif node == "Lambda":
        yield from shell_iter(term["body"], bound | {b["var"] for b in term["binders"]})
    elif node == "Implies":
        yield from shell_iter(term["antecedent"], bound)
        yield from shell_iter(term["consequent"], bound)
    elif node in ("And", "Or"):
        yield from shell_iter(term["left"], bound)
        yield from shell_iter(term["right"], bound)
    elif node == "Not":
        yield from shell_iter(term["operand"], bound)
    elif node == "Eq":
        yield from shell_iter(term["left"], bound)
        yield from shell_iter(term["right"], bound)
    elif node == "App":
        for a in term.get("args", []):
            yield from shell_iter(a, bound)


def collect_subshells(ir):
    """Yield the shell terms reachable through the document's primary
    carriers: goal, hypotheses, library_slice, definitional_metadata
    (definitional_equation / extensional_axiom / lifted underlying
    function), and type_constructor_application constructors.

    NOT exhaustive (audit M7): it does not descend into type_variable
    instances' abstract_signature, explicit abstract_axiom shells, or
    lifting_obligation subterms, so a TypeRef/symbol that appears ONLY
    in one of those is not surfaced by check_ir. This is the
    scoped-gap behaviour documented in the module docstring, stated
    here too so the boundary is visible at the call site."""
    yield ir["goal"]["shell"]
    for h in ir["context"].get("hypotheses", []):
        yield h["shell"]
    for entry in ir["context"].get("library_slice", []):
        yield entry["shell"]
    for sym, dm in ir.get("definitional_metadata", {}).items():
        for k in ("definitional_equation", "extensional_axiom"):
            if k in dm:
                yield dm[k]
        if dm.get("kind") == "lifted_to_quotient":
            uf = dm.get("underlying_function", {})
            if "shell" in uf:
                yield uf["shell"]
    for tid, tm in ir.get("type_metadata", {}).items():
        if tm.get("kind") == "type_constructor_application":
            ctor = tm.get("constructor", {})
            er = ctor.get("equivalence_relation", {})
            if "shell" in er:
                yield er["shell"]
            if "predicate" in ctor:
                yield ctor["predicate"]
            for arg in tm.get("arguments", []):
                yield arg


def check_ir(ir):
    errors, warnings = [], []
    type_metadata = ir.get("type_metadata", {})
    defn_metadata = ir.get("definitional_metadata", {})
    provenance = ir.get("library_provenance", {})
    type_vars = set(ir["context"].get("type_vars", []))
    free_vars = {fv["name"]: fv["type"] for fv in ir["context"].get("free_vars", [])}

    valid_type_refs = SHELL_PRIMITIVE_TYPES | set(type_metadata.keys()) | type_vars
    valid_symbols = set(defn_metadata.keys()) | set(provenance.keys()) | set(free_vars.keys())

    seen_type_refs: set[str] = set()
    seen_free_vars: set[str] = set()
    seen_unbound_symbols: set[str] = set()
    payload_refs: set[str] = set()

    for top in collect_subshells(ir):
        for term, bound in shell_iter(top):
            node = term["node"]
            if node in ("Forall", "Exists"):
                seen_type_refs.add(term["type"])
            elif node == "Lambda":
                for b in term["binders"]:
                    seen_type_refs.add(b["type"])
            elif node == "Eq":
                seen_type_refs.add(term["type"])
            elif node == "NumLit":
                seen_type_refs.add(term["type"])
            elif node == "App":
                for ta in term.get("type_args", []):
                    seen_type_refs.add(ta)
                if term["symbol"] not in bound:
                    seen_unbound_symbols.add(term["symbol"])
            elif node == "Var":
                if term["name"] not in bound:
                    seen_free_vars.add(term["name"])
            elif node == "Const":
                seen_unbound_symbols.add(term["name"])
            elif node == "Opaque":
                payload_refs.add(term["payload_id"])

    for fv in ir["context"].get("free_vars", []):
        seen_type_refs.add(fv["type"])
    for tid, tm in type_metadata.items():
        if tm.get("kind") == "type_constructor_application":
            ctor = tm.get("constructor", {})
            for k in ("underlying_type", "base_type"):
                if k in ctor:
                    seen_type_refs.add(ctor[k])
    for sym, dm in defn_metadata.items():
        if dm.get("kind") in ("lifted_to_quotient", "constructor", "eliminator"):
            ht = dm.get("host_type")
            if ht:
                seen_type_refs.add(ht)

    for tr in sorted(seen_type_refs):
        if tr in valid_type_refs or is_known_type_primitive(tr):
            continue
        errors.append(f"unresolved TypeRef '{tr}'")

    for v in sorted(seen_free_vars):
        if v not in free_vars:
            errors.append(f"unbound Var '{v}' not declared in context.free_vars")

    for v in sorted(free_vars):
        if v not in seen_free_vars and v not in seen_unbound_symbols:
            warnings.append(f"context.free_vars['{v}'] declared but never referenced")

    for s in sorted(seen_unbound_symbols):
        if s in valid_symbols:
            continue
        errors.append(f"unresolved symbol '{s}' (no definitional_metadata, library_provenance, or free_vars entry)")

    payloads = ir["goal"].get("payloads") or {}
    for p in sorted(payload_refs):
        if p not in payloads:
            errors.append(f"Opaque payload '{p}' not in goal.payloads")

    return errors, warnings


def check_ir_against_registry(ir, registry):
    errors, warnings = [], []
    type_metadata = ir.get("type_metadata", {})
    defn_metadata = ir.get("definitional_metadata", {})
    provenance = ir.get("library_provenance", {})

    feature_ids = {f["id"] for f in registry["logical_features"]}
    for f in ir["logic_classification"]["features_used"]:
        if f not in feature_ids:
            errors.append(f"logic_classification.features_used: unknown feature '{f}'")

    fragment_ids = {f["id"] for f in registry["first_order_fragments"]} | {"none"}
    fr = ir["logic_classification"]["first_order_fragment"]
    if fr not in fragment_ids:
        errors.append(f"logic_classification.first_order_fragment: unknown fragment '{fr}'")

    concept_ids = {c["id"] for c in registry["concept_tags"]}
    for sym, dm in defn_metadata.items():
        if "concept_tag" in dm and dm["concept_tag"] not in concept_ids:
            errors.append(f"definitional_metadata['{sym}'].concept_tag: unknown '{dm['concept_tag']}'")

    # Theory tags: registered ids, plus the R3-M1 witness form
    # `embedding_witness:<name>` where <name> must be a
    # library_provenance key (refinement joins these payloads into the
    # specialization record's soundness_witness, so a dangling name
    # here becomes an unverifiable witness there). Covers both
    # type_variable instances' theory_classification_tags and — new in
    # R3-M1, closing a documented gap — primitive entries' theory_tags.
    theory_tag_ids = {t["id"] for t in registry["theory_tags"]}

    def check_tag(tag, where):
        if tag.startswith("embedding_witness:"):
            name = tag.split(":", 1)[1]
            if name not in provenance:
                errors.append(
                    f"{where}: embedding_witness '{name}' has no "
                    "library_provenance entry"
                )
        elif tag not in theory_tag_ids:
            errors.append(f"{where}: unknown '{tag}'")

    for tid, tm in type_metadata.items():
        if tm.get("kind") == "type_variable":
            for inst in tm.get("instances", []):
                for tag in inst.get("theory_classification_tags", []):
                    check_tag(
                        tag,
                        f"type_metadata['{tid}'].instances[].theory_classification_tags",
                    )
        elif tm.get("kind") == "primitive":
            for tag in tm.get("theory_tags", []):
                check_tag(tag, f"type_metadata['{tid}'].theory_tags")

    # R3-M1: a specialization_targets entry's soundness_witness must
    # resolve in library_provenance — same rule as the embedding
    # witness tags (the method_specialization record copies it).
    for sym, dm in defn_metadata.items():
        if dm.get("kind") == "typeclass_method":
            for tgt in dm.get("specialization_targets", []):
                w = tgt.get("soundness_witness")
                if w is not None and w not in provenance:
                    errors.append(
                        f"definitional_metadata['{sym}'].specialization_targets"
                        f"[theory={tgt.get('theory')}]: soundness_witness "
                        f"'{w}' has no library_provenance entry"
                    )

    axiom_shape_ids = {a["id"] for a in registry["axiom_shape_descriptors"]}
    for tid, tm in type_metadata.items():
        if tm.get("kind") == "type_variable":
            for inst in tm.get("instances", []):
                for ax in inst.get("abstract_axioms", []):
                    if isinstance(ax, str):
                        shape_id = ax.split(":", 1)[0]
                        if shape_id not in axiom_shape_ids:
                            errors.append(
                                f"type_metadata['{tid}'].instances[].abstract_axioms: unknown shape '{shape_id}' in '{ax}'"
                            )

    referenced_entities: set[str] = set()
    for tid, tm in type_metadata.items():
        if tm.get("kind") == "type_variable":
            for inst in tm.get("instances", []):
                cls = inst.get("class", {})
                if "name" in cls:
                    referenced_entities.add(cls["name"])
        if tm.get("kind") == "type_constructor_application":
            ctor = tm.get("constructor", {})
            if "name" in ctor:
                referenced_entities.add(ctor["name"])
            for k in ("elimination_principle", "equality_principle"):
                if k in ctor:
                    referenced_entities.add(ctor[k])
            er = ctor.get("equivalence_relation", {})
            if "equivalence_proof" in er:
                referenced_entities.add(er["equivalence_proof"])
    for sym, dm in defn_metadata.items():
        if dm.get("kind") == "lifted_to_quotient":
            uf = dm.get("underlying_function", {})
            if "name" in uf:
                referenced_entities.add(uf["name"])
            lo = dm.get("lifting_obligation", {})
            if "witness" in lo:
                referenced_entities.add(lo["witness"])

    for ent in sorted(referenced_entities):
        if ent not in provenance:
            warnings.append(f"referenced entity '{ent}' has no library_provenance entry")

    return errors, warnings


def check_certificate(cert, registry):
    errors, warnings = [], []
    rr = cert.get("refinement_record", {})
    fragment_ids = {f["id"] for f in registry["first_order_fragments"]}
    if rr.get("fragment") and rr["fragment"] not in fragment_ids:
        errors.append(f"refinement_record.fragment: unknown fragment '{rr['fragment']}'")

    tier = cert["tier"]
    payload = cert["payload"]
    if tier == 1:
        wk = payload.get("witness_kind")
        wk_ids = {w["id"] for w in registry["adapter_capability_vocabulary"]["witness_kinds"]}
        if wk and wk not in wk_ids:
            errors.append(f"payload.witness_kind: unknown kind '{wk}'")
    elif tier == 3:
        tf = payload.get("trace_format")
        tf_ids = {t["id"] for t in registry["adapter_capability_vocabulary"]["trace_formats"]}
        if tf and tf not in tf_ids:
            errors.append(f"payload.trace_format: unknown format '{tf}'")

    return errors, warnings


def check_manifest(manifest, registry):
    errors, warnings = [], []
    fragment_ids = {f["id"] for f in registry["first_order_fragments"]}
    for fr in manifest["logic_fragments"]:
        if fr not in fragment_ids:
            errors.append(f"logic_fragments: unknown '{fr}'")

    construction_ids = {c["id"] for c in registry["construction_kinds"]}
    construction_ids |= {"primitive", "type_variable_via_specialization"}
    for tc in manifest["type_constructions"]:
        if tc not in construction_ids:
            errors.append(f"type_constructions: unknown '{tc}'")

    if 1 in manifest["tiers_produced"]:
        wks = {w["id"]: w for w in registry["adapter_capability_vocabulary"]["witness_kinds"]}
        for w in manifest.get("witness_kinds_produced", []):
            if w not in wks:
                errors.append(f"witness_kinds_produced: unknown '{w}'")
            elif not wks[w].get("v1", False):
                # R2: sat_* were demoted to v1:false — nothing mints
                # them; a manifest advertising one overclaims.
                errors.append(
                    f"witness_kinds_produced: '{w}' is v1:false in the "
                    "registry (not produced by any v1 adapter)")
    if 3 in manifest["tiers_produced"]:
        tf_ids = {t["id"] for t in registry["adapter_capability_vocabulary"]["trace_formats"]}
        for tf in manifest.get("trace_formats_produced", []):
            if tf not in tf_ids:
                errors.append(f"trace_formats_produced: unknown '{tf}'")

    return errors, warnings


def check_cert_manifest_consistency(cert, manifest, cert_name=None):
    """R2.4: a cert must be producible by its paired manifest —
    `cert.tier ∈ manifest.tiers_produced`, and a Tier-3 cert's
    `payload.trace_format ∈ manifest.trace_formats_produced` (a
    Tier-1 cert's witness_kind likewise). This is what the old
    config_hash-only pairing could not catch (STATUS §3.3 #7:
    manifest-vampire claimed tiers_produced=[0] while the adapter
    minted Tier 3)."""
    errors = []
    name = cert_name or "certificate"
    tier = cert.get("tier")
    tiers = manifest.get("tiers_produced", [])
    if tier not in tiers:
        errors.append(
            f"{name}: tier {tier} not in paired manifest's "
            f"tiers_produced {tiers}")
    if tier == 3:
        tf = cert.get("payload", {}).get("trace_format")
        produced = manifest.get("trace_formats_produced", [])
        if tf not in produced:
            errors.append(
                f"{name}: payload.trace_format '{tf}' not in paired "
                f"manifest's trace_formats_produced {produced}")
    if tier == 1:
        wk = cert.get("payload", {}).get("witness_kind")
        produced = manifest.get("witness_kinds_produced", [])
        if wk not in produced:
            errors.append(
                f"{name}: payload.witness_kind '{wk}' not in paired "
                f"manifest's witness_kinds_produced {produced}")
    return errors


# --- Repo-level source-scan checks (R2.4) --------------------------------

SDK_LIB = ROOT / "sdk" / "lib"

_QUOTED_ID_RE = re.compile(r'"([a-z0-9][a-z0-9-]*)"')


def check_sdk_trace_format_literals(registry, sdk_lib=None):
    """Every trace_format string literal in sdk/lib must be a
    registered trace format: an unregistered literal is either a
    typo (a dead verifier/minting arm) or a format the registry
    fails to admit exists (the `rocq-tactic-script` gap this check
    was written for)."""
    sdk_lib = Path(sdk_lib) if sdk_lib else SDK_LIB
    tf_ids = {t["id"] for t in registry["adapter_capability_vocabulary"]["trace_formats"]}
    errors = []
    for path in sorted(sdk_lib.glob("*.ml")):
        for lineno, line in enumerate(path.read_text().splitlines(), 1):
            if "trace_format" not in line:
                continue
            for lit in _QUOTED_ID_RE.findall(line):
                if lit not in tf_ids:
                    errors.append(
                        f"{path.relative_to(ROOT) if path.is_relative_to(ROOT) else path}"
                        f":{lineno}: trace_format literal '{lit}' is not "
                        "a registered trace format "
                        "(registry/patterns-v1.json "
                        "adapter_capability_vocabulary.trace_formats)")
    return errors


_PIN_RE = re.compile(
    r'\(\* PIN:always-unfold-for-dispatch \*\)(.*?)'
    r'\(\* ENDPIN:always-unfold-for-dispatch \*\)', re.S)


def check_always_unfold_pin(registry, pipeline_ml=None):
    """The SDK's baked-in dispatch unfold list (sdk/lib/pipeline.ml,
    between the PIN markers) must equal the registry's
    always_unfold_for_dispatch — the two-way pin that lets the SDK
    avoid a runtime file dependency on the registry JSON."""
    path = Path(pipeline_ml) if pipeline_ml else SDK_LIB / "pipeline.ml"
    text = path.read_text()
    m = _PIN_RE.search(text)
    if m is None:
        return [f"{path}: PIN:always-unfold-for-dispatch markers not found"]
    pinned = re.findall(r'"([a-z_]+)"', m.group(1))
    expected = registry.get("always_unfold_for_dispatch", [])
    if pinned != expected:
        return [
            f"{path}: pinned always_unfold_for_dispatch {pinned} != "
            f"registry {expected} — edit both together"]
    return []


# --- Cross-fixture hash linkage (#18d / #24-M1) ---------------------------
#
# The strict-identity hash invariants for example certificates:
#
#   * cert.backend.config_hash == canonical_sha256(paired_manifest)
#   * cert.dispatch_context_hash == canonical_sha256(paired_ir)
#     (when the cert ships with a paired IR fixture)
#
# Schema-stated (rewrite-trace.schema.json's `final_ir_hash matches the
# certificate's dispatch_context_hash`) but unenforced before this. Wired
# into validate.py for cert-* example fixtures; tools/regen_cert_hashes.py
# uses these same pairing maps to (re-)pin the fixture hashes.

# cert filename -> manifest filename. Every cert has a backend, so every
# cert has a manifest pairing.
CERT_MANIFEST_PAIRS = {
    "cert-example1-tier1-farkas.json":    "manifest-cvc5.json",
    "cert-example1-tier3-alethe.json":    "manifest-cvc5.json",
    "cert-example2-tier2-casesplit.json": "manifest-cvc5.json",
    "cert-example4-tier3-tptp.json":      "manifest-vampire.json",
    "cert-example-nat-tier1-farkas.json": "manifest-cvc5.json",
}

# cert filename -> IR filename. R2: every shipped cert pairs with a
# shipped IR fixture — the old "unpaired dispatch IR" sentinel is
# gone (cert-example2 / cert-example4 gained example-casesplit-lra /
# example-tstp-fol as their dispatch IRs).
CERT_IR_PAIRS = {
    "cert-example1-tier1-farkas.json": "example1-lia-typeclass.json",
    "cert-example1-tier3-alethe.json": "example1-lia-typeclass.json",
    "cert-example2-tier2-casesplit.json": "example-casesplit-lra.json",
    "cert-example4-tier3-tptp.json": "example-tstp-fol.json",
    "cert-example-nat-tier1-farkas.json": "example-nat-bound.json",
}

# cert filename -> rewrite-trace filename (R2). Every cert's
# rewrite_trace_hash is the canonical hash of its paired trace
# fixture; the paired traces here are identity traces of the default
# dispatch pipeline (both passes no-op) over the cert's paired IR.
CERT_TRACE_PAIRS = {
    "cert-example1-tier1-farkas.json": "rewrite-trace-example1-identity.json",
    "cert-example1-tier3-alethe.json": "rewrite-trace-example1-identity.json",
    "cert-example2-tier2-casesplit.json": "rewrite-trace-casesplit-identity.json",
    "cert-example4-tier3-tptp.json": "rewrite-trace-tstp-identity.json",
    "cert-example-nat-tier1-farkas.json": "rewrite-trace-nat-identity.json",
}

# rewrite-trace filename -> the IR fixture whose canonical hash every
# hash field of the (identity) trace must carry. A non-identity trace
# fixture (rewrite-trace-example3.json) has no entry — only chain
# continuity applies there.
TRACE_IR_PAIRS = {
    "rewrite-trace-example1-identity.json": "example1-lia-typeclass.json",
    "rewrite-trace-casesplit-identity.json": "example-casesplit-lra.json",
    "rewrite-trace-tstp-identity.json": "example-tstp-fol.json",
    "rewrite-trace-nat-identity.json": "example-nat-bound.json",
}

# The all-zeros "no trace" sentinel is REJECTED as of R2: every mint
# path stamps the real trace hash, and the OCaml verifier
# (Verifier.check_trace_hash_sentinel) refuses envelope verification
# on a sentinel-bearing cert. The name survives only so the checker
# and regen agree on what must never appear.
_ZERO_SENTINEL_HASH = "sha256:" + "0" * 64


def check_fixture_pairing_completeness(fixture_names=None):
    """C2 round 1, finding 1: the R2 hash/sentinel gates are keyed by
    the pairing maps above, so a cert-*.json dropped into examples/
    without entries there used to get vocabulary checks only — no
    sentinel rejection, no hash linkage, no cert-vs-manifest
    consistency — and still print OK. Completeness closes that: every
    cert fixture must key into ALL THREE cert maps
    (CERT_MANIFEST_PAIRS, CERT_IR_PAIRS, CERT_TRACE_PAIRS), and every
    identity-trace fixture (rewrite-trace-*-identity.json) into
    TRACE_IR_PAIRS. An unpaired fixture is an error, not a skip.

    A non-identity trace (rewrite-trace-example3.json) has no IR
    pairing by design — every hash slot of an identity trace equals
    one IR's hash, which is false for a real rewrite — so only chain
    continuity applies there and it is exempt here.

    `fixture_names` defaults to the examples/ listing; tests inject
    synthetic names."""
    if fixture_names is None:
        fixture_names = sorted(p.name for p in EXAMPLES.glob("*.json"))
    cert_maps = [
        ("CERT_MANIFEST_PAIRS", CERT_MANIFEST_PAIRS),
        ("CERT_IR_PAIRS", CERT_IR_PAIRS),
        ("CERT_TRACE_PAIRS", CERT_TRACE_PAIRS),
    ]
    errors = []
    for name in fixture_names:
        if name.startswith("cert-"):
            missing = [label for label, m in cert_maps if name not in m]
            if missing:
                errors.append(
                    f"examples/{name}: cert fixture has no entry in "
                    f"pairing map(s) {', '.join(missing)} "
                    "(tools/check.py) — an unpaired cert skips the "
                    "sentinel/hash-linkage/manifest-consistency gates; "
                    "pair it in all three maps and run "
                    "`python tools/regen_cert_hashes.py`")
        elif (name.startswith("rewrite-trace-")
                and name.endswith("-identity.json")
                and name not in TRACE_IR_PAIRS):
            errors.append(
                f"examples/{name}: identity-trace fixture has no entry "
                "in TRACE_IR_PAIRS (tools/check.py) — an unpaired "
                "identity trace skips the hash-slot check against its "
                "paired IR")
    return errors


def check_cert_hashes(cert, paired_ir=None, paired_manifest=None,
                      cert_name=None, manifest_name=None,
                      paired_trace=None):
    """Verify a certificate's strict-identity hash linkage to its
    paired fixtures.

    Callers (main() below, validate.py) do the pairing-name lookup and
    load the paired IR / manifest dicts. We compute the canonical
    SHA-256 and compare; mismatches are errors with both sides reported
    so the diagnostic is actionable.

    Both `paired_ir` and `paired_manifest` are optional — a cert with
    no paired IR (synthetic in-process dispatch) is checked for
    manifest linkage only. `cert_name` / `manifest_name` are only used
    to make the messages name the files.

    Non-blocking: when the paired manifest's `adapter_version` differs
    from the cert's `backend.version` a WARNING is returned (never an
    error). The config_hash is what binds the cert to the manifest; the
    version string is the adapter's declared label and had never been
    cross-checked, so shipped fixtures may carry stale labels.
    """
    # Local import: canonical_hash is in tools/; check.py is too.
    from canonical_hash import canonical_sha256
    errors, warnings = [], []

    if paired_manifest is not None:
        expected = canonical_sha256(paired_manifest)
        actual = cert.get("backend", {}).get("config_hash")
        if actual != expected:
            errors.append(
                f"backend.config_hash: expected {expected} (canonical hash "
                f"of paired manifest), got {actual}. Run "
                f"`python tools/regen_cert_hashes.py` to re-pin."
            )
        cert_version = cert.get("backend", {}).get("version")
        manifest_version = paired_manifest.get("adapter_version")
        if str(cert_version) != str(manifest_version):
            warnings.append(
                f"{cert_name or 'certificate'}: backend.version "
                f"{cert_version!r} != adapter_version {manifest_version!r} "
                f"in paired manifest {manifest_name or '(unnamed)'} "
                "(config_hash still binds the cert to this manifest; the "
                "version label is declared, not checked against a binary "
                "— relabel one side; non-blocking)"
            )

    if paired_ir is not None:
        expected = canonical_sha256(paired_ir)
        actual = cert.get("dispatch_context_hash")
        if actual != expected:
            errors.append(
                f"dispatch_context_hash: expected {expected} (canonical "
                f"hash of paired IR), got {actual}. Run "
                f"`python tools/regen_cert_hashes.py` to re-pin."
            )

    # R2: the zero-sentinel rewrite_trace_hash is rejected everywhere —
    # the OCaml verifier refuses it, so a fixture carrying it would
    # document a cert that can never verify.
    rth = cert.get("rewrite_trace_hash")
    if rth == _ZERO_SENTINEL_HASH:
        errors.append(
            "rewrite_trace_hash is the all-zeros sentinel; R2 deleted it "
            "from every mint path and the verifier rejects it. Pair the "
            "cert with a trace fixture and run "
            "`python tools/regen_cert_hashes.py`."
        )
    if paired_trace is not None and rth != _ZERO_SENTINEL_HASH:
        expected = canonical_sha256(paired_trace)
        if rth != expected:
            errors.append(
                f"rewrite_trace_hash: expected {expected} (canonical hash "
                f"of paired trace), got {rth}. Run "
                f"`python tools/regen_cert_hashes.py` to re-pin."
            )

    return errors, warnings


def check_cert_witness_provenance(cert, paired_ir, cert_name=None):
    """R3-M1 gate: every specialization's soundness_witness in a cert
    must resolve to library_provenance entries of the cert's paired
    IR. The witness is a comma-joined list of provenance keys (the
    refinement pass builds it from `embedding_witness:` tags /
    specialization_targets witnesses), so each token is checked
    individually. A dangling witness would let a cert claim an
    embedding lemma nothing in the IR names."""
    errors = []
    name = cert_name or "certificate"
    provenance = paired_ir.get("library_provenance", {})
    specs = cert.get("refinement_record", {}).get("specializations", [])
    for i, spec in enumerate(specs):
        w = spec.get("soundness_witness")
        if w is None:
            continue
        for token in w.split(","):
            if token not in provenance:
                errors.append(
                    f"{name}: refinement_record.specializations[{i}] "
                    f"({spec.get('kind')}, source={spec.get('source')}): "
                    f"soundness_witness token '{token}' has no "
                    "library_provenance entry in the paired IR"
                )
    return errors


def check_identity_trace_hashes(trace, paired_ir, trace_name=None):
    """R2: an identity trace fixture must carry the canonical hash of
    its paired IR in EVERY hash slot (initial, final, each entry's
    before/after) and only non-rewriting outcomes — it documents 'the
    default dispatch pipeline left this IR untouched'."""
    from canonical_hash import canonical_sha256
    errors = []
    ir_hash = canonical_sha256(paired_ir)
    name = trace_name or "trace"
    for field in ("initial_ir_hash", "final_ir_hash"):
        if trace.get(field) != ir_hash:
            errors.append(
                f"{name}: {field} must equal the paired IR's canonical "
                f"hash {ir_hash}, got {trace.get(field)}. Run "
                f"`python tools/regen_cert_hashes.py` to re-pin."
            )
    for i, entry in enumerate(trace.get("entries", [])):
        for field in ("before_hash", "after_hash"):
            if entry.get(field) != ir_hash:
                errors.append(
                    f"{name}: entries[{i}].{field} must equal the paired "
                    f"IR's canonical hash, got {entry.get(field)}"
                )
        if entry.get("outcome") not in ("no_op", "skipped_preconditions"):
            errors.append(
                f"{name}: entries[{i}].outcome "
                f"'{entry.get('outcome')}' is a rewriting outcome — an "
                "identity trace may only carry no_op / "
                "skipped_preconditions entries"
            )
    return errors


def emit_warnings(warnings, out=sys.stdout) -> None:
    """Print non-blocking warnings (one per line, `WARNING:` prefix so
    they are greppable in a CI log; the messages name their files).
    Shared with validate.py; never affects the exit status of either
    driver."""
    for msg in warnings:
        print(f"WARNING: {msg}", file=out)


def check_trace(trace, registry):
    errors, warnings = [], []
    pass_ids = {p["id"] for p in registry["rewriter_passes"]}
    entries = trace["entries"]
    for entry in entries:
        if entry["pass"] not in pass_ids:
            warnings.append(f"trace pass '{entry['pass']}' not in registry.rewriter_passes")

    # Hash-chain continuity (audit M1). The schema validates that each
    # hash is a well-formed sha256:<64hex>; it cannot express that the
    # per-pass hashes form a contiguous chain from initial_ir_hash to
    # final_ir_hash. Without this a trace can claim to describe a
    # rewrite of one IR while the segments don't actually connect —
    # exactly the "fixture hashes don't even match across files" class
    # of inconsistency. This is checkable without reproducing the
    # OCaml canonicalization: it is pure within-document linkage.
    init = trace["initial_ir_hash"]
    final = trace["final_ir_hash"]
    if not entries:
        if init != final:
            errors.append(
                "empty trace must have initial_ir_hash == final_ir_hash "
                f"(got {init} vs {final})"
            )
    else:
        if entries[0]["before_hash"] != init:
            errors.append(
                f"entries[0].before_hash ({entries[0]['before_hash']}) "
                f"!= initial_ir_hash ({init})"
            )
        if entries[-1]["after_hash"] != final:
            errors.append(
                f"entries[-1].after_hash ({entries[-1]['after_hash']}) "
                f"!= final_ir_hash ({final})"
            )
        for i in range(len(entries) - 1):
            a = entries[i]["after_hash"]
            b = entries[i + 1]["before_hash"]
            if a != b:
                errors.append(
                    f"trace chain break: entries[{i}].after_hash ({a}) "
                    f"!= entries[{i + 1}].before_hash ({b})"
                )
        # The schema says a 'failed' pass leaves the IR untouched
        # (after_hash == before_hash); a 'no_op' likewise made no
        # changes. Enforce that invariant here (the schema cannot).
        # (R2 bugfix: this read entry["status"], a field that does
        # not exist — the schema and both codecs call it "outcome" —
        # so the invariant had never actually fired.)
        for i, entry in enumerate(entries):
            st = entry.get("outcome")
            if st in ("failed", "no_op") and \
                    entry["after_hash"] != entry["before_hash"]:
                errors.append(
                    f"entries[{i}] outcome='{st}' must leave the IR "
                    f"unchanged (after_hash == before_hash), got "
                    f"{entry['before_hash']} -> {entry['after_hash']}"
                )

    return errors, warnings


PREFIX_HANDLER = [
    ("example", "ir"),
    ("cert-", "certificate"),
    ("manifest-", "manifest"),
    ("rewrite-trace-", "trace"),
]


def kind_for(name: str) -> str | None:
    for prefix, kind in PREFIX_HANDLER:
        if name.startswith(prefix):
            return kind
    return None


def check_unknown_fixture_names(fixture_names=None):
    """C2 round 2, Low: discovery itself was prefix-opt-in — a fixture
    whose name matches no PREFIX_HANDLER prefix (e.g. probe-cert.json)
    was checked by nothing and mentioned nowhere, the same vacuity
    pattern one level above pairing completeness. Every examples/*.json
    must match a known prefix; an unrecognized name is an error, not a
    silent skip."""
    if fixture_names is None:
        fixture_names = sorted(p.name for p in EXAMPLES.glob("*.json"))
    prefixes = ", ".join(p for p, _ in PREFIX_HANDLER)
    errors = []
    for name in fixture_names:
        if kind_for(name) is None:
            errors.append(
                f"examples/{name}: name matches no PREFIX_HANDLER prefix "
                f"({prefixes}) — an unrecognized fixture is checked by "
                "nothing; rename it or add a handler (tools/check.py)")
    return errors


def main() -> int:
    with REGISTRY_FILE.open() as f:
        registry = json.load(f)

    failed = 0
    total_warnings = 0

    # Repo-level source-scan checks (R2.4): trace_format literals in
    # sdk/lib registered; the SDK's baked-in always-unfold list in
    # sync with the registry.
    repo_errors = (check_sdk_trace_format_literals(registry)
                   + check_always_unfold_pin(registry))
    if repo_errors:
        print("FAIL sdk/lib source-scan checks")
        for msg in repo_errors:
            print(f"  ERROR  {msg}")
        failed += 1
    else:
        print("OK   sdk/lib source-scan checks (trace_format literals, "
              "always_unfold pin)")

    # Pairing completeness (C2 round 1): the per-fixture R2 gates below
    # only fire for fixtures the pairing maps know about, so an unpaired
    # fixture must be an error here, not a silent skip there.
    pairing_errors = check_fixture_pairing_completeness()
    if pairing_errors:
        print("FAIL examples/ pairing completeness")
        for msg in pairing_errors:
            print(f"  ERROR  {msg}")
        failed += 1
    else:
        print("OK   examples/ pairing completeness (every cert in all "
              "three pairing maps; every identity trace in TRACE_IR_PAIRS)")

    name_errors = check_unknown_fixture_names()
    if name_errors:
        print("FAIL examples/ fixture-name discovery")
        for msg in name_errors:
            print(f"  ERROR  {msg}")
        failed += 1
    else:
        print("OK   examples/ fixture-name discovery (every *.json matches "
              "a PREFIX_HANDLER prefix)")

    for fixture in sorted(EXAMPLES.glob("*.json")):
        kind = kind_for(fixture.name)
        if kind is None:
            continue
        with fixture.open() as f:
            doc = json.load(f)

        errors: list[str] = []
        warnings: list[str] = []
        hash_warnings: list[str] = []   # non-blocking, WARNING: lines
        if kind == "ir":
            e, w = check_ir(doc)
            errors += e
            warnings += w
            e, w = check_ir_against_registry(doc, registry)
            errors += e
            warnings += w
        elif kind == "certificate":
            e, w = check_certificate(doc, registry)
            errors += e
            warnings += w
            manifest_name = CERT_MANIFEST_PAIRS.get(fixture.name)
            if manifest_name is not None:
                with (EXAMPLES / manifest_name).open() as f:
                    paired_manifest = json.load(f)
                paired_ir = None
                ir_name = CERT_IR_PAIRS.get(fixture.name)
                if ir_name is not None:
                    with (EXAMPLES / ir_name).open() as f:
                        paired_ir = json.load(f)
                paired_trace = None
                trace_name = CERT_TRACE_PAIRS.get(fixture.name)
                if trace_name is not None:
                    with (EXAMPLES / trace_name).open() as f:
                        paired_trace = json.load(f)
                e, w = check_cert_hashes(
                    doc, paired_ir=paired_ir, paired_manifest=paired_manifest,
                    cert_name=str(fixture.relative_to(ROOT)),
                    manifest_name=str((EXAMPLES / manifest_name).relative_to(ROOT)),
                    paired_trace=paired_trace,
                )
                errors += e
                hash_warnings += w
                errors += check_cert_manifest_consistency(
                    doc, paired_manifest,
                    cert_name=str(fixture.relative_to(ROOT)))
                if paired_ir is not None:
                    errors += check_cert_witness_provenance(
                        doc, paired_ir,
                        cert_name=str(fixture.relative_to(ROOT)))
        elif kind == "manifest":
            e, w = check_manifest(doc, registry)
            errors += e
            warnings += w
        elif kind == "trace":
            e, w = check_trace(doc, registry)
            errors += e
            warnings += w
            ir_name = TRACE_IR_PAIRS.get(fixture.name)
            if ir_name is not None:
                with (EXAMPLES / ir_name).open() as f:
                    paired_ir = json.load(f)
                errors += check_identity_trace_hashes(
                    doc, paired_ir, trace_name=str(fixture.relative_to(ROOT)))

        rel = fixture.relative_to(ROOT)
        if errors:
            print(f"FAIL {rel}")
            for msg in errors:
                print(f"  ERROR  {msg}")
            for msg in warnings:
                print(f"  WARN   {msg}")
            failed += 1
        elif warnings:
            print(f"WARN {rel}")
            for msg in warnings:
                print(f"  WARN   {msg}")
            total_warnings += len(warnings)
        else:
            print(f"OK   {rel}")
        if hash_warnings:
            emit_warnings(hash_warnings)
            total_warnings += len(hash_warnings)

    print()
    if failed:
        print(f"{failed} fixture(s) have cross-doc errors.")
        return 1
    if total_warnings:
        print(f"All cross-doc checks pass ({total_warnings} warning(s)).")
    else:
        print("All cross-doc checks pass.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
