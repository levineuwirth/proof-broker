#!/usr/bin/env python3
"""Cross-document soundness checks for Phase 0 fixtures.

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
      are registered theory tags.
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

  Adapter manifests
    - logic_fragments, type_constructions, witness_kinds_produced,
      trace_formats_produced are registered.

  Rewrite traces
    - Each entry's pass name is in registry.rewriter_passes. (Warning.)
    - Hash-chain continuity: initial -> per-entry before/after chain ->
      final, and a failed/no_op pass leaves the IR unchanged.

NOT enforced (known, scoped gaps — documented so this docstring does
not overclaim; audit M7. Closing these is behaviour-affecting and is
tracked separately, not silently asserted here):
  - Explicit-object abstract_axioms ({"shape": "explicit", ...}): the
    shape id and any embedded shell term are not validated.
  - TypeMetadata_Primitive.theory_tags: only the type_variable
    instances' theory_classification_tags are registry-checked; the
    primitive-level theory_tags field is not.
  - collect_subshells does not descend into instances[].abstract_signature,
    explicit abstract_axiom shells, or lifting_obligation subterms, so an
    unresolved TypeRef/symbol hiding only there is not caught.
  - Tier-0 and Tier-2 payload contents (e.g. Tier-2 library-lemma
    content_hash) get no registry/hash cross-check; only the
    refinement_record.fragment is validated for those tiers.
  - No cross-document IR<->cert canonical-hash *equality* (would need
    the OCaml codec canonicalization reproduced here); only the
    within-trace hash chain above is enforced.

Errors fail the run; warnings are surfaced but do not.
"""

from __future__ import annotations

import json
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

    theory_tag_ids = {t["id"] for t in registry["theory_tags"]}
    for tid, tm in type_metadata.items():
        if tm.get("kind") == "type_variable":
            for inst in tm.get("instances", []):
                for tag in inst.get("theory_classification_tags", []):
                    if tag not in theory_tag_ids:
                        errors.append(
                            f"type_metadata['{tid}'].instances[].theory_classification_tags: unknown '{tag}'"
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
        wk_ids = {w["id"] for w in registry["adapter_capability_vocabulary"]["witness_kinds"]}
        for w in manifest.get("witness_kinds_produced", []):
            if w not in wk_ids:
                errors.append(f"witness_kinds_produced: unknown '{w}'")
    if 3 in manifest["tiers_produced"]:
        tf_ids = {t["id"] for t in registry["adapter_capability_vocabulary"]["trace_formats"]}
        for tf in manifest.get("trace_formats_produced", []):
            if tf not in tf_ids:
                errors.append(f"trace_formats_produced: unknown '{tf}'")

    return errors, warnings


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
}

# cert filename -> IR filename. Only certs whose dispatch IR is shipped
# as an example fixture appear. cert-example2 (synthetic H2 case-split)
# and cert-example4 (synthetic Tier-3 TPTP) construct their dispatch IR
# in-process and do NOT have a paired example IR; their
# dispatch_context_hash uses the documented unpaired sentinel.
CERT_IR_PAIRS = {
    "cert-example1-tier1-farkas.json": "example1-lia-typeclass.json",
    "cert-example1-tier3-alethe.json": "example1-lia-typeclass.json",
}

# Documented "not a real digest" sentinels. Anything appearing in a cert
# field with one of these values is intentionally not checked for hash
# equality, just for shape conformance (which the schema's ContentHash
# pattern already does). Pinning the exact strings here keeps the
# regen tool and the checker agreed on the convention.
_UNPAIRED_DISPATCH_CONTEXT_HASH = "sha256:" + "0" * 64
_NO_TRACE_HASH = "sha256:" + "0" * 64


def check_cert_hashes(cert, paired_ir=None, paired_manifest=None):
    """Verify a certificate's strict-identity hash linkage to its
    paired fixtures.

    Caller (validate.py) does the pairing-name lookup and loads the
    paired IR / manifest dicts. We compute the canonical SHA-256 and
    compare; mismatches are errors with both sides reported so the
    diagnostic is actionable.

    Both `paired_ir` and `paired_manifest` are optional — a cert with
    no paired IR (synthetic in-process dispatch) is checked for
    manifest linkage only.
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

    if paired_ir is not None:
        expected = canonical_sha256(paired_ir)
        actual = cert.get("dispatch_context_hash")
        if actual != expected:
            errors.append(
                f"dispatch_context_hash: expected {expected} (canonical "
                f"hash of paired IR), got {actual}. Run "
                f"`python tools/regen_cert_hashes.py` to re-pin."
            )

    return errors, warnings


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
        for i, entry in enumerate(entries):
            st = entry.get("status")
            if st in ("failed", "no_op") and \
                    entry["after_hash"] != entry["before_hash"]:
                errors.append(
                    f"entries[{i}] status='{st}' must leave the IR "
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


def main() -> int:
    with REGISTRY_FILE.open() as f:
        registry = json.load(f)

    failed = 0
    total_warnings = 0
    for fixture in sorted(EXAMPLES.glob("*.json")):
        kind = kind_for(fixture.name)
        if kind is None:
            continue
        with fixture.open() as f:
            doc = json.load(f)

        errors: list[str] = []
        warnings: list[str] = []
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
        elif kind == "manifest":
            e, w = check_manifest(doc, registry)
            errors += e
            warnings += w
        elif kind == "trace":
            e, w = check_trace(doc, registry)
            errors += e
            warnings += w

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
