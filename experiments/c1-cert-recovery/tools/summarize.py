"""Turn one campaign pass into the report's tables.

Reads runs/<stamp>/results.json (the closer comparison) and
raw/<stamp>/*.report.json (the stage tracer) and writes
runs/<stamp>/summary.md. Nothing is inferred that is not in those files;
where a measurement does not exist the cell says so rather than guessing.
"""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import corpus

CLOSER_ORDER = ["omega", "grind", "pb", "pbterm",
                "pbterm_z3", "pbterm_cvc5", "pbterm_cvc4"]

def status(r):
    if r is None: return "—"
    if r.get("exit") == 0: return "closed"
    e = r.get("error", "")
    if "verifier did not accept" in e: return "refused(tier0)"
    if "no adapter minted a cert" in e: return "refused(no cert)"
    if "ℕ subtraction is truncated" in e: return "refused(reify)"
    if "dispatch_broker failed" in e: return "refused(dispatch)"
    if "linarith failed" in e or "omega could not" in e: return "failed"
    if "The rfl tactic failed" in e: return "failed"
    if e: return "failed"
    return "failed(no error line)"

def rep(r, k):
    if r is None: return ""
    return (r.get("report_fields") or {}).get(k, "")

def cert_route(d, backend):
    """Where a tier-1 witness for this backend came from, if any.

    Three internal routes now, not two: the backend's own proof, the bounded
    coefficient enumeration, and exact recovery — which runs only where the
    enumeration came up empty. Reporting the last two as one "fallback" would
    hide exactly the thing this campaign changed."""
    bd = d["backends"][backend]
    ne = bd.get("native_extraction")
    if isinstance(ne, dict) and ne.get("result") == "ok":
        return "extracted"
    fb = bd.get("fallback_search", {})
    route = fb.get("route")
    if route == "bounded_enumeration":
        return "enumerated"
    if route == "exact_recovery":
        return "exact"
    if fb.get("result") == "ok":          # pre-repair report shape
        return "fallback"
    return "none"

def loss_stage(d, case_status):
    """Which stage lost the certificate, from the tracer alone."""
    if d is None: return "reification (no IR)"
    responses = {b: d["backends"][b].get("solver_response") for b in d["backends"]}
    if all(v != "unsat" for v in responses.values()):
        return "backend search (%s)" % ",".join(f"{k}={v}" for k, v in responses.items())
    for b in ("z3", "cvc5", "cvc4"):
        if cert_route(d, b) != "none":
            return "—(recovered: %s via %s)" % (b, cert_route(d, b))
    native = []
    for b in ("z3", "cvc5"):
        ne = d["backends"][b].get("native_extraction")
        if isinstance(ne, dict):
            native.append(f"{b}:{ne.get('kind') or ne.get('result')}")
    fb = d["backends"]["z3"].get("fallback_search", {})
    kinds = []
    for stage in ("bounded_enumeration", "exact_recovery"):
        st = fb.get(stage)
        if isinstance(st, dict):
            kinds.append("%s:%s" % (stage.split("_")[0],
                                    st.get("kind") or st.get("result")))
    if not kinds and fb.get("kind"):
        kinds = [str(fb.get("kind"))]
    return "extraction (%s) then internal (%s)" % ("; ".join(native),
                                                   "; ".join(kinds))

def main(run_dir):
    stamp = os.path.basename(run_dir.rstrip("/"))
    res = json.load(open(os.path.join(run_dir, "results.json")))
    raw = os.path.join("raw", stamp)
    diag = {}
    for c in corpus.CASES:
        p = os.path.join(raw, c["id"] + ".report.json")
        diag[c["id"]] = json.load(open(p)) if os.path.exists(p) else None
    # in-context sites live under O1..O4
    for n in (1, 2, 3, 4):
        p = os.path.join(raw, f"O{n}.report.json")
        if os.path.exists(p): diag[f"O{n}"] = json.load(open(p))

    out = []
    out.append(f"# Campaign pass `{stamp}` — tables\n")

    out.append("\n## 1. Closure, by case and closer\n")
    out.append("`closed` = the closer closed the original goal and the file "
               "elaborated (probe EXIT=0). Everything else is that run's own "
               "named outcome; none of it is a counterexample.\n")
    out.append("| case | truth | " + " | ".join(CLOSER_ORDER) + " |")
    out.append("|" + "---|" * (len(CLOSER_ORDER) + 2))
    for c in corpus.CASES:
        row = res.get(c["id"], {})
        out.append("| `%s` | %s | %s |" % (
            c["id"], c["truth"],
            " | ".join(status(row.get(k)) for k in CLOSER_ORDER)))

    out.append("\n## 2. What the broker closers actually did\n")
    out.append("| case | `proof_broker` closer/backend/tier/format | "
               "`proof_broker_term` closer/backend/tier/format |")
    out.append("|---|---|---|")
    for c in corpus.CASES:
        row = res.get(c["id"], {})
        def cell(k):
            r = row.get(k)
            if r is None: return "—"
            if not r.get("report_fields"):
                return "(no report line) " + status(r)
            f = r["report_fields"]
            return "%s / %s / t%s / %s" % (f.get("closer"), f.get("backend"),
                                           f.get("tier"), f.get("format"))
        out.append("| `%s` | %s | %s |" % (c["id"], cell("pb"), cell("pbterm")))

    out.append("\n## 3. Certificate recovery, per case (stage tracer)\n")
    out.append("`route`: **extracted** from the backend's own proof, "
               "**enumerated** by the bounded coefficient search, **exact** by "
               "exact support-bounded recovery, **none** if nothing produced "
               "one. It is not the same question as `minted tiers`: cvc5 may "
               "prefer its own tier-3 trace over a tier-1 witness it could "
               "also have produced, and the parallel driver then picks among "
               "the minted certs.\n")
    out.append("`need` is the largest multiplier in the smallest witness the "
               "existence probe found over the dispatched IR, re-checked by "
               "the SDK's own `Farkas.verify`. `route` is explained above.\n")
    out.append("| case | inputs | witness exists | support | need | "
               "z3 route | cvc5 route | cvc4 route | minted tiers | where lost |")
    out.append("|" + "---|" * 10)
    ids = ["O1", "O2", "O3", "O4"] + [c["id"] for c in corpus.CASES]
    for cid in ids:
        d = diag.get(cid)
        if d is None:
            out.append("| `%s` | — | — | — | — | — | — | — | — | reification "
                       "(no IR captured) |" % cid)
            continue
        p = d["witness_existence_probe"]
        minted = " ".join("%s=t%s" % (b, (v.get("cert") or {}).get("tier"))
                          if v["outcome"] == "cert" else "%s=FAILED" % b
                          for b, v in d["adapter_minted"].items())
        out.append("| `%s` | %d | %s | %s | %s | %s | %s | %s | %s | %s |" % (
            cid, len(d["farkas_compiled_inputs"]), p["status"],
            p.get("support", "—"), p.get("max_abs_coefficient", "—"),
            cert_route(d, "z3"), cert_route(d, "cvc5"), cert_route(d, "cvc4"),
            minted, loss_stage(d, None)))

    out.append("\n## 4. Costs, separated where observable\n")
    out.append("Solver / extraction / fallback-search / Lean-side numbers are "
               "from different instruments and are NOT summable: the first "
               "three are the stage tracer's own timings of one sequential "
               "replay, the last two are the bridge's per-call report and "
               "Lean's profiler inside the probe. `n/a` = not measured.\n")
    out.append("| case | z3 solve ms | z3 extract ms | enumerate ms | "
               "exact ms | `pbterm` dispatch ms | `pbterm` verify ms | "
               "`pbterm` tactic ms | `omega` tactic ms |")
    out.append("|" + "---|" * 9)
    for c in corpus.CASES:
        d, row = diag.get(c["id"]), res.get(c["id"], {})
        z = (d or {}).get("backends", {}).get("z3", {})
        ne = z.get("native_extraction")
        fb = z.get("fallback_search", {})
        out.append("| `%s` | %s | %s | %s | %s | %s | %s | %s | %s |" % (
            c["id"], z.get("solver_ms", "n/a"),
            (ne.get("ms", "n/a") if isinstance(ne, dict) else "n/a"),
            (fb.get("bounded_enumeration") or {}).get("ms", "n/a"),
            (fb.get("exact_recovery") or {}).get("ms", "n/a"),
            rep(row.get("pbterm"), "dispatch_ms") or "n/a",
            rep(row.get("pbterm"), "verify_ms") or "n/a",
            (row.get("pbterm") or {}).get("tactic_ms", "n/a"),
            (row.get("omega") or {}).get("tactic_ms", "n/a")))

    p = os.path.join(run_dir, "summary.md")
    open(p, "w").write("\n".join(out) + "\n")
    print("wrote", p)

if __name__ == "__main__":
    main(sys.argv[1])
