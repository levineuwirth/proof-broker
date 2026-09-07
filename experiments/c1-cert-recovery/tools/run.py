"""Run one campaign pass: every (case, closer) through tools/probe.sh.

Sequential by construction — the case study recorded that overlapping work
moves these timings, so nothing else runs while a pass is in flight. Each run
gets its own log; the parsed table is written next to them.

Build preflight: the FFI shared object the probe loads must be the one that
links the current SDK, and it must be checked BEFORE any timing starts. A pass
run against a stale `proof_broker_ffi.so` measures the previous SDK, silently;
that has happened here. `BUILD_DIAG` is the seam the preflight self-test
injects a failing helper through.
"""
import json, os, re, subprocess, sys, time

RE_TRAILER = re.compile(r"EXIT=(\d+) WALL=([0-9.]+)s CAP=(\S+)")
RE_TACTIC  = re.compile(r"tactic execution ([0-9.]+)(m?s)")
RE_REPORT  = re.compile(r"proof_broker report: (.*)")
RE_ERROR   = re.compile(r"^(.*?):(\d+):(\d+): error: (.*)$", re.M)
RE_PEAK    = re.compile(r"PEAK_RSS_BYTES=(\d+)")

def parse(log):
    txt = open(log, errors="replace").read()
    out = {}
    m = RE_TRAILER.search(txt)
    if m:
        out["exit"] = int(m.group(1)); out["wall_s"] = float(m.group(2))
        out["cap"] = m.group(3)
    tacs = RE_TACTIC.findall(txt)
    if tacs:
        v, u = tacs[-1]
        out["tactic_ms"] = float(v) if u == "ms" else float(v) * 1000.0
    m = RE_PEAK.search(txt)
    if m: out["peak_rss"] = int(m.group(1))
    reps = RE_REPORT.findall(txt)
    if reps:
        out["report"] = reps[-1].strip()
        out["report_fields"] = dict(
            kv.split("=", 1) for kv in reps[-1].split() if "=" in kv)
    errs = RE_ERROR.findall(txt)
    if errs:
        out["error"] = errs[0][3][:400]
        out["n_errors"] = len(errs)
    return out

def build_preflight():
    """Build (and identify) the diagnostic binaries; abort the pass on failure.

    Returns nothing; raises SystemExit(2) rather than letting a single probe
    run against artifacts nobody checked."""
    helper = os.environ.get("BUILD_DIAG", "tools/build_diag.sh")
    r = subprocess.run([helper], stdout=subprocess.DEVNULL,
                       stderr=subprocess.PIPE)
    if r.returncode != 0:
        sys.stderr.write("run.py: diagnostic build failed (exit %d) — "
                         "refusing to run\n" % r.returncode)
        sys.stderr.write(r.stderr.decode(errors="replace"))
        raise SystemExit(2)


def main(run_dir, only=None):
    build_preflight()
    probe = os.environ.get("PROBE_BIN", "tools/probe.sh")
    lean_dir = os.path.join(run_dir, "lean")
    log_dir = os.path.join(run_dir, "logs")
    os.makedirs(log_dir, exist_ok=True)
    files = sorted(f for f in os.listdir(lean_dir) if f.endswith(".lean"))
    if only:
        files = [f for f in files if any(o in f for o in only)]
    results = {}
    t0 = time.time()
    for i, f in enumerate(files, 1):
        case, closer = f[:-5].rsplit(".", 1)
        log = os.path.join(log_dir, f[:-5] + ".log")
        with open(log, "w") as fh:
            subprocess.run([probe, os.path.join(lean_dir, f)],
                           stdout=fh, stderr=subprocess.STDOUT)
        r = parse(log)
        r["case"], r["closer"], r["log"] = case, closer, log
        results.setdefault(case, {})[closer] = r
        print(f"[{i:3d}/{len(files)}] {f:<48} exit={r.get('exit')} "
              f"tac={r.get('tactic_ms')} {r.get('report','')[:70]}", flush=True)
    out = os.path.join(run_dir, "results.json")
    json.dump(results, open(out, "w"), indent=1, sort_keys=True)
    print(f"\n{len(files)} runs in {time.time() - t0:.0f}s -> {out}")

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2:] or None)
