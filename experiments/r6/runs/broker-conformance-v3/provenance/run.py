#!/usr/bin/env python3
"""R6-000 step 1: freeze a human-proof challenge and replay saved proofs.

Only trusted, checked-in source is compiled in this step. No candidate-source
interface is exposed yet. Validation accepts serialized proof data exclusively.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import difflib
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import signal
import subprocess
import sys
import tempfile
import time

import jsonschema

ROOT = Path(__file__).resolve().parent
TASK = ROOT / "tasks/verinf-d1-70"
LOCAL = "Bracket.lift_cell.r6_d1_70"
WHOLE = "Bracket.lift_cell"
AXIOMS = ["Classical.choice", "Quot.sound", "propext"]
# Comparator/Main.lean at the revision in vendor/sources.lock.json.
PRIMITIVES = ["Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div",
              "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor",
              "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat",
              "List", "eagerReduce", "Nat", "String", "String.mk", "Char",
              "optParam", "autoParam", "semiOutParam", "outParam"]
EXPORT_TARGETS = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind", *AXIOMS, *PRIMITIVES]
SOURCE_HASH = "03b4d5ca39f435b0eed7d79fe70e9cc33c401fc7ec240a4120a194b54de722a2"
OLD = "    have hle : (2:ℕ)^24 + 2 * Zmax ≤ P := by omega"
NEW = OLD.removesuffix("omega") + "r6_capture_human"


def sha(path: Path) -> str:
    with path.open("rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


def read_json(path: Path):
    return json.loads(path.read_text())


def write_json(path: Path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def pack(source: Path, target: Path):
    # No filename or timestamp in the gzip header.
    with source.open("rb") as inp, target.open("wb") as out:
        with gzip.GzipFile(fileobj=out, mode="wb", mtime=0, filename="") as gz:
            shutil.copyfileobj(inp, gz)


def unpack(source: Path, target: Path):
    with gzip.open(source, "rb") as inp, target.open("wb") as out:
        shutil.copyfileobj(inp, out)


def command(args, **kwargs) -> str:
    return subprocess.check_output([str(x) for x in args], text=True, **kwargs).strip()


def policy(targets, binding=False):
    return {"theorem_names": targets, "permitted_axioms": AXIOMS,
            "primitive_names": PRIMITIVES,
            "required_dependency": [WHOLE, LOCAL] if binding else None}


def instrument(source: str) -> str:
    if source.splitlines()[69] != OLD or source.count(OLD) != 1:
        raise ValueError("D1/70 proof location is not the frozen source")
    if not source.startswith("import Mathlib\n"):
        raise ValueError("Unexpected imports")
    return source.replace("import Mathlib\n", "import Mathlib\nimport Capture\n", 1).replace(OLD, NEW, 1)


def trusted_sources():
    if sha(TASK / "Pristine.lean") != SOURCE_HASH:
        raise ValueError("Pristine source hash mismatch")
    for record in read_json(ROOT / "vendor/sources.lock.json"):
        for name, digest in record["files_sha256"].items():
            if sha(ROOT / "vendor" / record["name"] / name) != digest:
                raise ValueError(f"Vendored source changed: {record['name']}/{name}")


def toolchain(version: str) -> Path:
    # Exact installed toolchain selection: no `stable` resolution or update.
    lean = command(["elan", "which", "lean"], env={**os.environ, "ELAN_TOOLCHAIN": f"leanprover/lean4:v{version}"})
    prefix = Path(lean).parent.parent.resolve()
    actual = command([prefix / "bin/lean", "--version"])
    if f"version {version}," not in actual:
        raise ValueError(f"Unexpected toolchain: {actual}")
    return prefix


def build_tools(only_checker=False):
    trusted_sources()
    compiler, validator = (None if only_checker else toolchain("4.32.0")), toolchain("4.32.2")
    projects = [("checker", validator)] if only_checker else [("exporter", compiler), ("checker", validator)]
    for kind, prefix in projects:
        dest = ROOT / ".cache" / kind
        dest.mkdir(parents=True, exist_ok=True)
        shutil.copytree(ROOT / "vendor/lean4export", dest, dirs_exist_ok=True)
        if kind == "checker":
            shutil.copytree(ROOT / "vendor/comparator", dest, dirs_exist_ok=True)
            shutil.copyfile(ROOT / "validate/Replay.lean", dest / "Replay.lean")
            config = ('name = "r6checker"\n[[lean_lib]]\nname = "Export"\n'
                      '[[lean_lib]]\nname = "Comparator"\n[[lean_exe]]\n'
                      'name = "r6-replay"\nroot = "Replay"\n')
            target = "r6-replay"
        else:
            config = ('name = "r6exporter"\n[[lean_lib]]\nname = "Export"\n'
                      '[[lean_exe]]\nname = "lean4export"\nroot = "Main"\n'
                      'supportInterpreter = true\n')
            target = "lean4export"
        (dest / "lakefile.toml").write_text(config)
        (dest / "lean-toolchain").write_text(f"leanprover/lean4:v{'4.32.0' if kind == 'exporter' else '4.32.2'}\n")
        subprocess.run([str(prefix / "bin/lake"), "build", target], cwd=dest, check=True)
    return compiler, ROOT / ".cache/exporter/.lake/build/bin/lean4export", ROOT / ".cache/checker/.lake/build/bin/r6-replay"


def libraries(binary: Path) -> list[Path]:
    # Run ldd only on our trusted binaries, never on a supplied artifact.
    text = command(["ldd", binary])
    return sorted({Path(p) for p in re.findall(r"(/\S+) \(", text)})


def runtime_record(checker):
    bwrap = Path(shutil.which("bwrap"))
    return {"bubblewrap_version": command([bwrap, "--version"]), "bubblewrap_sha256": sha(bwrap),
            "os": list(os.uname()), "python": sys.version,
            "validator_libraries_sha256": {str(p): sha(p) for p in libraries(checker)},
            "repository_head": command(["git", "-C", ROOT, "rev-parse", "HEAD"])}


def limits():
    # Mathlib's mmap-backed imports need more virtual space than resident RAM.
    resource.setrlimit(resource.RLIMIT_AS, (32 * 1024**3, 32 * 1024**3))
    resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
    resource.setrlimit(resource.RLIMIT_FSIZE, (256 * 1024**2, 256 * 1024**2))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def sandbox(binary: Path, argv: list[str], mounts: list[tuple[Path, str]], out: Path,
            label: str, env=None, compiler: Path | None = None, stdout_path: Path | None = None):
    """Empty-root, network/PID/IPC/user-isolated process, one writable output dir.

    The caller chooses read-only inputs. In final replay these are only NDJSON,
    the policy, the replay binary and its dynamic loader/libraries.
    """
    out.mkdir(parents=True, exist_ok=True)
    args = ["bwrap", "--unshare-all", "--die-with-parent", "--new-session", "--cap-drop", "ALL",
            "--clearenv", "--setenv", "PATH", "/no-programs", "--setenv", "LEAN_ABORT_ON_PANIC", "1",
            "--symlink", "usr/lib", "/lib", "--symlink", "usr/lib64", "/lib64",
            "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp", "--dir", "/work",
            "--chdir", "/work"]
    if compiler:
        args += ["--ro-bind", str(compiler / "lib"), "/toolchain/lib",
                 "--ro-bind", str(compiler / "bin/lean"), "/toolchain/bin/lean",
                 "--setenv", "LEAN_SYSROOT", "/toolchain",
                 "--setenv", "LD_LIBRARY_PATH", "/toolchain/lib/lean:/toolchain/lib"]
    for lib in libraries(binary):
        if compiler and lib.is_relative_to(compiler):
            continue  # Supplied at the relocated toolchain path above.
        args += ["--ro-bind", str(lib.resolve()), str(lib)]
    for host, guest in mounts:
        args += ["--ro-bind", str(host.resolve()), guest]
    for key, value in (env or {}).items():
        args += ["--setenv", key, value]
    executable = "/toolchain/bin/program" if compiler else "/runner/bin/program"
    args += ["--ro-bind", str(binary), executable, "--bind", str(out), "/out", executable, *argv]
    write_json(out / f"{label}.command.json", {"argv": args, "timeout_seconds": 150,
               "address_space_bytes": 32 * 1024**3, "cpu_seconds": 120,
               "max_output_file_bytes": 256 * 1024**2})
    start = time.monotonic()
    with (stdout_path or out / f"{label}.stdout").open("wb") as stdout, (out / f"{label}.stderr").open("wb") as stderr:
        proc = subprocess.Popen(args, stdout=stdout, stderr=stderr, start_new_session=True, preexec_fn=limits)
        timed_out = False
        try:
            code = proc.wait(timeout=150)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(proc.pid, signal.SIGKILL)
            code = proc.wait()
    result = {"exit_code": code, "timed_out": timed_out, "wall_seconds": time.monotonic() - start}
    write_json(out / f"{label}.process.json", result)
    if code:
        raise RuntimeError(f"{label} failed ({code}); see {out / (label + '.stderr')}")
    return result


def environment(packages_dir: Path, compiler: Path):
    records, mounts, paths = [], [], []
    for p in read_json(TASK / "upstream-lake-manifest.json")["packages"]:
        root = packages_dir / p["name"]
        if command(["git", "-C", root, "rev-parse", "HEAD"]) != p["rev"]:
            raise ValueError(f"Wrong dependency commit: {root}")
        if command(["git", "-C", root, "status", "--porcelain", "--untracked-files=no"]):
            raise ValueError(f"Modified tracked dependency source: {root}")
        lib = root / ".lake/build/lib/lean"
        if lib.exists():
            guest = f"/env/{p['name']}"
            mounts.append((lib, guest)); paths.append(guest)
        records.append({"name": p["name"], "repository": p["url"], "commit": p["rev"]})
    return mounts, ":".join(paths), {"dependencies": records,
            "elaboration_lean": command([compiler / "bin/lean", "--version"]),
            "elaboration_lean_sha256": sha(compiler / "bin/lean"),
            "validator_lean": command([toolchain("4.32.2") / "bin/lean", "--version"])}


def inventory(mounts, compiler):
    """Logical caches and loadable native objects; hashes, not mtime guesses."""
    files = {}
    for host, guest in [*mounts, (compiler / "lib", "/toolchain/lib")]:
        for path in sorted(host.rglob("*")):
            if path.is_file() and (".olean" in path.name or ".so" in path.name):
                files[f"{guest}/{path.relative_to(host)}"] = sha(path)
    return files


def finalize_freeze(packages_dir: Path):
    if (TASK / "manifest.json").exists():
        raise ValueError("Task manifest already exists")
    compiler = toolchain("4.32.0")
    mounts, _, env = environment(packages_dir, compiler)
    expected = read_json(TASK / "expected.json")
    if env != expected["environment"]:
        raise ValueError("Environment changed while freezing")
    with tempfile.TemporaryDirectory(prefix="r6-inventory-") as temp:
        inv = Path(temp) / "inventory.json"
        write_json(inv, inventory(mounts, compiler))
        pack(inv, TASK / "environment-inventory.json.gz")
    (TASK / "pristine.sha256").write_text(f"{SOURCE_HASH}  Pristine.lean\n")
    files = ["Pristine.lean", "pristine.sha256", "expected.json", "challenge.ndjson.gz",
             "baseline.ndjson.gz", "context/local-context.json", "permitted.patch",
             "upstream-lake-manifest.json", "upstream-lakefile.toml", "lean-toolchain",
             "environment-inventory.json.gz"]
    source = (TASK / "Pristine.lean").read_bytes()
    start = source.index(OLD.encode()) + len(OLD.removesuffix("omega").encode())
    manifest = {
        "schema_version": "r6-task-1", "task_id": "verinf-d1-70", "revision": 1,
        "frozen_at": datetime.now(timezone.utc).isoformat(), "task_unit": "local_obligation",
        "upstream": {"repository": "https://github.com/JamesPetrie/VerInf.git",
            "commit": "c07e03c94884e9084ffaf7a7294fc0907672f6c2",
            "commit_date": "2026-07-21T22:25:27Z", "source_file": "lean/BracketSpike/BracketSpike/Bracket.lean",
            "line": 70, "pristine_sha256": SOURCE_HASH,
            "proof_byte_span": {"start": start, "end_exclusive": start + len(b"omega")}},
        "original_declaration": WHOLE, "local_name": "hle", "saved_local_declaration": LOCAL,
        "local_goal_source": "(2:ℕ)^24 + 2 * Zmax ≤ P",
        "elaborated_context": "context/local-context.json", "expected_declarations": "expected.json",
        "allowed_imports": ["Mathlib"], "trusted_instrumentation_imports": ["Capture"],
        "environment_lock": "upstream-lake-manifest.json",
        "compiled_environment_inventory": "environment-inventory.json.gz",
        "allowed_axioms": AXIOMS,
        "baseline_axioms": {t["name"]: t["axioms"] for t in expected["targets"]},
        "axiom_policy": "transitive_allowlist; report added and removed relative to each baseline",
        "context_policy": "complete_elaborated_context; auxiliary declaration placeholders recorded but excluded",
        "model_context_policy": "undecided; reference human proofs are evaluator-only",
        "permitted_modifications": "permitted.patch; no other source changes",
        "acceptance": {"local_obligation_closed": "expected local theorem/type/definitions/axioms/kernel replay",
            "whole_declaration_validated": "original containing theorem/type/definitions/axioms/kernel replay and local-proof reference",
            "episode_accepted": "local_obligation_closed AND whole_declaration_validated"},
        "artifacts_sha256": {name: sha(TASK / name) for name in files},
        "capture_sha256": sha(ROOT / "capture/Capture.lean"),
        "vendor_lock_sha256": sha(ROOT / "vendor/sources.lock.json")}
    jsonschema.validate(manifest, read_json(ROOT / "schema/task-manifest.schema.json"))
    write_json(TASK / "manifest.json", manifest)


def frozen_task():
    manifest = read_json(TASK / "manifest.json")
    jsonschema.validate(manifest, read_json(ROOT / "schema/task-manifest.schema.json"))
    for name, digest in manifest["artifacts_sha256"].items():
        path = TASK / name
        if not path.resolve().is_relative_to(TASK) or sha(path) != digest:
            raise ValueError(f"Frozen task artifact mismatch: {name}")
    if sha(ROOT / "capture/Capture.lean") != manifest["capture_sha256"]:
        raise ValueError("Capture helper differs from frozen task")
    if sha(ROOT / "vendor/sources.lock.json") != manifest["vendor_lock_sha256"]:
        raise ValueError("Checking libraries differ from frozen task")
    expected = read_json(TASK / "expected.json")
    if expected["policy"] != policy([LOCAL, WHOLE], True):
        raise ValueError("Frozen validation policy differs from evaluator policy")
    return manifest, expected


def compile_and_export(work: Path, compiler: Path, exporter: Path, mounts, lean_path: str, *, original=False):
    inputs, outputs = work / "input", work / "output"
    inputs.mkdir(parents=True)
    outputs.mkdir()
    pristine = (TASK / "Pristine.lean").read_text()
    # Stable module name keeps private declaration names stable across processes.
    (inputs / "Frozen.lean").write_text(pristine if original else instrument(pristine))
    shutil.copyfile(ROOT / "capture/Capture.lean", inputs / "Capture.lean")
    all_mounts = [*mounts, (inputs, "/input")]
    if not original:
        sandbox(compiler / "bin/lean", ["-R", "/input", "-o", "/out/Capture.olean", "/input/Capture.lean"],
                all_mounts, outputs, "capture-build", compiler=compiler)
    sandbox(compiler / "bin/lean", ["-R", "/input", "-o", "/out/Frozen.olean", "/input/Frozen.lean"],
            all_mounts, outputs, "task-build", compiler=compiler,
            env={"LEAN_PATH": lean_path + ":/out", "R6_CAPTURE_OUTPUT": "/out/context.json"})
    export_file = outputs / "proof.ndjson"
    # Export is a separate read-only process: candidate .olean data cannot write
    # the challenge, policy, or prior build artifacts even if it is malformed.
    export_out = work / "export"
    sandbox(exporter, ["Frozen", "--", WHOLE, *([] if original else [LOCAL]), *EXPORT_TARGETS],
            [*mounts, (outputs, "/objects")], export_out, "export", compiler=compiler,
            env={"LEAN_PATH": lean_path + ":/objects"}, stdout_path=export_file)
    return export_file, outputs


def check(challenge: Path, solution: Path, checker: Path, config: dict, out: Path):
    out.mkdir(parents=True)
    with tempfile.TemporaryDirectory(prefix="r6-policy-") as temp:
        policy_file = Path(temp) / "policy.json"
        write_json(policy_file, config)
        try:
            sandbox(checker, ["/challenge.ndjson", "/solution.ndjson", "/policy.json", "/out/verdict.json"],
                    [(challenge, "/challenge.ndjson"), (solution, "/solution.ndjson"), (policy_file, "/policy.json")],
                    out, "replay")
        except RuntimeError:
            if not (out / "verdict.json").is_file():
                return {"accepted": False, "stage": "validation_process", "error": "No trusted verdict produced"}
    report = read_json(out / "verdict.json")
    process = read_json(out / "replay.process.json")
    if report.get("accepted") and process["exit_code"] != 0:
        return {"accepted": False, "stage": "validation_process", "error": "Verdict/exit mismatch"}
    pack(out / "verdict.json", out / "verdict.raw.json.gz")
    for target in report.get("targets", []):
        raw_type = target.pop("type_repr")
        target["type_sha256"] = hashlib.sha256(raw_type.encode()).hexdigest()
        target["type_hash_format"] = "Lean-4.32.2-reprStr-Expr-UTF8"
    write_json(out / "verdict.json", report)
    return report


def accepted(report):
    if not report.get("accepted"):
        raise ValueError(f"{report.get('stage')}: {report.get('error')}")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["build-tools", "freeze", "golden", "validate", "self-test"])
    parser.add_argument("--packages-dir", type=Path, default=ROOT.parents[1] / "lean-bridge/.lake/packages")
    parser.add_argument("--run-dir", type=Path)
    parser.add_argument("--solution", type=Path, help="Saved NDJSON export for validate; never a Lean source file")
    args = parser.parse_args()
    compiler, exporter, checker = build_tools(only_checker=args.action in {"validate", "self-test"})
    if args.action == "build-tools":
        return
    run = (args.run_dir or ROOT / "runs" / f"{args.action}-{time.time_ns()}").resolve()
    run.mkdir(parents=True, exist_ok=False)
    write_json(run / "runtime.json", runtime_record(checker))
    if args.action == "freeze":
        if (TASK / "expected.json").exists():
            raise ValueError("Task is already frozen; introduce a new task revision instead of overwriting it")
        mounts, lean_path, env = environment(args.packages_dir.resolve(), compiler)
        baseline, _ = compile_and_export(run / "baseline", compiler, exporter, mounts, lean_path, original=True)
        challenge, captured = compile_and_export(run / "challenge", compiler, exporter, mounts, lean_path)
        baseline_report = accepted(check(baseline, baseline, checker, policy([WHOLE]), run / "baseline-validation"))
        binding_report = accepted(check(baseline, challenge, checker, policy([WHOLE]), run / "source-binding-validation"))
        local_report = accepted(check(challenge, challenge, checker, policy([LOCAL, WHOLE], True), run / "challenge-validation"))
        pack(challenge, TASK / "challenge.ndjson.gz")
        pack(baseline, TASK / "baseline.ndjson.gz")
        shutil.copyfile(captured / "context.json", TASK / "context/local-context.json")
        pristine = (TASK / "Pristine.lean").read_text()
        patch = "".join(difflib.unified_diff(pristine.splitlines(True), instrument(pristine).splitlines(True),
                                            fromfile="Pristine.lean", tofile="Frozen.lean"))
        (TASK / "permitted.patch").write_text(patch)
        write_json(TASK / "expected.json", {
            "task_id": "verinf-d1-70", "challenge_sha256": sha(challenge),
            "baseline_sha256": sha(baseline), "environment": env,
            "baseline_whole_declaration": baseline_report["targets"][0],
            "source_binding_validated": binding_report["accepted"], "targets": local_report["targets"],
            "policy": policy([LOCAL, WHOLE], True)})
        finalize_freeze(args.packages_dir.resolve())
        print(f"Frozen challenge and source binding: {TASK}")
        return
    manifest, expected = frozen_task()
    if args.action == "self-test":
        from test_validation import integration_tests
        integration_tests(checker, run)
        return
    with tempfile.TemporaryDirectory(prefix="r6-challenge-") as temp:
        challenge = Path(temp) / "challenge.ndjson"
        unpack(TASK / "challenge.ndjson.gz", challenge)
        if sha(challenge) != expected["challenge_sha256"]:
            raise ValueError("Frozen challenge hash mismatch")
        if args.action == "golden":
            mounts, lean_path, env = environment(args.packages_dir.resolve(), compiler)
            if env != expected["environment"]:
                raise ValueError("Environment differs from frozen task")
            with gzip.open(TASK / "environment-inventory.json.gz", "rt") as file:
                frozen_inventory = json.load(file)
            if inventory(mounts, compiler) != frozen_inventory:
                raise ValueError("Compiled environment differs from frozen inventory")
            solution, _ = compile_and_export(run / "human", compiler, exporter, mounts, lean_path)
        else:
            if args.solution is None:
                raise ValueError("validate requires --solution")
            # Copy the artifact into a supervisor-owned directory before checking.
            solution = Path(temp) / "solution.ndjson"
            shutil.copyfile(args.solution, solution)
        local = check(challenge, solution, checker, policy([LOCAL]), run / "validation-local")
        whole = check(challenge, solution, checker, policy([WHOLE], True), run / "validation-whole")
        results = local.get("targets", []) + whole.get("targets", [])
        pack(solution, run / "solution.ndjson.gz")
        baseline_axioms = {t["name"]: set(t["axioms"]) for t in expected["targets"]}
        verdict = {"task_id": "verinf-d1-70", "search_policy": "human_omega" if args.action == "golden" else "saved_export",
            "accepted": local["accepted"] and whole["accepted"],
            "local_obligation_closed": local["accepted"], "whole_declaration_validated": whole["accepted"],
            "challenge_sha256": sha(challenge), "solution_sha256": sha(solution),
            "proof_exporter_sha256": sha(exporter) if args.action == "golden" else None,
            "replay_binary_sha256": sha(checker),
            "manifest_sha256": sha(TASK / "manifest.json"),
            "runtime_sha256": sha(run / "runtime.json"),
            "harness_sources_sha256": {str(p.relative_to(ROOT)): sha(p) for p in
                [ROOT / "run.py", ROOT / "capture/Capture.lean", ROOT / "validate/Replay.lean", ROOT / "vendor/sources.lock.json"]},
            "axiom_delta": {t["name"]: {"added": sorted(set(t["axioms"]) - baseline_axioms[t["name"]]),
                "removed": sorted(baseline_axioms[t["name"]] - set(t["axioms"]))} for t in results},
            "final_validation": {"local": local, "whole": whole}}
        write_json(run / "verdict.json", verdict)
        jsonschema.validate(verdict, read_json(ROOT / "schema/verdict.schema.json"))
        accepted(verdict)
        print(f"Local obligation and containing declaration validated: {run / 'verdict.json'}")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, RuntimeError, subprocess.SubprocessError, OSError, jsonschema.exceptions.ValidationError) as error:
        print(f"R6 validation failed: {error}", file=sys.stderr)
        sys.exit(1)
