"""Boundary checks on saved proof data. Invoked by run.py self-test.

These edits are to disposable serialized artifacts, never to the frozen task
or upstream repository. No corrupt Lean code is executed on the host.
"""
from __future__ import annotations

import copy
import gzip
import json
from pathlib import Path
import shutil
import tempfile
from dataclasses import replace

import run as r6


class Export:
    def __init__(self, path):
        self.rows = [json.loads(line) for line in path.read_text().splitlines()]
        self.names = {0: ""}
        self.name_ids = {}
        self.exprs = {}
        self.declarations = {}
        for row in self.rows:
            if "in" in row:
                data = row.get("str", row.get("num"))
                prefix = self.names[data["pre"]]
                name = (prefix + "." if prefix else "") + str(data.get("str", data.get("i")))
                self.names[row["in"]] = name
                self.name_ids[name] = row["in"]
            if "ie" in row:
                self.exprs[row["ie"]] = row
            for kind in ["thm", "def", "axiom", "opaque", "ctor", "ind", "rec"]:
                if kind in row:
                    self.declarations[self.names[row[kind]["name"]]] = (row, kind)

    def const_expr(self, name):
        for idx, row in self.exprs.items():
            if row.get("const") == {"name": self.name_ids[name], "us": []}:
                return idx
        raise AssertionError(f"No constant expression for {name}")

    def theorem(self, name):
        row, kind = self.declarations[name]
        assert kind == "thm"
        return row["thm"]

    def write(self, path):
        with path.open("w") as out:
            for row in self.rows:
                out.write(json.dumps(row, separators=(",", ":")) + "\n")

    def make_trivial(self, name):
        theorem = self.theorem(name)
        theorem["type"] = self.const_expr("True")
        theorem["value"] = self.const_expr("True.intro")

    def axiom_proof(self, name, local=r6.LOCAL):
        theorem = self.theorem(local)
        name_id, expr_id = max(self.names) + 1, max(self.exprs) + 1
        additions = [
            {"in": name_id, "str": {"pre": 0, "str": name}},
            {"axiom": {"name": name_id, "isUnsafe": False, "levelParams": [], "type": theorem["type"]}},
            {"ie": expr_id, "const": {"name": name_id, "us": []}}]
        at = self.rows.index(self.declarations[local][0])
        self.rows[at:at] = additions
        theorem["value"] = expr_id

    def inline_local(self, local=r6.LOCAL):
        value = self.exprs[self.theorem(local)["value"]]
        for row in self.rows:
            if row.get("const") == {"name": self.name_ids[local], "us": []}:
                idx = row["ie"]
                row.clear(); row.update(copy.deepcopy(value)); row["ie"] = idx


def integration_tests(checker: Path, out: Path):
    outcomes = []
    with tempfile.TemporaryDirectory(prefix="r6-conformance-") as temp:
        root = Path(temp)
        challenge = root / "challenge.ndjson"
        r6.unpack(r6.TASK / "challenge.ndjson.gz", challenge)
        original = Export(challenge)
        baseline = root / "baseline.ndjson"
        r6.unpack(r6.TASK / "baseline.ndjson.gz", baseline)
        for name, solution in [("pristine_baseline", baseline), ("original_source_binding", challenge)]:
            report = r6.check(baseline, solution, checker, r6.policy([r6.WHOLE]), out / name)
            assert report["accepted"] is True and report["stage"] == "complete", report
            outcomes.append({"case": name, "expected_stage": "complete", "expected_acceptance": True,
                "passed": True, "artifact_sha256": r6.sha(solution), "observed": report})
            print(f"PASS {name}: complete", flush=True)

        def case(name, edit, config, expected_stage, expected_accept=False):
            data = copy.deepcopy(original)
            edit(data)
            solution = root / f"{name}.ndjson"
            data.write(solution)
            report = r6.check(challenge, solution, checker, config, out / name)
            if report["accepted"] != expected_accept or report["stage"] != expected_stage:
                raise AssertionError(f"{name}: expected ({expected_accept}, {expected_stage}), got {report}")
            outcomes.append({"case": name, "expected_stage": expected_stage,
                "expected_acceptance": expected_accept, "passed": True,
                "artifact_sha256": r6.sha(solution), "observed": report})
            print(f"PASS {name}: {report['stage']}", flush=True)

        case("valid_local", lambda _: None, r6.policy([r6.LOCAL]), "complete", True)
        case("valid_whole", lambda _: None, r6.policy([r6.WHOLE], True), "complete", True)
        case("wrong_local_target", lambda d: d.make_trivial(r6.LOCAL), r6.policy([r6.LOCAL]), "challenge_match")
        case("wrong_container", lambda d: d.make_trivial(r6.WHOLE), r6.policy([r6.WHOLE], True), "challenge_match")
        case("local_survives_wrong_container", lambda d: d.make_trivial(r6.WHOLE), r6.policy([r6.LOCAL]), "complete", True)
        case("missing_declaration", lambda d: d.rows.remove(d.declarations[r6.LOCAL][0]), r6.policy([r6.LOCAL]), "challenge_match")
        case("changed_definition", lambda d: d.declarations["Bracket.P"][0]["def"].update(value=d.const_expr("Nat.zero")), r6.policy([r6.LOCAL]), "challenge_match")
        case("forbidden_axiom", lambda d: d.axiom_proof("R6_forbidden_axiom"), r6.policy([r6.LOCAL]), "axiom_policy")
        case("sorry_axiom", lambda d: d.axiom_proof("sorryAx"), r6.policy([r6.LOCAL]), "axiom_policy")
        # Representative new computation-specific axiom; no native_decide code
        # is executed. The test checks the generic allowlist, not an old blacklist.
        case("new_native_axiom_name", lambda d: d.axiom_proof("R6_new_native_decide_axiom"), r6.policy([r6.LOCAL]), "axiom_policy")
        case("invalid_proof", lambda d: d.theorem(r6.LOCAL).update(value=d.const_expr("True.intro")), r6.policy([r6.LOCAL]), "kernel_replay")
        case("inlined_proof_is_valid", lambda d: d.inline_local(), r6.policy([r6.WHOLE]), "complete", True)
        case("missing_local_reference", lambda d: d.inline_local(), r6.policy([r6.WHOLE], True), "local_proof_binding")
        case("wrong_export_format", lambda d: d.rows[0]["meta"]["format"].update(version="99.0.0"), r6.policy([r6.LOCAL]), "export_parse")
        malformed = root / "malformed.ndjson"
        malformed.write_text('{"ie":')
        report = r6.check(challenge, malformed, checker, r6.policy([r6.LOCAL]), out / "malformed_export")
        assert report["accepted"] is False and report["stage"] == "export_parse", report
        outcomes.append({"case": "malformed_export", "expected_stage": "export_parse", "passed": True, "observed": report})
        print("PASS malformed_export: export_parse", flush=True)

        trailing = root / "trailing.ndjson"
        trailing.write_text(challenge.read_text().rstrip("\n") + " garbage\n")
        report = r6.check(challenge, trailing, checker, r6.policy([r6.LOCAL]), out / "trailing_garbage")
        assert report["accepted"] is False and report["stage"] == "export_parse", report
        outcomes.append({"case": "trailing_garbage", "expected_stage": "export_parse", "passed": True, "observed": report})
        print("PASS trailing_garbage: export_parse", flush=True)

        copied = root / "task"
        shutil.copytree(r6.TASK, copied)
        with (copied / "Pristine.lean").open("a") as file:
            file.write("\n-- changed after freeze\n")
        try:
            r6.frozen_task(replace(r6.D1,path=copied))
        except ValueError as error:
            assert "Pristine source hash mismatch" in str(error), error
        else:
            raise AssertionError("Changed pristine source was admitted")
        outcomes.append({"case": "changed_source", "expected_stage": "task_integrity", "passed": True})
        print("PASS changed_source: task_integrity", flush=True)
    r6.write_json(out / "tests.json", {"all_passed": True, "cases": outcomes,
        "replay_binary_sha256": r6.sha(checker), "manifest_sha256": r6.sha(r6.TASK / "manifest.json"),
        "test_source_sha256": r6.sha(Path(__file__)), "runner_sha256": r6.sha(r6.ROOT / "run.py")})
