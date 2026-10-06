#!/usr/bin/env python3
"""Run new pinned verification checks and retain their logs without changing pins."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def read_json(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def sha256(path):
    value = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def record_info(path, **fields):
    return {"record": str(path), "record_sha256": sha256(path), **fields}


def single_record(work, pattern):
    paths = sorted(work.glob(pattern))
    require(len(paths) == 1, f"Expected one newly generated report in {work}; found {len(paths)}")
    return paths[0]


def validate_audit(output):
    path = output / "run.json"
    report = read_json(path)
    summary = read_json(output / "verification.json")
    require(report.get("status") == "passed" and report.get("lean_invoked") is True,
            "Lean did not complete a fresh full audit")
    require(report.get("build_returncode") == 0 and report.get("returncode") == 0,
            "Lean build or audit subprocess did not pass")
    require(all(report.get(field) is True for field in
                ("build_input_hashes_unchanged", "input_hashes_unchanged", "artifact_hashes_unchanged")),
            "Lean source/configuration or compiled-artifact stability failed")
    require(report.get("audit_engine") == "shared"
            and report.get("engine_sha256") == sha256(output / "audit.py")
            and report.get("engine_sha256") == sha256(ROOT / "formalization/scripts/shared_audit.py"),
            "Lean audit did not run the current shared dependency auditor")
    require(summary.get("axiom_audit") == "passed" and summary.get("source_placeholder_scan") == "passed"
            and summary.get("lean_exit_code") == 0 and set(summary.get("allowed_axioms", [])) == STANDARD_AXIOMS,
            "The complete Lean audit did not satisfy the axiom and placeholder policy")
    require(not any(summary.get(field) for field in ("unexpected_axioms", "missing_modules", "missing_reports",
                                                    "duplicate_reports", "conflicting_reports")),
            "Lean audit reports an axiom or coverage failure")
    aggregate = summary.get("aggregate_axioms")
    coverage = summary.get("aggregate_coverage", {})
    require(summary.get("audit_schema") == "cloning-shared-axiom-audit-v1"
            and summary.get("audit_strategy") == "shared-transitive-axiom-union"
            and summary.get("axiom_report_scope") == "aggregate union; no per-root axiom attribution"
            and isinstance(coverage, dict)
            and coverage.get("inventory_complete") is True and coverage.get("traversal_complete") is True
            and coverage.get("includes_private_generated") is True
            and coverage.get("source_modules") == summary.get("modules")
            and coverage.get("unique_roots") == summary.get("audited_constants")
            and isinstance(aggregate, list) and all(isinstance(name, str) for name in aggregate)
            and set(aggregate) <= STANDARD_AXIOMS,
            "Shared axiom traversal did not certify complete coverage and the permitted aggregate axioms")
    require(all(type(coverage.get(field)) is int for field in
                ("source_modules", "imported_modules", "export_occurrences", "unique_roots", "visited_constants"))
            and coverage["imported_modules"] == coverage["source_modules"] + 1
            and coverage["export_occurrences"] == summary.get("raw_constant_reports")
            and coverage["export_occurrences"] >= coverage["unique_roots"]
            and coverage["visited_constants"] >= coverage["unique_roots"],
            "Shared audit inventory and traversal counts are inconsistent")
    for field in ("modules", "audited_constants"):
        require(type(report.get(field)) is int and report[field] > 0 and report[field] == summary.get(field),
                "Lean audit scope is missing or inconsistent: " + field)
    return record_info(path, audit_engine="shared", modules=report["modules"],
                       audited_constants=report["audited_constants"], aggregate_axioms=aggregate)


def validate_comparator(work, lock, lock_sha256):
    path = single_record(work, "runs/*/run.json")
    report = read_json(path)
    require(report.get("status") == "passed" and report.get("comparator_executed") is True
            and report.get("comparator_verdict") == "Your solution is okay!",
            "Comparator did not complete statement comparison and Lean replay")
    require(report.get("mode") == "trusted-local-no-sandbox"
            and report.get("source_audit_sha256") == lock["audit"]["run_sha256"]
            and report.get("lock_sha256") == lock_sha256,
            "Comparator report mode or pinned source/tool binding differs")
    require("Your solution is okay!" in (path.parent / "comparator.log").read_text(encoding="utf-8"),
            "The fresh Comparator log is missing its success marker")
    return record_info(path, claims=27, mode=report["mode"])


def validate_nanoda(work, lock, lock_sha256):
    path = single_record(work, "run-*/run.json")
    report = read_json(path)
    binding = read_json(path.parent / "binding.json")
    exported = read_json(path.parent / "export.json")
    require(report.get("status") == "passed" and report.get("mode") == "run"
            and report.get("phase") == "complete" and report.get("independent_kernel_check") == "passed"
            and report.get("inputs_unchanged") is True and report.get("source_binding") == "matched",
            "Nanoda did not complete a fresh independent kernel check")
    require(report.get("tools_lock_sha256") == lock_sha256
            and report.get("project_declarations") == lock["audit"]["constants"]
            and binding.get("run_sha256") == lock["audit"]["run_sha256"]
            and binding.get("project_declarations") == lock["audit"]["constants"]
            and binding.get("source_binding") == "matched",
            "Nanoda report does not cover the complete pinned project inventory")
    count = exported.get("declarations")
    require(type(count) is int and count >= lock["audit"]["constants"]
            and report.get("checked_declarations") == count and not exported.get("missing_roots"),
            "Nanoda checked/exported scope is missing or inconsistent")
    markers = re.findall(r"^Checked (\d+) declarations with no errors$",
                         (path.parent / "nanoda.stdout").read_text(encoding="utf-8"), re.MULTILINE)
    require(markers == [str(count)], "The fresh Nanoda log lacks an unqualified full-scope success marker")
    return record_info(path, project_declarations=report["project_declarations"], checked_declarations=count)


class Verification:
    def __init__(self, mode):
        self.project = ROOT / "formalization"
        self.mode = mode
        base = ROOT / ".verify-work"
        base.mkdir(exist_ok=True)
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
        self.work = Path(tempfile.mkdtemp(prefix="run-" + stamp + "-", dir=base))
        self.console = (self.work / "wrapper.log").open("w", encoding="utf-8")
        self.env = os.environ.copy()
        self.env["PATH"] = os.pathsep.join([str(Path.home() / ".elan/bin"),
                                           str(Path.home() / ".cargo/bin"), self.env.get("PATH", "")])
        self.env.pop("LEAN_PATH", None)
        self.env["LEAN_ABORT_ON_PANIC"] = "1"
        self.state = {"status": "running", "mode": mode, "started_utc": datetime.now(timezone.utc).isoformat(),
                      "audit_engine": "shared", "audit_jobs": 1, "commands": [], "checks": {},
                      "environment": {"PATH": self.env["PATH"],
                                      "RUSTUP_HOME": self.env.get("RUSTUP_HOME", str(Path.home() / ".rustup")),
                                      "CARGO_HOME": self.env.get("CARGO_HOME", str(Path.home() / ".cargo")),
                                      "inherited_LEAN_PATH_removed": True},
                      "wrapper_sha256": {p.name: sha256(p) for p in (ROOT / "scripts/verify.sh", Path(__file__))}}
        self.save()
        self.emit("Fresh verification logs: " + str(self.work))

    def emit(self, message):
        print(message, flush=True)
        self.console.write(message + "\n")
        self.console.flush()

    def save(self):
        (self.work / "run.json").write_text(json.dumps(self.state, indent=2) + "\n", encoding="utf-8")

    def command(self, name, argv):
        log = self.work / (name + ".log")
        entry = {"name": name, "argv": [str(x) for x in argv], "cwd": str(self.project), "log": str(log)}
        self.state["phase"] = name
        self.state["commands"].append(entry)
        self.save()
        self.emit("+ " + shlex.join(entry["argv"]))
        self.emit("Log: " + str(log))
        with log.open("w", encoding="utf-8") as output:
            process = subprocess.Popen(entry["argv"], cwd=self.project, env=self.env, text=True,
                                       encoding="utf-8", errors="replace", stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            try:
                for line in process.stdout:
                    output.write(line)
                    output.flush()
                    self.emit(line.rstrip("\n"))
                code = process.wait()
            except BaseException:
                if process.poll() is None:
                    os.killpg(process.pid, signal.SIGTERM)
                    try:
                        process.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait()
                raise
            finally:
                process.stdout.close()
        entry["returncode"] = code
        self.save()
        require(code == 0, f"{name} exited {code}; see {log}")

    def run(self):
        require(platform.system() in ("Darwin", "Linux"), "Use macOS or Linux for these pinned verification runners")
        lock_path = self.project / "verification/tools-lock.json"
        lock = read_json(lock_path)
        lock_sha = sha256(lock_path)
        require((self.project / "lean-toolchain").read_text().strip() == lock["lean_toolchain"],
                "Lean toolchain differs from the tool lock; keep the repository pins")
        self.state["tools_lock_sha256"] = lock_sha
        self.state["source_binding_audit_sha256"] = lock["audit"]["run_sha256"]
        names = ["git", "curl", "tar", "lake"]
        if self.mode in ("all", "nanoda"):
            names += ["rustup", "cargo"]
        tools = {name: shutil.which(name, path=self.env["PATH"]) for name in names}
        missing = [name for name, path in tools.items() if not path]
        self.state["executables"] = tools
        self.save()
        require(not missing, "Missing prerequisites: " + ", ".join(missing) + "; install elan and Rustup as applicable")
        require(any(shutil.which(name, path=self.env["PATH"]) for name in ("cc", "clang", "gcc")),
                "A native C compiler/linker toolchain is required")
        lake = tools["lake"]
        self.command("dependency-cache", [lake, "exe", "cache", "get"])
        if self.mode in ("all", "lean"):
            output = self.work / "lean-audit"
            if "CLONING_AUDIT_JOBS" in self.env:
                self.emit("The shared audit uses one traversal; CLONING_AUDIT_JOBS no longer applies.")
            self.command("lean", [sys.executable, "scripts/audit.py", "--engine", "shared", "--output", output])
            self.state["checks"]["lean"] = validate_audit(output)
            self.save()
        if self.mode in ("all", "comparator"):
            if self.mode == "comparator":
                self.command("project-build", [lake, "build", "All"])
            self.emit("Comparator mode: trusted local execution, no sandbox.")
            output = self.work / "comparator"
            self.command("comparator", ["bash", "verification/comparator/run.sh", "run", "--trusted-local",
                                        "--lake", lake, "--work", output])
            self.state["checks"]["comparator"] = validate_comparator(output, lock, lock_sha)
            self.save()
        if self.mode in ("all", "nanoda"):
            rust = lock["tools"]["nanoda"]["rust_toolchain"]
            self.command("rust-toolchain", [tools["rustup"], "toolchain", "install", rust, "--profile", "minimal"])
            output = self.work / "nanoda"
            self.command("nanoda", ["bash", "verification/nanoda/run.sh", "--run", "--threads", "1", "--work", output])
            self.state["checks"]["nanoda"] = validate_nanoda(output, lock, lock_sha)
            self.save()
        require(sha256(lock_path) == lock_sha, "Tool/source pins changed during verification")
        self.state.update(status="passed", phase="complete", completed_utc=datetime.now(timezone.utc).isoformat())
        self.save()
        self.emit("VERIFICATION PASSED: " + self.mode)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("all", "lean", "comparator", "nanoda"),
                        help="all runs Lean, Comparator, then Nanoda; each mode performs new checks")
    args = parser.parse_args(argv)
    if sys.version_info < (3, 10):
        parser.error("Python 3.10 or newer is required")
    verification = Verification(args.mode)
    try:
        verification.run()
        return 0
    except (RuntimeError, OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        verification.state.update(status="failed", error=str(error), completed_utc=datetime.now(timezone.utc).isoformat())
        verification.save()
        verification.emit("VERIFICATION FAILED: " + args.mode + ": " + str(error))
        return 1
    except KeyboardInterrupt:
        verification.state.update(status="interrupted", completed_utc=datetime.now(timezone.utc).isoformat())
        verification.save()
        verification.emit("VERIFICATION INTERRUPTED: " + args.mode)
        return 130
    finally:
        verification.console.close()


if __name__ == "__main__":
    raise SystemExit(main())
