"""Cheap orchestration and false-success regression checks; execute no proof tools."""
import contextlib
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import verify


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value))


class VerificationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.lock = {"lean_toolchain": "leanprover/lean4:v4.29.0-rc6",
                     "audit": {"run_sha256": "audit", "constants": 3},
                     "tools": {"nanoda": {"rust_toolchain": "1.93.1"}}}

    def test_individual_and_all_dispatch(self):
        expected = {
            "lean": ["dependency-cache", "lean"],
            "comparator": ["dependency-cache", "project-build", "comparator"],
            "nanoda": ["dependency-cache", "rust-toolchain", "nanoda"],
            "all": ["dependency-cache", "lean", "comparator", "rust-toolchain", "nanoda"],
        }
        write_json(self.base / "verification/tools-lock.json", self.lock)
        (self.base / "lean-toolchain").write_text(self.lock["lean_toolchain"])
        for mode, names in expected.items():
            with self.subTest(mode=mode):
                runner = verify.Verification.__new__(verify.Verification)
                runner.project, runner.work = self.base, self.base / "fresh-work"
                runner.mode, runner.jobs, runner.env = mode, 3, {"PATH": "/mock"}
                runner.state = {"checks": {}}
                calls, messages = [], []
                runner.command = lambda name, argv: calls.append((name, argv))
                runner.save = lambda: None
                runner.emit = messages.append
                with patch.object(verify.platform, "system", return_value="Linux"), \
                     patch.object(verify.shutil, "which", side_effect=lambda name, **kw: "/mock/" + name), \
                     patch.object(verify, "validate_audit", return_value={}), \
                     patch.object(verify, "validate_comparator", return_value={}), \
                     patch.object(verify, "validate_nanoda", return_value={}):
                    runner.run()
                self.assertEqual([name for name, argv in calls], names)
                if mode in ("all", "comparator"):
                    argv = next(argv for name, argv in calls if name == "comparator")
                    self.assertIn("run", argv)
                    self.assertIn("--trusted-local", argv)
                if mode in ("all", "nanoda"):
                    argv = next(argv for name, argv in calls if name == "rust-toolchain")
                    self.assertEqual(argv[1:], ["toolchain", "install", "1.93.1", "--profile", "minimal"])
                    argv = next(argv for name, argv in calls if name == "nanoda")
                    self.assertIn("--run", argv)
                self.assertEqual(messages[-1], "VERIFICATION PASSED: " + mode)

    def test_command_failure_retains_log_and_stops(self):
        runner = verify.Verification.__new__(verify.Verification)
        runner.project = runner.work = self.base
        runner.env, runner.state, runner.console = os.environ.copy(), {"commands": []}, io.StringIO()
        with contextlib.redirect_stdout(io.StringIO()), self.assertRaisesRegex(RuntimeError, "exited 7"):
            runner.command("failure", [sys.executable, "-c", "print('diagnostic'); raise SystemExit(7)"])
        self.assertEqual((self.base / "failure.log").read_text().strip(), "diagnostic")
        self.assertEqual(runner.state["commands"][0]["returncode"], 7)
        self.assertNotIn("VERIFICATION PASSED", runner.console.getvalue())

    def test_audit_preparation_cannot_pass(self):
        write_json(self.base / "run.json", {"status": "prepared_only", "lean_invoked": False})
        write_json(self.base / "verification.json", {})
        with self.assertRaisesRegex(RuntimeError, "fresh full audit"):
            verify.validate_audit(self.base)

    def test_audit_artifact_drift_cannot_pass(self):
        write_json(self.base / "run.json", {"status": "passed", "lean_invoked": True,
                   "build_returncode": 0, "returncode": 0, "build_input_hashes_unchanged": True,
                   "input_hashes_unchanged": True, "artifact_hashes_unchanged": False})
        write_json(self.base / "verification.json", {})
        with self.assertRaisesRegex(RuntimeError, "stability failed"):
            verify.validate_audit(self.base)

    def comparator(self):
        path = self.base / "runs/new/run.json"
        report = {"status": "passed", "comparator_executed": True,
                  "comparator_verdict": "Your solution is okay!", "mode": "trusted-local-no-sandbox",
                  "source_audit_sha256": "audit", "lock_sha256": "lock"}
        write_json(path, report)
        (path.parent / "comparator.log").write_text("Your solution is okay!\n")
        return path, report

    def test_comparator_configuration_validation_cannot_pass(self):
        path, report = self.comparator()
        report["comparator_executed"] = False
        write_json(path, report)
        with self.assertRaisesRegex(RuntimeError, "did not complete"):
            verify.validate_comparator(self.base, self.lock, "lock")

    def test_comparator_changed_binding_cannot_pass(self):
        path, report = self.comparator()
        report["source_audit_sha256"] = "other-audit"
        write_json(path, report)
        with self.assertRaisesRegex(RuntimeError, "binding differs"):
            verify.validate_comparator(self.base, self.lock, "lock")

    def test_comparator_missing_success_marker_cannot_pass(self):
        path, report = self.comparator()
        (path.parent / "comparator.log").write_text("Configuration valid\n")
        with self.assertRaisesRegex(RuntimeError, "success marker"):
            verify.validate_comparator(self.base, self.lock, "lock")

    def nanoda(self):
        path = self.base / "run-new/run.json"
        report = {"status": "passed", "mode": "run", "phase": "complete",
                  "independent_kernel_check": "passed", "inputs_unchanged": True,
                  "source_binding": "matched", "tools_lock_sha256": "lock",
                  "project_declarations": 3, "checked_declarations": 5}
        write_json(path, report)
        write_json(path.parent / "binding.json", {"run_sha256": "audit", "project_declarations": 3,
                                                   "source_binding": "matched"})
        write_json(path.parent / "export.json", {"declarations": 5, "missing_roots": []})
        (path.parent / "nanoda.stdout").write_text("Checked 5 declarations with no errors\n")
        return path, report

    def test_nanoda_preflight_cannot_pass(self):
        path, report = self.nanoda()
        report["mode"] = "preflight"
        write_json(path, report)
        with self.assertRaisesRegex(RuntimeError, "fresh independent kernel"):
            verify.validate_nanoda(self.base, self.lock, "lock")

    def test_nanoda_partial_count_cannot_pass(self):
        path, report = self.nanoda()
        report["checked_declarations"] = 4
        write_json(path, report)
        with self.assertRaisesRegex(RuntimeError, "scope is missing or inconsistent"):
            verify.validate_nanoda(self.base, self.lock, "lock")


if __name__ == "__main__":
    unittest.main()
