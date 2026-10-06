"""Local guard tests only: these do not execute Lean, the exporter, or Nanoda."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import reproduce as runner
from test_check_checkpoint import shared_fixture, write_json


class SharedInventoryBinding(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.project = Path(directory.name) / "project"
        self.archive = self.project / "verification/shared"
        self.run, self.inventory = shared_fixture(self.archive)
        (self.project / "Cloning").mkdir()
        for name in ("Cloning.lean", "Cloning/Fixture.lean"):
            (self.project / name).write_bytes((self.archive / name).read_bytes())
        for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
            (self.project / name).write_text("fixture\n")
            self.run["input_sha256"][name] = runner.sha256(self.project / name)
        self.lock = {"audit": {"run_file": "verification/shared/run.json", "modules": 1, "constants": 2}}
        self.save_run()
        project_patch = patch.object(runner, "PROJECT", self.project)
        project_patch.start()
        self.addCleanup(project_patch.stop)

    def save_run(self):
        path = self.archive / "run.json"
        write_json(path, self.run)
        self.lock["audit"]["run_sha256"] = runner.sha256(path)

    def test_shared_roots_include_private_declarations_and_bind_aggregate_scope(self):
        roots, binding = runner.bound_inventory(self.lock)
        self.assertEqual(roots, [row["name"] for row in self.inventory["declarations"]])
        self.assertTrue(any(name.startswith("_private.") for name in roots))
        self.assertEqual(binding["project_declarations"], 2)
        self.assertEqual(binding["inventory_sha256"], runner.sha256(self.archive / "audit-inventory.json"))
        self.assertEqual(binding["aggregate_axioms"], ["propext"])
        self.assertEqual(binding["axiom_report_scope"], "aggregate union; no per-root axiom attribution")

    def test_source_drift_cannot_reuse_the_saved_root_catalog(self):
        (self.project / "Cloning/Fixture.lean").write_text("theorem changed : True := True.intro\n")
        with self.assertRaisesRegex(RuntimeError, "audited input drift"):
            runner.bound_inventory(self.lock)

    def test_lock_cannot_weaken_complete_root_scope(self):
        self.lock["audit"]["constants"] = 1
        with self.assertRaisesRegex(RuntimeError, "declaration count mismatch"):
            runner.bound_inventory(self.lock)

    def test_forged_derived_inventory_cannot_pass_with_only_an_updated_outer_hash(self):
        altered = dict(self.inventory)
        altered["declarations"] = self.inventory["declarations"][:-1]
        write_json(self.archive / "audit-inventory.json", altered)
        self.run["evidence_sha256"]["audit-inventory.json"] = runner.sha256(self.archive / "audit-inventory.json")
        self.save_run()
        with self.assertRaisesRegex(RuntimeError, "differs from native"):
            runner.bound_inventory(self.lock)

    def test_unknown_schema_cannot_fall_back_to_historical_reports(self):
        self.run["audit_engine"] = "invented"
        self.save_run()
        with self.assertRaisesRegex(RuntimeError, "unknown bound audit engine"):
            runner.bound_inventory(self.lock)


class ExportGuards(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.path = Path(self.tmp.name) / "fixture.ndjson"
        self.lock = {"export_format": "3.1.0", "lean_toolchain": "leanprover/lean4:v4.29.0-rc6"}
        self.records = [
            {"meta": {"format": {"version": "3.1.0"}, "lean": {"version": "4.29.0-rc6"}}},
            {"in": 1, "str": {"pre": 0, "str": "Cloning"}},
            {"in": 2, "str": {"pre": 1, "str": "proof"}},
            {"thm": {"name": 2}},
        ]

    def scan(self, roots=frozenset({"Cloning.proof"})):
        self.path.write_text("".join(json.dumps(r) + "\n" for r in self.records))
        return runner.scan_export(self.path, set(roots), self.lock)

    def test_coverage_counts_a_root(self):
        report = self.scan()
        self.assertEqual(report["declarations"], 1)
        self.assertEqual(report["missing_roots"], [])

    def test_missing_root_fails(self):
        with self.assertRaisesRegex(RuntimeError, "omitted"):
            self.scan({"Cloning.missing"})

    def test_unpermitted_axiom_fails_even_when_unused(self):
        self.records.extend([{"in": 3, "str": {"pre": 0, "str": "sorryAx"}},
                             {"axiom": {"name": 3, "isUnsafe": False}}])
        with self.assertRaisesRegex(RuntimeError, "unpermitted exported axiom"):
            self.scan()

    def test_partial_definition_fails(self):
        self.records[-1] = {"def": {"name": 2, "safety": "partial"}}
        with self.assertRaisesRegex(RuntimeError, "unsafe/partial"):
            self.scan()

    def test_wrong_export_version_fails(self):
        self.records[0]["meta"]["format"]["version"] = "3.2.0"
        with self.assertRaisesRegex(RuntimeError, "format mismatch"):
            self.scan()

    def test_duplicate_root_fails(self):
        self.records.append(copy.deepcopy(self.records[-1]))
        with self.assertRaisesRegex(RuntimeError, "duplicate exported declaration"):
            self.scan()

    def test_axiom_policy_cannot_be_weakened(self):
        config = runner.read_json(runner.HERE / "nanoda-config.json")
        lock = {"permitted_axioms": list(runner.STANDARD_AXIOMS)}
        runner.validate_config(config, lock)
        config["unpermitted_axiom_hard_error"] = False
        with self.assertRaisesRegex(RuntimeError, "hard error"):
            runner.validate_config(config, lock)

    def test_axiom_report_without_destination_fails(self):
        config = runner.read_json(runner.HERE / "nanoda-config.json")
        config.update(print_axioms=True, pp_to_stdout=False)
        lock = {"permitted_axioms": list(runner.STANDARD_AXIOMS)}
        with self.assertRaisesRegex(RuntimeError, "output destination"):
            runner.validate_config(config, lock)


if __name__ == "__main__":
    unittest.main()
