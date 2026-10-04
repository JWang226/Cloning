"""Local guard tests only: these do not execute Lean, the exporter, or Nanoda."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import reproduce as runner


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
