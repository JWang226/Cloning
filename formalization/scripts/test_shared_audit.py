"""Focused native and provenance tests for the shared axiom audit.

The native cases compile small isolated modules with the project's pinned Lean.
They do not import or rebuild the project proof library.
"""

import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ENGINE = Path(__file__).with_name("shared_audit.py")
PINNED_LEAN = Path.home() / ".elan/toolchains/leanprover--lean4---v4.29.0-rc6/bin/lean"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FIXTURE_SOURCE = """import Lean
namespace Fixture
theorem extensionality (p q : Prop) (h : p ↔ q) : p = q := propext h
noncomputable def chosen (α : Type) (h : Nonempty α) : α := Classical.choice h
theorem sound (r : Nat → Nat → Prop) (a b : Nat) (h : r a b) :
    Quot.mk r a = Quot.mk r b := Quot.sound h
private def hidden (n : Nat) : Nat := n + 1
def visible (n : Nat) : Nat := hidden n
inductive Box where
  | mk : Nat → Box
def shared (n : Nat) : Nat := n + 2
def first (n : Nat) : Nat := shared n
def second (n : Nat) : Nat := shared n
theorem firstEq (n : Nat) : first n = shared n := rfl
theorem secondEq (n : Nat) : second n = shared n := rfl
end Fixture
"""
REFERENCE_DRIVER = """import Cloning
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  for idx in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    if modName == `Cloning || (`Cloning).isPrefixOf modName then
      for name in env.header.moduleData[idx]!.constNames do
        let axioms ← collectAxioms name
        let (_, state) := ((CollectAxioms.collect name).run env).run {}
        let report := Json.mkObj [
          ("module", toJson modName.toString),
          ("name", toJson name.toString),
          ("axioms", toJson ((axioms.qsort Name.lt).map Name.toString)),
          ("dependencies", toJson (state.visited.toArray.map Name.toString))]
        liftIO <| IO.println ("REFERENCE_ROOT " ++ report.compress)
"""


def fixture_env(root):
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join([str(root / "build"), str(root)])
    env["CLONING_LEAN"] = str(PINNED_LEAN)
    env["CLONING_PACKAGES"] = str(root / "packages")
    return env


def compile_module(root, relative):
    output = root / "build" / Path(relative).with_suffix(".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    result = subprocess.run(
        [str(PINNED_LEAN), "-DautoImplicit=false", "-o", str(output), relative],
        cwd=root, env=fixture_env(root), text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=30,
    )
    if result.returncode:
        raise AssertionError(f"Fixture compilation failed for {relative}:\n{result.stdout}")


def run_engine(root, *arguments, env=None):
    copied_engine = root / "audit.py"
    shutil.copy2(ENGINE, copied_engine)
    return subprocess.run(
        [sys.executable, str(copied_engine), *arguments], cwd=root,
        env=fixture_env(root) if env is None else env,
        text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=60,
    )


def read_json(root, name):
    return json.loads((root / name).read_text())


class NativeFixtureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not PINNED_LEAN.is_file():
            raise unittest.SkipTest(f"Pinned Lean fixture compiler is unavailable: {PINNED_LEAN}")
        cls.base_directory = tempfile.TemporaryDirectory(prefix="cloning-shared-audit-base-")
        cls.addClassCleanup(cls.base_directory.cleanup)
        cls.base = Path(cls.base_directory.name)
        (cls.base / "Cloning").mkdir()
        (cls.base / "packages").mkdir()
        (cls.base / "Cloning" / "Fixture.lean").write_text(FIXTURE_SOURCE)
        (cls.base / "Cloning.lean").write_text("import Cloning.Fixture\n")
        compile_module(cls.base, "Cloning/Fixture.lean")
        compile_module(cls.base, "Cloning.lean")
        (cls.base / "Reference.lean").write_text(REFERENCE_DRIVER)
        result = subprocess.run(
            [str(PINNED_LEAN), "-DautoImplicit=false", "Reference.lean"],
            cwd=cls.base, env=fixture_env(cls.base), text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60,
        )
        if result.returncode:
            raise AssertionError(f"Native reference audit failed:\n{result.stdout}")
        cls.reference = [json.loads(line.removeprefix("REFERENCE_ROOT "))
                         for line in result.stdout.splitlines()
                         if line.startswith("REFERENCE_ROOT ")]
        if not cls.reference:
            raise AssertionError("The native reference audit reported no fixture roots")

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="cloning-shared-audit-case-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name) / "snapshot"
        shutil.copytree(self.base, self.root)

    def assert_passed(self, result):
        self.assertEqual(result.returncode, 0, result.stdout)
        summary = read_json(self.root, "verification.json")
        self.assertEqual(summary["axiom_audit"], "passed")
        return summary

    def test_shared_union_matches_native_per_root_collection_and_inventory(self):
        summary = self.assert_passed(run_engine(self.root))
        native_union = {axiom for report in self.reference for axiom in report["axioms"]}
        self.assertEqual(native_union, STANDARD_AXIOMS)
        self.assertEqual(set(summary["aggregate_axioms"]), native_union)
        self.assertEqual(summary["audit_schema"], "cloning-shared-axiom-audit-v1")
        self.assertEqual(summary["audit_strategy"], "shared-transitive-axiom-union")
        self.assertEqual(summary["axiom_report_scope"],
                         "aggregate union; no per-root axiom attribution")
        inventory = read_json(self.root, "audit-inventory.json")
        expected_names = {report["name"] for report in self.reference}
        actual_names = {entry["name"] for entry in inventory["declarations"]}
        self.assertEqual(actual_names, expected_names)
        self.assertEqual(summary["audited_constants"], len(expected_names))
        self.assertTrue(any(entry["private"] for entry in inventory["declarations"]))
        self.assertIn("Fixture.Box.rec", actual_names)
        self.assertIn("Fixture.Box.noConfusion", actual_names)
        self.assertIn("Fixture.Box._sizeOf_1", actual_names)
        exports = {(entry["module"], constant["name"])
                   for entry in inventory["modules"] for constant in entry["constants"]}
        self.assertEqual(exports, {(entry["module"], entry["name"])
                                   for entry in self.reference})
        for declaration in inventory["declarations"]:
            self.assertEqual(set(declaration["exported_by"]),
                             {module for module, name in exports if name == declaration["name"]})
        coverage = summary["aggregate_coverage"]
        native_visited = {name for report in self.reference for name in report["dependencies"]}
        separate_visits = sum(len(report["dependencies"]) for report in self.reference)
        self.assertEqual(coverage["visited_constants"], len(native_visited))
        self.assertLess(coverage["visited_constants"], separate_visits)
        self.assertTrue(coverage["inventory_complete"])
        self.assertTrue(coverage["traversal_complete"])
        self.assertTrue(coverage["includes_private_generated"])
        self.assertEqual(coverage["unique_roots"], len(expected_names))
        self.assertEqual(coverage["export_occurrences"], len(self.reference))
        self.assertEqual(summary["unexpected_axioms"], [])

    def test_forbidden_imported_axiom_is_rejected_by_native_audit(self):
        (self.root / "Forbidden.lean").write_text("namespace Forbidden\naxiom surprise : Nat\nend Forbidden\n")
        fixture = self.root / "Cloning" / "Fixture.lean"
        fixture.write_text("import Forbidden\n" + FIXTURE_SOURCE +
                           "\nnoncomputable def forbiddenValue : Nat := Forbidden.surprise\n")
        compile_module(self.root, "Forbidden.lean")
        compile_module(self.root, "Cloning/Fixture.lean")
        compile_module(self.root, "Cloning.lean")
        result = run_engine(self.root)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        summary = read_json(self.root, "verification.json")
        self.assertEqual(summary["axiom_audit"], "failed")
        self.assertIn("Forbidden.surprise", summary["aggregate_axioms"])
        self.assertEqual(summary["unexpected_axioms"], ["Forbidden.surprise"])
        self.assertTrue(summary["aggregate_coverage"]["traversal_complete"])

    def test_allowed_axiom_policy_accepts_an_observed_subset(self):
        (self.root / "Cloning" / "Fixture.lean").write_text(
            "import Lean\ntheorem simple : True := True.intro\n")
        compile_module(self.root, "Cloning/Fixture.lean")
        compile_module(self.root, "Cloning.lean")
        summary = self.assert_passed(run_engine(self.root))
        self.assertEqual(set(summary["allowed_axioms"]), STANDARD_AXIOMS)
        self.assertEqual(summary["aggregate_axioms"], [])

    def test_generate_only_cannot_be_resummarized_as_a_completed_run(self):
        generated = run_engine(self.root, "--generate-only")
        self.assertEqual(generated.returncode, 0, generated.stdout)
        self.assertTrue((self.root / "Audit.lean").is_file())
        self.assertTrue((self.root / "audit-inputs.json").is_file())
        self.assertFalse((self.root / "verification.json").exists())
        result = run_engine(self.root, "--resummarize")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertFalse((self.root / "verification.json").exists())

    def test_source_placeholder_is_rejected(self):
        source = self.root / "Cloning" / "Fixture.lean"
        source.write_text(FIXTURE_SOURCE + "\ntheorem missingProof : True := by sorry\n")
        result = run_engine(self.root, "--generate-only")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertFalse((self.root / "verification.json").exists())

    def test_comments_and_strings_do_not_trigger_placeholder_scan(self):
        source = self.root / "Cloning" / "Fixture.lean"
        source.write_text(FIXTURE_SOURCE + '''
-- sorry admit axiom sorryAx
/- outer sorry /- inner axiom -/ admit -/
def placeholderWords : String := "sorry admit axiom sorryAx"
''')
        result = run_engine(self.root, "--generate-only")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertTrue((self.root / "Audit.lean").is_file())

    def test_resummarize_requires_unchanged_completed_artifacts(self):
        self.assert_passed(run_engine(self.root))
        self.assert_passed(run_engine(self.root, "--resummarize"))
        artifacts = ["Audit.lean", "audit-inputs.json", "audit-native.jsonl",
                     "audit-inventory.json", "AXIOMS.txt", "Cloning/Fixture.lean"]
        for relative in artifacts:
            with self.subTest(artifact=relative):
                modified = Path(self.directory.name) / relative.replace("/", "-")
                shutil.copytree(self.root, modified)
                path = modified / relative
                path.write_bytes(path.read_bytes() + b"\nTAMPERED\n")
                result = run_engine(modified, "--resummarize")
                self.assertNotEqual(result.returncode, 0, result.stdout)

    def test_native_nonzero_exit_cannot_produce_passed_summary(self):
        failed_lean = self.root / "failed-lean"
        failed_lean.write_text(
            f"#!{sys.executable}\n"
            "import subprocess, sys\n"
            "if sys.argv[1:] in (['--version'], ['--print-prefix']):\n"
            f"    raise SystemExit(subprocess.run([{str(PINNED_LEAN)!r}, *sys.argv[1:]]).returncode)\n"
            "print('fixture native failure', flush=True)\n"
            "raise SystemExit(7)\n"
        )
        failed_lean.chmod(0o755)
        env = fixture_env(self.root)
        env["CLONING_LEAN"] = str(failed_lean)
        result = run_engine(self.root, env=env)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("fixture native failure", (self.root / "AXIOMS.txt").read_text())
        summary_path = self.root / "verification.json"
        if summary_path.exists():
            self.assertNotEqual(read_json(self.root, "verification.json")["axiom_audit"], "passed")
        result = run_engine(self.root, "--resummarize")
        self.assertNotEqual(result.returncode, 0, result.stdout)


class ParserTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        spec = importlib.util.spec_from_file_location("shared_audit_under_test", ENGINE)
        cls.engine = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = cls.engine
        spec.loader.exec_module(cls.engine)

    def setUp(self):
        self.source_digest = "7" * 64
        self.modules = ["Cloning", "Cloning.Fixture"]
        self.events = [
            {"event": "begin", "audit_schema": "cloning-shared-axiom-audit-v1",
             "source_manifest_sha256": self.source_digest, "imported_modules": 2},
            {"event": "module", "module": "Cloning.Fixture", "constant_count": 3,
             "constants": [
                 {"name": "Fixture.first", "kind": "definition", "private": False},
                 {"name": "_private.Cloning.Fixture.0.Fixture.hidden",
                  "kind": "definition", "private": True},
                 {"name": "Fixture.Box.rec", "kind": "recursor", "private": False}]},
            {"event": "module", "module": "Cloning", "constant_count": 1,
             "constants": [{"name": "Fixture.first", "kind": "definition", "private": False}]},
            {"event": "inventory_complete", "imported_modules": 2,
             "export_occurrences": 4, "unique_roots": 3},
            {"event": "aggregate", "root_count": 3, "visited_constants": 9,
             "axioms": sorted(STANDARD_AXIOMS)},
            {"event": "complete", "passed": True},
        ]

    def encoded(self, events=None):
        return "".join(json.dumps(event) + "\n" for event in
                       (self.events if events is None else events))

    def parse(self, text=None, modules=None, source_digest=None):
        return self.engine.parse_native_output(
            self.encoded() if text is None else text,
            self.modules if modules is None else modules,
            self.source_digest if source_digest is None else source_digest,
        )

    def test_identical_repeated_exports_are_deduplicated(self):
        inventory = self.parse()
        self.assertEqual(inventory["coverage"]["export_occurrences"], 4)
        self.assertEqual(inventory["coverage"]["unique_roots"], 3)
        first = next(item for item in inventory["declarations"]
                     if item["name"] == "Fixture.first")
        self.assertEqual(first["exported_by"], ["Cloning", "Cloning.Fixture"])
        self.assertEqual(set(inventory["aggregate_axioms"]), STANDARD_AXIOMS)

    def test_malformed_incomplete_or_duplicate_framing_is_rejected(self):
        output = self.encoded()
        cases = {
            "missing trailing newline": output.rstrip("\n"),
            "missing begin": self.encoded(self.events[1:]),
            "missing completion": self.encoded(self.events[:-1]),
            "duplicate completion": self.encoded([*self.events, self.events[-1]]),
            "duplicate module": self.encoded([self.events[0], self.events[1], *self.events[1:]]),
            "extra event": output + '{"event":"extra"}\n',
            "malformed JSON": output + "{\n",
            "blank record": output + "\n",
            "duplicate JSON key": output.replace('"passed": true', '"passed": true, "passed": true'),
            "non-finite JSON number": output.replace('"visited_constants": 9', '"visited_constants": NaN'),
        }
        for label, text in cases.items():
            with self.subTest(case=label), self.assertRaises(self.engine.AuditError):
                self.parse(text)

    def test_source_binding_and_expected_modules_are_required(self):
        for label, arguments in [
            ("different source", {"source_digest": "8" * 64}),
            ("missing source module", {"modules": [*self.modules, "Cloning.Missing"]}),
            ("duplicate expected module", {"modules": [*self.modules, "Cloning"]}),
        ]:
            with self.subTest(case=label), self.assertRaises(self.engine.AuditError):
                self.parse(**arguments)

    def test_coverage_counters_and_metadata_are_checked(self):
        cases = [
            ("begin module count", 0, "imported_modules", 1),
            ("module constant count", 1, "constant_count", 2),
            ("export occurrence count", 3, "export_occurrences", 3),
            ("unique root count", 3, "unique_roots", 2),
            ("aggregate root count", 4, "root_count", 2),
            ("omitted visited roots", 4, "visited_constants", 2),
            ("boolean counter", 4, "visited_constants", True),
            ("negative counter", 4, "visited_constants", -1),
            ("unknown module", 1, "module", "Other"),
        ]
        for label, index, key, value in cases:
            events = json.loads(json.dumps(self.events))
            events[index][key] = value
            with self.subTest(case=label), self.assertRaises(self.engine.AuditError):
                self.parse(self.encoded(events))
        for label, mutate in [
            ("unknown constant kind", lambda events: events[1]["constants"][0].update(kind="invalid")),
            ("false private flag", lambda events: events[1]["constants"][1].update(private=False)),
            ("conflicting repeated declaration", lambda events: events[2]["constants"][0].update(kind="theorem")),
            ("duplicate aggregate axiom", lambda events: events[4]["axioms"].append("propext")),
        ]:
            events = json.loads(json.dumps(self.events))
            mutate(events)
            with self.subTest(case=label), self.assertRaises(self.engine.AuditError):
                self.parse(self.encoded(events))

    def test_forbidden_axiom_requires_failed_native_verdict(self):
        self.events[4]["axioms"].append("Forbidden.surprise")
        with self.assertRaises(self.engine.AuditError):
            self.parse()
        self.events[-1]["passed"] = False
        inventory = self.parse()
        self.assertFalse(inventory["native_passed"])
        self.assertIn("Forbidden.surprise", inventory["aggregate_axioms"])


if __name__ == "__main__":
    unittest.main()
