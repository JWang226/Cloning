"""Saved shared-evidence guards; fixtures do not claim native Lean execution."""
import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import check_checkpoint as checkpoint
import shared_audit as shared


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def shared_fixture(root):
    """Construct synthetic completed evidence for parser/binding guard tests."""
    (root / "Cloning").mkdir(parents=True)
    (root / "Cloning.lean").write_text("import Cloning.Fixture\n")
    (root / "Cloning/Fixture.lean").write_text("theorem visible : True := True.intro\n")
    shutil.copyfile(Path(shared.__file__), root / "audit.py")
    manifest = shared.generate(root)
    constants = [{"name": "Fixture.visible", "kind": "theorem", "private": False},
                 {"name": "_private.Cloning.Fixture.0.Fixture.hidden", "kind": "definition", "private": True}]
    events = [
        {"event": "begin", "audit_schema": shared.SCHEMA,
         "source_manifest_sha256": manifest["source_manifest_sha256"], "imported_modules": 2},
        {"event": "module", "module": "Cloning", "constant_count": 0, "constants": []},
        {"event": "module", "module": "Cloning.Fixture", "constant_count": 2, "constants": constants},
        {"event": "inventory_complete", "imported_modules": 2, "export_occurrences": 2, "unique_roots": 2},
        {"event": "aggregate", "root_count": 2, "visited_constants": 6, "axioms": ["propext"]},
        {"event": "complete", "passed": True},
    ]
    (root / "audit-native.jsonl").write_text("".join(json.dumps(event) + "\n" for event in events))
    (root / "AXIOMS.txt").write_text("Synthetic fixture stdout; not a native certificate.\n")
    inventory = shared.parse_native_output((root / "audit-native.jsonl").read_text(),
                                          manifest["expected_modules"], manifest["source_manifest_sha256"])
    write_json(root / "audit-inventory.json", inventory)
    receipt = {"audit_schema": shared.SCHEMA, "status": "completed", "lean_invoked": True,
               "lean_exit_code": 0, "evidence_sha256": {name: checkpoint.sha256(root / name)
               for name in ("audit-inputs.json", "Audit.lean", "audit-native.jsonl", "AXIOMS.txt")}}
    write_json(root / "audit-run.json", receipt)
    summary = shared.make_summary(manifest, receipt, inventory, root)
    write_json(root / "verification.json", summary)
    run = {"audit_engine": "shared", "status": "passed", "lean_invoked": True,
           "engine_sha256": checkpoint.sha256(root / "audit.py"),
           "build_returncode": 0, "returncode": 0, "build_input_hashes_unchanged": True,
           "input_hashes_unchanged": True, "artifact_hashes_unchanged": True,
           "input_sha256": manifest["source_sha256"],
           **{key: summary[key] for key in ("modules", "theorems", "audited_constants")},
           "evidence_sha256": {path.relative_to(root).as_posix(): checkpoint.sha256(path)
                               for path in root.rglob("*") if path.is_file()}}
    return run, inventory


class SharedEvidenceGuards(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.run, self.inventory = shared_fixture(self.root)

    def validate(self):
        return checkpoint.shared_inventory(self.root, self.run)

    def rehash(self, name):
        self.run["evidence_sha256"][name] = checkpoint.sha256(self.root / name)

    def update_native_receipt(self, events):
        path = self.root / "audit-native.jsonl"
        path.write_text("".join(json.dumps(event) + "\n" for event in events))
        receipt = checkpoint.read_json(self.root / "audit-run.json")
        receipt["evidence_sha256"]["audit-native.jsonl"] = checkpoint.sha256(path)
        write_json(self.root / "audit-run.json", receipt)
        self.rehash("audit-native.jsonl")
        self.rehash("audit-run.json")
        return receipt

    def test_shared_inventory_has_private_roots_and_no_per_root_attribution(self):
        result = self.validate()
        self.assertEqual(result, self.inventory)
        self.assertEqual(len(result["declarations"]), 2)
        self.assertTrue(any(row["private"] for row in result["declarations"]))
        self.assertEqual(result["aggregate_axioms"], ["propext"])
        self.assertTrue(all("axioms" not in row for row in result["declarations"]))

    def test_preparation_failure_or_unstable_run_cannot_pass(self):
        original = copy.deepcopy(self.run)
        for key, value in (("status", "prepared_only"), ("lean_invoked", False),
                           ("build_returncode", 1), ("returncode", 1),
                           ("build_input_hashes_unchanged", False), ("input_hashes_unchanged", False),
                           ("artifact_hashes_unchanged", False)):
            with self.subTest(key=key):
                self.run = {**original, key: value}
                with self.assertRaises(checkpoint.CheckpointError):
                    self.validate()

    def test_unknown_engine_cannot_be_accepted_as_shared(self):
        self.run["audit_engine"] = "invented"
        with self.assertRaisesRegex(checkpoint.CheckpointError, "Expected a shared"):
            self.validate()

    def test_missing_evidence_hash_cannot_pass(self):
        del self.run["evidence_sha256"]["audit-inventory.json"]
        with self.assertRaisesRegex(checkpoint.CheckpointError, "SHA-256 mismatch"):
            self.validate()

    def test_source_change_cannot_pass_after_updating_outer_evidence_hash(self):
        path = self.root / "Cloning/Fixture.lean"
        path.write_text(path.read_text() + "theorem extra : True := True.intro\n")
        self.rehash("Cloning/Fixture.lean")
        with self.assertRaisesRegex(checkpoint.CheckpointError, "proof-source hashes"):
            self.validate()

    def test_saved_inventory_change_cannot_pass_after_rehash(self):
        altered = copy.deepcopy(self.inventory)
        altered["declarations"][0]["private"] = True
        write_json(self.root / "audit-inventory.json", altered)
        self.rehash("audit-inventory.json")
        with self.assertRaisesRegex(checkpoint.CheckpointError, "differs from native"):
            self.validate()

    def test_execution_receipt_failure_cannot_pass_after_rehash(self):
        receipt = checkpoint.read_json(self.root / "audit-run.json")
        receipt["lean_exit_code"] = 1
        write_json(self.root / "audit-run.json", receipt)
        self.rehash("audit-run.json")
        with self.assertRaisesRegex(checkpoint.CheckpointError, "execution receipt"):
            self.validate()

    def test_receipt_and_run_cannot_be_bound_to_different_native_output(self):
        path = self.root / "audit-native.jsonl"
        path.write_text(path.read_text().replace('"visited_constants": 6', '"visited_constants": 7'))
        self.rehash("audit-native.jsonl")
        with self.assertRaisesRegex(checkpoint.CheckpointError, "SHA-256 mismatch"):
            self.validate()

    def test_wrong_summary_or_run_counts_cannot_pass(self):
        original = checkpoint.read_json(self.root / "verification.json")
        altered = {**original, "audited_constants": 3}
        write_json(self.root / "verification.json", altered)
        self.rehash("verification.json")
        with self.assertRaisesRegex(checkpoint.CheckpointError, "summary differs"):
            self.validate()
        write_json(self.root / "verification.json", original)
        self.rehash("verification.json")
        self.run["audited_constants"] = 3
        with self.assertRaisesRegex(checkpoint.CheckpointError, "run count differs"):
            self.validate()

    def test_forged_per_root_axioms_in_derived_inventory_cannot_pass(self):
        altered = copy.deepcopy(self.inventory)
        altered["declarations"][0]["axioms"] = ["propext"]
        write_json(self.root / "audit-inventory.json", altered)
        self.rehash("audit-inventory.json")
        with self.assertRaisesRegex(checkpoint.CheckpointError, "differs from native"):
            self.validate()

    def test_missing_native_module_cannot_pass_after_rebinding_receipt(self):
        events = [json.loads(line) for line in (self.root / "audit-native.jsonl").read_text().splitlines()]
        del events[2]
        self.update_native_receipt(events)
        with self.assertRaisesRegex(shared.AuditError, "Missing imported project module"):
            self.validate()

    def test_wrong_traversed_root_count_cannot_pass_after_rebinding_receipt(self):
        events = [json.loads(line) for line in (self.root / "audit-native.jsonl").read_text().splitlines()]
        events[-2]["root_count"] = 1
        self.update_native_receipt(events)
        with self.assertRaisesRegex(shared.AuditError, "does not cover every unique root"):
            self.validate()

    def test_forbidden_aggregate_cannot_pass_even_with_consistent_inventory_and_summary(self):
        events = [json.loads(line) for line in (self.root / "audit-native.jsonl").read_text().splitlines()]
        events[-2]["axioms"] = ["sorryAx"]
        events[-1]["passed"] = False
        receipt = self.update_native_receipt(events)
        manifest = checkpoint.read_json(self.root / "audit-inputs.json")
        inventory = shared.parse_native_output((self.root / "audit-native.jsonl").read_text(),
                                              manifest["expected_modules"], manifest["source_manifest_sha256"])
        write_json(self.root / "audit-inventory.json", inventory)
        write_json(self.root / "verification.json", shared.make_summary(manifest, receipt, inventory, self.root))
        self.rehash("audit-inventory.json")
        self.rehash("verification.json")
        with self.assertRaisesRegex(checkpoint.CheckpointError, "aggregate axiom policy"):
            self.validate()


if __name__ == "__main__":
    unittest.main()
