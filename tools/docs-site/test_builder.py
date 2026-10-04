"""Focused regression tests for exact excerpts and offline integrity checks."""
import unittest

from build import Wiki, checker_verdict, lean_mask, offline_proof_map, statement_end, validate_links


class SourceExcerptTests(unittest.TestCase):
    def excerpt(self, source):
        mask = lean_mask(source)
        start = source.index("example") + len("example")
        return source[:statement_end(mask, start, len(mask))].rstrip()

    def test_statement_let_bindings_are_preserved(self):
        source = """theorem example (x : Nat) :
    let y := x + 1
    let z := y + 1
    z = x + 2 := by omega"""
        self.assertEqual(self.excerpt(source), source.split(" := by omega")[0])

    def test_binder_defaults_and_nested_lets_are_not_proof_boundaries(self):
        source = "theorem example (x : Nat := 1) : (let y := x; y) = x := by rfl"
        self.assertEqual(self.excerpt(source), source.split(" := by rfl")[0])

    def test_nested_comments_and_strings_preserve_source_offsets(self):
        source = 'theorem example /- outer /- := -/ inner -/ : "a := b" = "a := b" := by rfl'
        mask = lean_mask(source)
        self.assertEqual(len(mask), len(source))
        self.assertEqual(self.excerpt(source), source.split(" := by rfl")[0])


class GuideCorrespondenceTests(unittest.TestCase):
    def wiki(self):
        wiki = Wiki.__new__(Wiki)
        endpoint = {"name": "Cloning.example", "file": "formalization/Cloning/Example.lean",
                    "line": 7, "url": "source/Cloning.Example.html#L7",
                    "kind": "theorem", "statement": "theorem example : True"}
        wiki.declarations = {endpoint["name"]: endpoint}
        wiki.pointer_uses = []
        wiki.chapters = [{"id": "example", "title": "An informal proof", "summary": "Proof flow.",
                          "assumptions": ["The exact hypotheses are linked."],
                          "steps": [{"title": "Construct the witness", "explanation": "Then conclude.",
                                     "lean": [{"name": endpoint["name"], "file": endpoint["file"]}]}],
                          "results": [{"label": "A readable conclusion", "name": endpoint["name"],
                                       "file": endpoint["file"]}],
                          "limitations": [], "manuscript_labels": ["thm:example"]}]
        wiki.results = {"thm:example": {"label": "thm:example", "title": "The manuscript theorem",
                         "kind": "theorem", "url": "results/thm-example.html", "tex": "Exact TeX.",
                         "line": 17, "parts": [{"label": "thm:example", "scope": "Exact scope.",
                                                "pointers": [endpoint]}]}}
        wiki.files = {}
        wiki.search = []
        return wiki

    def test_friendly_headings_and_reciprocal_named_result_links(self):
        wiki = self.wiki()
        wiki.validate_guides()
        wiki.render_guides()
        wiki.render_results()
        guide = wiki.files["guides/example.html"].decode()
        result = wiki.files["results/thm-example.html"].decode()
        self.assertIn("<h3>A readable conclusion</h3>", guide)
        self.assertIn('href="../results/thm-example.html">The manuscript theorem</a>', guide)
        self.assertIn("Read this part of the proof", result)
        self.assertIn('href="../guides/example.html">An informal proof', result)

    def test_unknown_manuscript_labels_fail(self):
        wiki = self.wiki()
        wiki.chapters[0]["manuscript_labels"] = ["thm:unknown"]
        with self.assertRaisesRegex(ValueError, "Unknown manuscript result"):
            wiki.validate_guides()

    def test_correspondence_requires_a_shared_exact_endpoint(self):
        wiki = self.wiki()
        wiki.results["thm:example"]["parts"][0]["pointers"] = [{"name": "Cloning.unrelated"}]
        with self.assertRaisesRegex(ValueError, "no corresponding Lean endpoint"):
            wiki.validate_guides()

    def test_every_named_result_requires_an_informal_guide(self):
        wiki = self.wiki()
        wiki.chapters[0]["manuscript_labels"] = []
        with self.assertRaisesRegex(ValueError, "Named results missing a proof guide"):
            wiki.validate_guides()


class OfflineIntegrityTests(unittest.TestCase):
    def test_valid_relative_source_anchor(self):
        validate_links({
            "index.html": b'<a href="source/X.html#L17">source</a>',
            "source/X.html": b'<a href="../index.html">home</a><span id="L17">text</span>',
        })

    def test_missing_line_anchor_fails(self):
        with self.assertRaisesRegex(ValueError, "Broken local anchor"):
            validate_links({"index.html": b'<a href="#L99">source</a>'})

    def test_missing_asset_fails(self):
        with self.assertRaisesRegex(ValueError, "Broken local link"):
            validate_links({"index.html": b'<script src="remote.js"></script>'})

    def test_duplicate_anchor_fails(self):
        with self.assertRaisesRegex(ValueError, "Duplicate HTML id"):
            validate_links({"index.html": b'<b id="x"></b><b id="x"></b>'})

    def test_local_links_cannot_escape_standalone_site(self):
        with self.assertRaisesRegex(ValueError, "leaves generated docs"):
            validate_links({"index.html": b'<a href="../formalization/X.lean">x</a>'})


class ProofMapDownloadTests(unittest.TestCase):
    def setUp(self):
        self.files = {
            "reference/cloning.tex": b"manuscript",
            "verification.html": b"audit evidence",
            "data/audit-summary.json": b"{}",
            "source/Cloning.Example.html": b'<span id="L17">exact source</span>',
        }

    def test_repository_links_become_valid_offline_download_links(self):
        original = (
            "Reference: [cloning.tex](reference/cloning.tex).\n"
            "Evidence: [progress](PROGRESS.md), [snapshot](verification/latest.json).\n"
            "Endpoint: [Example.lean](Cloning/Example.lean#L17).\n"
            "Upstream: [reference](https://example.org/proof#statement).\n"
        )
        self.files["reference/PROOF_MAP.md"] = original.encode()
        with self.assertRaisesRegex(ValueError, "Broken local link"):
            validate_links(self.files)

        rewritten = offline_proof_map(original)
        self.assertIn("[cloning.tex](cloning.tex)", rewritten)
        self.assertIn("[progress](../verification.html)", rewritten)
        self.assertIn("[snapshot](../data/audit-summary.json)", rewritten)
        self.assertIn("[Example.lean](../source/Cloning.Example.html#L17)", rewritten)
        self.assertIn("https://example.org/proof#statement", rewritten)
        self.files["reference/PROOF_MAP.md"] = rewritten.encode()
        validate_links(self.files)

    def test_source_fragment_is_preserved_and_validated(self):
        rewritten = offline_proof_map("[endpoint](Cloning/Example.lean#L99)")
        self.assertIn("#L99", rewritten)
        self.files["reference/PROOF_MAP.md"] = rewritten.encode()
        with self.assertRaisesRegex(ValueError, "Broken local anchor"):
            validate_links(self.files)

    def test_new_unbundled_markdown_target_fails(self):
        self.files["reference/PROOF_MAP.md"] = offline_proof_map(
            "[new endpoint](Cloning/NotBundled.lean)"
        ).encode()
        with self.assertRaisesRegex(ValueError, "Broken local link"):
            validate_links(self.files)

    def test_markdown_links_cannot_escape_standalone_site(self):
        with self.assertRaisesRegex(ValueError, "leaves generated docs"):
            validate_links({"reference/PROOF_MAP.md": b"[source](../../formalization/X.lean)"})


class CheckerStatusTests(unittest.TestCase):
    def comparator_records(self):
        summary = {"status": "passed", "source_audit_sha256": "audit",
                   "comparator_executed": True, "comparator_verdict": "Your solution is okay!",
                   "claims": 27, "mode": "trusted-local-no-sandbox"}
        record = {**summary, "lock_sha256": "lock"}
        return summary, record

    def verdict(self, name, summary, record=None, binding=None):
        return checker_verdict(name, summary, record, "audit", 14375, "lock", binding)

    def test_preparation_and_failure_never_display_success(self):
        summary, record = self.comparator_records()
        for status in ("prepared_not_run", "ready_not_run", "failed", "running", "not_run"):
            with self.subTest(status=status):
                summary["status"] = status
                self.assertNotIn("Passed", self.verdict("comparator", summary, record))

    def test_comparator_pass_requires_actual_bound_full_run(self):
        summary, record = self.comparator_records()
        self.assertIn("Passed: 27 statements", self.verdict("comparator", summary, record))
        for field, value in (("status", "failed"), ("comparator_executed", False),
                             ("source_audit_sha256", "other-audit"), ("lock_sha256", "changed-lock"),
                             ("comparator_verdict", "configuration-valid")):
            with self.subTest(field=field):
                with self.assertRaisesRegex(ValueError, "recorded success is not verified"):
                    self.verdict("comparator", summary, {**record, field: value})
        with self.assertRaisesRegex(ValueError, "archived full run did not pass"):
            self.verdict("comparator", summary)

    def test_nanoda_pass_requires_full_scope_count_and_archived_audit_binding(self):
        summary = {"status": "passed", "source_audit_sha256": "audit",
                   "independent_kernel_check": "passed", "project_declarations": 14375,
                   "exported_declarations": 20000}
        record = {"status": "passed", "independent_kernel_check": "passed",
                  "project_declarations": 14375, "checked_declarations": 20000,
                  "mode": "run", "phase": "complete", "inputs_unchanged": True,
                  "tools_lock_sha256": "lock", "source_binding": "matched"}
        binding = {"run_sha256": "audit", "project_declarations": 14375, "source_binding": "matched"}
        self.assertIn("20,000 declarations checked", self.verdict("nanoda", summary, record, binding))
        for changed_record, changed_binding in (
            ({**record, "checked_declarations": 19999}, binding),
            ({**record, "project_declarations": 12}, binding),
            ({**record, "inputs_unchanged": False}, binding),
            (record, {**binding, "run_sha256": "other-audit"}),
            (record, None),
        ):
            with self.assertRaisesRegex(ValueError, "recorded success is not verified"):
                self.verdict("nanoda", summary, changed_record, changed_binding)


if __name__ == "__main__":
    unittest.main()
