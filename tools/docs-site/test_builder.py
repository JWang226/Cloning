"""Focused regression tests for exact excerpts and offline integrity checks."""
import unittest
from copy import deepcopy
import json
import re
from unittest.mock import patch

from build import ARXIV, ROOT, Wiki, checker_verdict, lean_mask, offline_proof_map, sha, statement_end, validate_links
from paper import paper_structure


class CompiledInventoryTests(unittest.TestCase):
    def wiki(self, engine):
        wiki = Wiki.__new__(Wiki)
        wiki.run = {"audit_engine": engine}
        wiki.audit_dir = ROOT / "formalization/verification/example"
        wiki.read = lambda path: ""
        return wiki

    def test_shared_inventory_keeps_private_metadata_without_assigning_axioms(self):
        wiki = self.wiki("shared")
        constants = [{"name": "Cloning.visible", "kind": "theorem", "private": False},
                     {"name": "_private.Cloning.Example.0.hidden", "kind": "definition", "private": True}]
        inventory = {"modules": [{"module": "Cloning.Example", "constants": constants}],
                     "aggregate_axioms": ["propext"]}
        with patch("build.shared_inventory", return_value=inventory) as validate:
            rows = wiki.compiled_inventory()
        validate.assert_called_once_with(wiki.audit_dir, wiki.run)
        self.assertEqual(rows, [{"module": "Cloning.Example", **row} for row in constants])
        self.assertTrue(all("axioms" not in row for row in rows))

    def test_shared_validation_failure_is_not_rendered_as_a_compiled_inventory(self):
        with patch("build.shared_inventory", side_effect=ValueError("incomplete native traversal")):
            with self.assertRaisesRegex(ValueError, "incomplete native"):
                self.wiki("shared").compiled_inventory()

    def test_historical_inventory_keeps_its_exact_per_root_report(self):
        wiki = self.wiki("historical")
        row = {"module": "Cloning.Example", "name": "Cloning.visible", "kind": "theorem",
               "private": False, "axioms": ["propext"]}
        wiki.read = lambda path: "AXIOM_REPORT " + json.dumps(row) + "\n"
        self.assertEqual(wiki.compiled_inventory(), [row])

    def test_unknown_engine_cannot_produce_an_inventory(self):
        with self.assertRaisesRegex(ValueError, "Unknown recorded audit engine"):
            self.wiki("unknown").compiled_inventory()

    def test_shared_source_pages_explain_aggregate_scope(self):
        wiki = self.wiki("shared")
        wiki.results, wiki.chapters = {}, []
        wiki.dependencies = {"edges": []}
        wiki.files, wiki.search = {}, []
        wiki.modules = {"Cloning.Example": {"name": "Cloning.Example",
                        "file": "formalization/Cloning/Example.lean", "text": "-- fixture\n",
                        "declarations": [], "url": "source/Cloning.Example.html"}}
        wiki.render_sources()
        page = wiki.files["source/Cloning.Example.html"].decode()
        self.assertIn("aggregate union, without attributing axioms to individual declarations", page)


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
                          "paper": {"sections": [{"label": "sec:main-results", "role": "statement"}],
                                    "explanation": "Connect the paper statement to its construction."},
                          "assumptions": ["The exact hypotheses are linked."],
                          "steps": [{"title": "Construct the witness", "explanation": "Then conclude.",
                                     "paper_labels": ["thm:example"],
                                     "lean": [{"name": endpoint["name"], "file": endpoint["file"]}]}],
                          "results": [{"label": "A readable conclusion", "name": endpoint["name"],
                                       "file": endpoint["file"]}],
                          "limitations": [], "manuscript_labels": ["thm:example"]}]
        wiki.results = {"thm:example": {"label": "thm:example", "title": "The manuscript theorem",
                         "kind": "theorem", "url": "results/thm-example.html", "tex": "Exact TeX.",
                         "number": "1.1", "citation": "Theorem 1.1", "anchor": "S1.Thmtheorem1",
                         "section": "1.1", "argument_sections": ["1.1"],
                         "line": 17, "parts": [{"label": "thm:example", "scope": "Exact scope.",
                                                "pointers": [endpoint]}]}}
        wiki.files = {}
        wiki.search = []
        wiki.manuscript = wiki.results
        wiki.paper = {"html_url": "https://arxiv.org/html/2609.35986v1",
                      "paper_url": ARXIV, "version": "v1", "version_url": ARXIV + "v1"}
        section = {"number": "1.1", "title": "Results", "anchor": "S1.SS1", "label": "sec:main-results"}
        wiki.paper_sections = {"1.1": section}
        wiki.paper_labels = {"sec:main-results": section, "section:1.1": section}
        wiki.latest = {"run_sha256": "bound-audit"}
        return wiki

    def test_friendly_headings_and_reciprocal_named_result_links(self):
        wiki = self.wiki()
        wiki.validate_guides()
        wiki.render_guides()
        wiki.render_results()
        guide = wiki.files["guides/example.html"].decode()
        result = wiki.files["results/thm-example.html"].decode()
        self.assertIn("<h3>A readable conclusion</h3>", guide)
        self.assertIn('href="../results/thm-example.html">Theorem 1.1 · The manuscript theorem</a>', guide)
        self.assertIn("Read this part of the proof", result)
        self.assertIn('href="../guides/example.html">An informal proof', result)
        self.assertIn(f'href="{ARXIV}">Read the paper on arXiv', result)
        self.assertNotIn('href="../reference/cloning.tex', result)

    def test_overview_prominently_links_the_paper(self):
        wiki = self.wiki()
        wiki.audit = {"modules": 1, "audited_constants": 1}
        wiki.guides = {"title": "An informal proof", "intro": "Read the argument."}
        wiki.render_overview()
        self.assertIn(f'class="button secondary" href="{ARXIV}">Read the paper on arXiv',
                      wiki.files["index.html"].decode())

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


class StatementReviewTests(unittest.TestCase):
    def wiki(self):
        wiki = Wiki.__new__(Wiki)
        base = "formalization/verification/semantic-pilot/"
        files = {base + "probe.lean.txt": "example : True := True.intro\n",
                 base + "review.md": "Scoped review.\n", base + "output.log": "Checked.\n"}
        files[base + "run.json"] = json.dumps({"exit_code": 0, "probe_sha256": sha(files[base + "probe.lean.txt"]),
                                              "log_sha256": sha(files[base + "output.log"]),
                                              "source_audit_sha256": "audited-sources"})
        entry = {"report": base + "review.md", "probe": base + "probe.lean.txt",
                 "log": base + "output.log", "run": base + "run.json", "lean": []}
        wiki.latest = {"run_sha256": "audited-sources"}
        wiki.results = {label: {} for label in ("thm:known-optimum", "thm:unknown-optimum", "thm:grassmann")}
        wiki.statement_review = {"source_audit_sha256": "audited-sources", "manuscript_sha256": sha("paper"),
                                 "artifacts": {p: sha(v) for p, v in files.items()},
                                 "results": {label: deepcopy(entry) for label in wiki.results}}
        files["formalization/reference/cloning.tex"] = "paper"
        wiki.read = lambda path: files[path.relative_to(ROOT).as_posix()]
        wiki.read_json = lambda path: json.loads(wiki.read(path))
        return wiki, files

    def test_matching_review_evidence(self):
        wiki, _ = self.wiki()
        wiki.validate_statement_review()

    def test_stale_audit_or_manuscript_rejected(self):
        for key in ("source_audit_sha256", "manuscript_sha256"):
            with self.subTest(key=key):
                wiki, _ = self.wiki()
                wiki.statement_review[key] = "stale"
                with self.assertRaises(ValueError):
                    wiki.validate_statement_review()

    def test_altered_report_or_probe_output_rejected(self):
        for file in ("review.md", "probe.lean.txt", "output.log"):
            with self.subTest(file=file):
                wiki, files = self.wiki()
                files["formalization/verification/semantic-pilot/" + file] += "changed"
                with self.assertRaisesRegex(ValueError, "artifact hash differs"):
                    wiki.validate_statement_review()

    def test_unbound_probe_rejected(self):
        wiki, _ = self.wiki()
        wiki.statement_review["results"]["thm:grassmann"]["probe"] = "unbound.txt"
        with self.assertRaisesRegex(ValueError, "missing bound artifact"):
            wiki.validate_statement_review()

    def test_failed_or_wrong_probe_run_rejected_even_with_matching_record_hash(self):
        for run in ({"exit_code": 1}, {"exit_code": 0, "probe_sha256": "wrong"}):
            with self.subTest(run=run):
                wiki, files = self.wiki()
                path = "formalization/verification/semantic-pilot/run.json"
                files[path] = json.dumps(run)
                wiki.statement_review["artifacts"][path] = sha(files[path])
                with self.assertRaisesRegex(ValueError, "probe did not pass"):
                    wiki.validate_statement_review()

    def test_evidence_path_cannot_escape_review_directory(self):
        wiki, _ = self.wiki()
        wiki.statement_review["artifacts"]["formalization/verification/semantic-pilot/../other.md"] = "x"
        with self.assertRaisesRegex(ValueError, "outside evidence directory"):
            wiki.validate_statement_review()

    def test_run_cannot_be_mixed_with_another_log_or_audit(self):
        for key in ("log_sha256", "source_audit_sha256"):
            with self.subTest(key=key):
                wiki, files = self.wiki()
                path = "formalization/verification/semantic-pilot/run.json"
                run = json.loads(files[path])
                run[key] = "different"
                files[path] = json.dumps(run)
                wiki.statement_review["artifacts"][path] = sha(files[path])
                with self.assertRaisesRegex(ValueError, "different log or source audit"):
                    wiki.validate_statement_review()


class PaperCorrespondenceTests(unittest.TestCase):
    def test_remarks_consume_numbers_and_starred_headings_do_not(self):
        text = r"""\section{Introduction}\label{sec:intro}
\subsection{Results}\label{sec:results}
\begin{theorem}\label{thm:first}True\end{theorem}
\begin{remark}A numbering check.\end{remark}
\section*{Glossary}
\begin{corollary}\label{cor:third}True\end{corollary}
\appendix
\section{Auxiliary proof}\label[appendix]{app:aux}
\begin{lemma}\label{lem:appendix}True\end{lemma}"""
        sections, results = paper_structure(text)
        self.assertEqual([s["number"] for s in sections], ["1", "1.1", "A"])
        self.assertEqual(results["cor:third"]["citation"], "Corollary 1.3")
        self.assertEqual(results["cor:third"]["anchor"], "S1.Thmtheorem3")
        self.assertEqual(results["lem:appendix"]["citation"], "Lemma A.1")
        self.assertEqual(sections[-1]["label"], "app:aux")

    def test_unknown_or_missing_step_paper_reference_fails(self):
        for references in ([], ["section:99"]):
            wiki = GuideCorrespondenceTests().wiki()
            wiki.chapters[0]["steps"][0]["paper_labels"] = references
            with self.subTest(references=references), self.assertRaisesRegex(ValueError, "paper reference"):
                wiki.validate_guides()

    def test_reviewed_arxiv_numbering_drift_fails(self):
        wiki = GuideCorrespondenceTests().wiki()
        wiki.paper["sections"] = [{k: s[k] for k in ("number", "title", "anchor")} for s in wiki.paper_sections.values()]
        wiki.paper["results"] = {label: {k: r[k] for k in ("number", "citation", "anchor", "section")} for label, r in wiki.results.items()}
        wiki.validate_paper()
        wiki.paper["results"]["thm:example"]["anchor"] = "S1.Thmtheorem2"
        with self.assertRaisesRegex(ValueError, "numbering or anchor differs"):
            wiki.validate_paper()

    def test_crosswalk_separates_statement_argument_guide_and_lean(self):
        wiki = GuideCorrespondenceTests().wiki()
        section = {"number": "2.3", "title": "Cloning fidelity", "anchor": "S2.SS3", "label": "sec:proof"}
        wiki.paper_sections["2.3"] = section
        wiki.paper_labels["section:2.3"] = section
        wiki.results["thm:example"]["argument_sections"] = ["2.3"]
        wiki.render_correspondence()
        page = wiki.files["correspondence.html"].decode()
        for href in ('https://arxiv.org/html/2609.35986v1#S1.Thmtheorem1',
                     'https://arxiv.org/html/2609.35986v1#S2.SS3',
                     'guides/example.html', 'source/Cloning.Example.html#L7'):
            self.assertIn('href="' + href + '"', page)
        data = json.loads(wiki.files["data/paper-correspondence.json"])["results"][0]
        self.assertEqual(data["statement_section"], "1.1")
        self.assertIn("§2.3", data["argument_sections"][0]["text"])

    def test_sidebar_keeps_high_level_navigation_without_chapter_subtabs(self):
        wiki = GuideCorrespondenceTests().wiki()
        wiki.validate_guides()
        wiki.render_guides()
        page = wiki.files["guides/example.html"].decode()
        sidebar = re.search(r'<aside class="sidebar".*?</aside>', page, re.S)[0]
        self.assertIn('href="../guides/index.html"', sidebar)
        self.assertIn('href="../correspondence.html"', sidebar)
        self.assertNotIn('guides/example.html', sidebar)
        self.assertNotIn('Read the proof', sidebar)
        self.assertIn("Where this guide fits in the paper", page)
        self.assertIn('href="https://arxiv.org/html/2609.35986v1#S1.Thmtheorem1"', page)


class DependencyMapTests(unittest.TestCase):
    def wiki(self):
        wiki = GuideCorrespondenceTests().wiki()
        wiki.validate_guides()
        consumer = deepcopy(wiki.chapters[0])
        consumer.update(id="consumer", title="The later argument", manuscript_labels=[])
        wiki.chapters.append(consumer)
        endpoint = next(iter(wiki.declarations.values()))
        wiki.latest = {"run_sha256": "bound-audit"}
        wiki.dependencies = {
            "title": "Proof route", "intro": "Ingredients and uses.", "legend": "Curated stage contributions.",
            "default_stage": "consumer",
            "nodes": [{"id": "example", "label": "Ingredient"}, {"id": "consumer", "label": "Consumer"}],
            "edges": [{"from": "example", "to": "consumer", "label": "Construct the witness", "kind": "ingredient",
                       "evidence": [{"name": endpoint["name"], "file": endpoint["file"], "note": "The compiled witness is used."}]}],
        }
        return wiki

    def test_stages_cover_guides_and_each_edge_has_compiled_evidence(self):
        wiki = self.wiki()
        wiki.dependencies["nodes"].pop()
        with self.assertRaisesRegex(ValueError, "match the proof guides"):
            wiki.validate_dependencies()
        wiki = self.wiki()
        wiki.dependencies["edges"][0]["evidence"][0]["name"] = "Cloning.missing"
        with self.assertRaisesRegex(ValueError, "Unresolved or ambiguous"):
            wiki.validate_dependencies()

    def test_unknown_targets_and_duplicate_edges_fail(self):
        for change, message in (("unknown", "Unknown dependency edge stage"), ("duplicate", "duplicate dependency edge")):
            wiki = self.wiki()
            if change == "unknown":
                wiki.dependencies["edges"][0]["to"] = "missing"
            else:
                wiki.dependencies["edges"].append(deepcopy(wiki.dependencies["edges"][0]))
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, message):
                wiki.validate_dependencies()

    def test_ingredient_cycles_fail_and_comparisons_do_not_imply_a_dependency(self):
        wiki = self.wiki()
        reverse = deepcopy(wiki.dependencies["edges"][0])
        reverse.update({"from": "consumer", "to": "example"})
        wiki.dependencies["edges"].append(reverse)
        with self.assertRaisesRegex(ValueError, "contains a cycle"):
            wiki.validate_dependencies()
        reverse["kind"] = "comparison"
        wiki.validate_dependencies()

    def test_static_fallback_keeps_stage_guides_results_and_lean_evidence(self):
        wiki = self.wiki()
        wiki.validate_dependencies()
        wiki.render_dependencies()
        page = wiki.files["dependencies.html"].decode()
        self.assertIn('data-from="example" data-to="consumer" data-kind="ingredient"', page)
        self.assertIn('id="stage-example" data-stage="example"', page)
        self.assertIn('href="guides/example.html"', page)
        self.assertIn('href="results/thm-example.html"', page)
        self.assertIn('href="source/Cloning.Example.html#L7"', page)
        self.assertTrue(all("hidden" not in article for article in re.findall(r"<article[^>]*>", page)))
        self.assertIn('data-default-stage="consumer"', page)
        data = json.loads(wiki.files["data/dependencies.json"])
        self.assertEqual(data["source_audit_sha256"], "bound-audit")
        self.assertEqual(data["edges"][0]["evidence"][0]["line"], 7)
        self.assertNotIn("_pointer", str(data))


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

    def test_reader_facing_tex_links_are_rejected_locally_and_externally(self):
        for path, content in (
            ("index.html", b'<a href="reference/cloning.tex">paper</a>'),
            ("index.html", b'<a href="https://example.org/cloning.tex#L7">paper</a>'),
            ("README.md", b'[paper](https://example.org/cloning%2Etex?download=1)'),
            ("README.md", b'[paper](<https://example.org/cloning.tex>)'),
            ("README.md", b'[paper][source]\n\n[source]: <https://example.org/cloning.tex>'),
        ):
            with self.subTest(path=path, content=content):
                with self.assertRaisesRegex(ValueError, "Reader-facing TeX source link"):
                    validate_links({path: content, "reference/cloning.tex": b"source"})


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
        with self.assertRaisesRegex(ValueError, "Reader-facing TeX source link"):
            validate_links(self.files)

        rewritten = offline_proof_map(original)
        self.assertIn(f"[paper on arXiv]({ARXIV})", rewritten)
        self.assertIn("[progress](../verification.html)", rewritten)
        self.assertIn("[snapshot](../data/audit-summary.json)", rewritten)
        self.assertIn("[Example.lean](../source/Cloning.Example.html#L17)", rewritten)
        self.assertIn("https://example.org/proof#statement", rewritten)
        self.files["reference/PROOF_MAP.md"] = rewritten.encode()
        validate_links(self.files)

    def test_legacy_manuscript_fragments_become_a_paper_link(self):
        for href in ("reference/cloning.tex#L17", "cloning.tex?download=1",
                     "https://github.com/example/repo/blob/main/formalization/reference/cloning.tex#L17"):
            with self.subTest(href=href):
                self.assertEqual(offline_proof_map(f"[source]({href})"), f"[paper on arXiv]({ARXIV})")

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
