"""Safety checks for project-only benchmark invalidation."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("benchmark", Path(__file__).with_name("benchmark_elaboration.py"))
benchmark = importlib.util.module_from_spec(spec)
spec.loader.exec_module(benchmark)


class HeaderImportTests(unittest.TestCase):
    def test_legacy_header_skips_nested_and_line_comments_then_stops_at_body(self):
        text = """/- Copyright. /- import Cloning.Fake -/ -/
-- import Cloning.AlsoFake
import Cloning.Thermal -- a real edge
import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-! Module documentation. import Cloning.NotAnEdge -/
import Cloning.AfterBody
"""
        self.assertEqual(benchmark.header_imports(text),
                         ["Cloning.Thermal", "Mathlib.Analysis.SpecialFunctions.Pow.Real"])

    def test_modern_multiline_import_flags_preserve_every_owned_graph_edge(self):
        sources = {
            "All": "module\npublic import Cloning.Consumer\n",
            "Cloning.Consumer": """\ufeff/- License /- nested -/ -/ module
prelude
public /- across tokens -/ meta import
  Cloning.Public
meta import all Cloning.Private
import Cloning.Other import Mathlib.Data.Real.Basic
public section
/- import Cloning.BodyComment -/
""",
            "Cloning.Public": "module\nprelude\n",
            "Cloning.Private": "module\n",
            "Cloning.Other": "import Cloning.Public\nnamespace Cloning\n",
        }
        graph = {module: [name for name in benchmark.header_imports(text) if name in sources]
                 for module, text in sources.items()}
        self.assertEqual(graph, {"All": ["Cloning.Consumer"],
                                 "Cloning.Consumer": ["Cloning.Public", "Cloning.Private", "Cloning.Other"],
                                 "Cloning.Public": [], "Cloning.Private": [],
                                 "Cloning.Other": ["Cloning.Public"]})

    def test_escaped_identifier_components_normalize_without_losing_literal_dots(self):
        text = "module\nimport «Cloning».«Thermal»\nimport Cloning.«A.B»\nimport Cloning.α₁\n"
        self.assertEqual(benchmark.header_imports(text), ["Cloning.Thermal", "Cloning.«A.B»", "Cloning.α₁"])

    def test_doc_comment_is_a_body_token_even_before_first_import(self):
        self.assertEqual(benchmark.header_imports("/-- Documentation -/\nimport Cloning.NotAHeader\n"), [])

    def test_declaration_body_strings_and_comments_are_not_scanned(self):
        text = 'import Cloning.Real\ndef fake := "import Cloning.Fake"\n/- import Cloning.Fake2 -/\n'
        self.assertEqual(benchmark.header_imports(text), ["Cloning.Real"])

    def test_each_rc6_import_directive_has_exactly_one_identifier(self):
        # Parser.Module.import has one identWithPartialTrailingDot, not a list.
        self.assertEqual(benchmark.header_imports("import Cloning.A Cloning.B\nimport Cloning.C\n"),
                         ["Cloning.A"])

    def test_unterminated_header_tokens_and_missing_import_names_fail(self):
        for text in ("/- missing end", "import «missing end", "module\nimport all\n"):
            with self.subTest(text=text), self.assertRaises(ValueError):
                benchmark.header_imports(text)


class InvalidationTests(unittest.TestCase):
    def test_only_exact_owned_modules_are_removed(self):
        with tempfile.TemporaryDirectory() as tmp:
            previous = benchmark.PROJECT
            benchmark.PROJECT = Path(tmp)
            try:
                names = [".lake/build/lib/lean/Cloning/A.olean",
                         ".lake/build/lib/lean/Cloning/A.olean.hash",
                         ".lake/build/ir/Cloning/A.c", ".lake/build/lib/lean/All.trace",
                         ".lake/build/lib/lean/Cloning/Another.olean",
                         ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"]
                for name in names:
                    p = Path(tmp) / name
                    p.parent.mkdir(parents=True, exist_ok=True)
                    p.write_text("sentinel")
                removed = benchmark.invalidate_owned(["Cloning.A", "All"])
                self.assertEqual(set(removed), set(names[:4]))
                for name in names[4:]:
                    self.assertEqual((Path(tmp) / name).read_text(), "sentinel")
            finally:
                benchmark.PROJECT = previous

    def test_symlinked_build_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            previous = benchmark.PROJECT
            benchmark.PROJECT = Path(tmp) / "project"
            try:
                (benchmark.PROJECT / ".lake").mkdir(parents=True)
                outside = Path(tmp) / "outside"
                outside.mkdir()
                (benchmark.PROJECT / ".lake/build").symlink_to(outside)
                with self.assertRaises(ValueError):
                    benchmark.invalidate_owned(["Cloning.A"])
            finally:
                benchmark.PROJECT = previous


if __name__ == "__main__":
    unittest.main()
