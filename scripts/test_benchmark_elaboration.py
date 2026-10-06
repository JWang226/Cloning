"""Safety checks for project-only benchmark invalidation."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("benchmark", Path(__file__).with_name("benchmark_elaboration.py"))
benchmark = importlib.util.module_from_spec(spec)
spec.loader.exec_module(benchmark)


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
