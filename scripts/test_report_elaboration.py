"""Synthetic checks for measurement units, provenance, and report safeguards."""
import copy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("elaboration_report", Path(__file__).with_name("report_elaboration.py"))
report = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = report
spec.loader.exec_module(report)


def fixture(directory):
    source = "import Mathlib\n/- namespace Fake -/\nnamespace Cloning.Scalar\ntheorem ok : True := by trivial\nend Cloning.Scalar\n"
    root = "import Cloning.A\n"
    sizes = [{"module": "All", "source": "formalization/All.lean", "lines": 1,
              "code_lines": 1, "module_header": False},
             {"module": "Cloning.A", "source": "formalization/Cloning/A.lean", "lines": 5,
              "code_lines": 4, "module_header": False}]
    resources = {"User time (seconds)": "10.00", "System time (seconds)": "2.00",
                 "Elapsed (wall clock) time (h:mm:ss or m:ss)": "0:06.00",
                 "Percent of CPU this job got": "200%",
                 "Maximum resident set size (kbytes)": "123456"}
    summary = {"schema": "cloning-elaboration-test-v1", "commit": "a" * 40,
               "start_utc": "2026-10-06T01:00:00+00:00", "end_utc": "2026-10-06T01:00:06+00:00",
               "command": ["/opt/homebrew/bin/gtime", "-v", "lake", "--no-ansi", "--no-cache", "build", "All"],
               "environment": {"LEAN_NUM_THREADS": "2", "LAKE_ARTIFACT_CACHE": "false"},
               "host": "test-host", "cpu_count": 8, "memory_bytes": "16000000000",
               "lean": "Lean 4.29.0-rc6", "lake": "Lake 5.0.0", "time_tool": "time (GNU Time) 1.10\n",
               "exit_code": 0, "wall_seconds_observed": 6.1, "resources": resources,
               "dependency_artifacts_unchanged": True, "upstream_compilations": [],
               "module_count": 2, "total_lines": 6, "code_lines": 5, "legacy_header_files": 2,
               "warnings": 0, "errors": 0, "sorry_messages": 0, "lake_jobs": 4563,
               "timings": [{"module": "Cloning.A", "seconds": 12.0}, {"module": "All", "seconds": .001}]}
    log = "✔ [4562/4563] Built Cloning.A (12s)\n✔ [4563/4563] Built All (1ms)\n"
    graph = {"All": ["Cloning.A"], "Cloning.A": []}
    sources = {"formalization/All.lean": root, "formalization/Cloning/A.lean": source}
    samples = [{"utc": summary["start_utc"], "processes": ["lean this-repo", "lean another-repo"]}]
    for name, content in [("summary.json", summary), ("size.json", sizes), ("imports.json", graph),
                          ("process-samples.json", samples)]:
        (directory / name).write_text(json.dumps(content))
    (directory / "skill-size.txt").write_text("comment-only files (excluded): 0\n")
    (directory / "build.log").write_text(log)
    return report.Snapshot(directory, summary, sizes, graph, log, samples, sources,
                           {"All": .001, "Cloning.A": 12.0}, {"All", "Cloning.A"},
                           report.resource_metrics(resources))


class ReportTests(unittest.TestCase):
    def test_elapsed_hours_minutes_and_fraction(self):
        self.assertEqual(report.elapsed_seconds("1:02:03.50"), 3723.5)
        self.assertEqual(report.elapsed_seconds("4:05.25"), 245.25)
        with self.assertRaises(ValueError):
            report.elapsed_seconds("1:2:3:4")

    def test_cpu_and_rss_keep_their_recorded_units(self):
        parsed = report.resource_metrics({"User time (seconds)": "9.2", "System time (seconds)": "1.8",
                                         "Maximum resident set size (kbytes)": "4096"})
        self.assertEqual(parsed["cpu"], 11)
        self.assertEqual(parsed["rss_kib"], 4096)
        self.assertIsNone(parsed["wall"])
        self.assertIsNone(report.resource_metrics({})["cpu"])

    def test_namespace_ignores_nested_comments_and_strings(self):
        source = '/- namespace Wrong /- namespace Nested -/ -/\n#eval "namespace String"\nnamespace Right.First\nnamespace Other\n'
        self.assertEqual(report.first_namespace(source), "Right.First")
        self.assertEqual(report.first_namespace('import All\n'), "(root / facade)")

    def test_timings_are_verified_against_raw_log_and_handle_ms(self):
        summary = {"timings": [{"module": "A", "seconds": .125}]}
        times, compiled = report.timing_rows(summary, "Built A (125ms)\nReplayed Mathlib.B\n", {"A"})
        self.assertEqual(times, {"A": .125})
        self.assertEqual(compiled, {"A"})
        with self.assertRaises(ValueError):
            report.timing_rows(summary, "Built A (126ms)", {"A"})
        with self.assertRaises(ValueError):
            report.timing_rows({"timings": summary["timings"] * 2}, "Built A (125ms)", {"A"})

    def test_weighted_chain_uses_dependency_path_not_total_work(self):
        seconds, chain = report.weighted_chain({"All": ["A", "B"], "A": ["C"], "B": [], "C": []},
                                               {"All": 1, "A": 2, "B": 6, "C": 3})
        self.assertEqual((seconds, chain), (7, ["B", "All"]))
        with self.assertRaises(ValueError):
            report.weighted_chain({"All": ["A"], "A": ["All"]}, {})

    def test_snapshot_reads_measured_archive_and_rejects_scope_drift(self):
        with tempfile.TemporaryDirectory() as tmp:
            current = fixture(Path(tmp))
            with patch.object(report, "archive_sources", return_value=current.sources) as archived:
                loaded = report.Snapshot.read(tmp)
            archived.assert_called_once_with("a" * 40, [x["source"] for x in current.sizes])
            self.assertEqual(loaded.groups()["Cloning.Scalar"]["seconds"], 12)
            broken = copy.deepcopy(current.summary)
            broken["code_lines"] += 1
            (Path(tmp) / "summary.json").write_text(json.dumps(broken))
            with self.assertRaisesRegex(ValueError, "source counts"):
                report.Snapshot.read(tmp)

    def test_render_has_all_sections_and_separates_cpu_elapsed_jobs(self):
        with tempfile.TemporaryDirectory() as tmp:
            current = fixture(Path(tmp))
            output = report.render(current)
            self.assertEqual(output.count("\n## "), 11)
            self.assertIn("GNU-time total CPU seconds | 12.00", output)
            self.assertIn("Logged elapsed job-duration sum seconds | 12.00", output)
            self.assertIn("not measured CPU", output)
            self.assertIn("Maximum process peak RSS (KiB) | 123,456.00", output)
            self.assertIn("zero files without a `module` header", output)
            self.assertIn("deliberately adapts", output)
            self.assertIn("Lake total jobs (includes cached upstream jobs) | 4563", output)
            self.assertIn("Unique owned modules actually compiled | 2", output)
            self.assertIn("LAKE_ARTIFACT_CACHE=false LEAN_NUM_THREADS=2", output)
            self.assertNotIn("\n+  --", output)

    def test_profiles_use_exclusive_elapsed_not_os_cpu(self):
        profiles = {"profiles": [{"profile": {"module": "A", "repetition": 1, "exit_code": 0,
                     "wall_seconds": 10, "command": ["lake", "env", "lean", "--profile", "A.lean"]},
                     "text_profile": {"exclusive_phase_ms": {"import": 6000, "simp": 1000},
                                      "events_over_threshold": []}, "warnings": []}]}
        output = report.profile_section(profiles)
        self.assertIn("exclusive **elapsed** times", output)
        self.assertIn("A | 1 | 0 | 10.00 | 7.00 | import", output)
        self.assertIn("simp | 1.000", output)

    def test_comparison_discloses_mismatch_without_assigning_cause(self):
        with tempfile.TemporaryDirectory() as tmp:
            current = fixture(Path(tmp))
            prior = copy.deepcopy(current)
            prior.summary["environment"]["LEAN_NUM_THREADS"] = "4"
            output = report.comparison(current, prior)
            self.assertIn("unmatched: avoid a wall-time speedup claim", output)
            self.assertIn("do not identify the cause", output)

    def test_process_census_attributes_only_explicit_absolute_sources(self):
        sample = [{"processes": [
            "100 00:10 0:01 10.0 lean /repo/formalization/A.lean -o /repo/A.olean",
            "101 00:11 0:02 20.0 lean /other/B.lean -o /other/B.olean",
            "102 00:12 0:03 30.0 lake build All"]}]
        census = report.process_census(sample, Path("/repo"))
        self.assertEqual(census["maxima"], {"owned_source": 1, "other_source": 1, "unresolved": 1})
        self.assertEqual(census["foreign_source_paths"], ["/other/B.lean"])
        self.assertEqual(census["samples_with_other_source"], 1)

    def test_archive_rejects_noncommit_and_escaping_paths(self):
        with self.assertRaises(ValueError):
            report.archive_sources("HEAD", [])
        with self.assertRaises(ValueError):
            report.archive_sources("a" * 40, ["formalization/../../secrets"])

    def test_main_refuses_to_overwrite_raw_measurement(self):
        with tempfile.TemporaryDirectory() as tmp:
            current = fixture(Path(tmp))
            sentinel = (Path(tmp) / "summary.json").read_bytes()
            with patch.object(report.Snapshot, "read", return_value=current), patch.object(sys, "argv", [
                    "report_elaboration.py", "--benchmark", tmp, "--output", str(Path(tmp) / "summary.json")]):
                with self.assertRaises(SystemExit) as stopped:
                    report.main()
            self.assertEqual(stopped.exception.code, 2)
            self.assertEqual((Path(tmp) / "summary.json").read_bytes(), sentinel)


if __name__ == "__main__":
    unittest.main()
