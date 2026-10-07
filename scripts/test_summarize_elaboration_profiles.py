"""Small native/Firefox fixtures; no Lean or real campaign traces are read."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from summarize_elaboration_profiles import parse_native_resources, profile_trace_mode, summarize


def fixture(directory, native=True):
    source = b"namespace Cloning\ntheorem pilot : True := by trivial\nend Cloning\n"
    (directory / "source.lean.txt").write_bytes(source)
    (directory / "run.log").write_text("elaboration of Cloning.pilot took 101ms\n"
        "number of imported modules: 3\nnumber of imported bytes: 1000\n"
        "cumulative profiling times:\n  elaboration 1.25s\n")
    (directory / "resources.txt").write_text("User time (seconds): 9.20\nSystem time (seconds): 1.80\n"
        "Elapsed (wall clock) time (h:mm:ss or m:ss): 0:06.00\nPercent of CPU this job got: 183%\n"
        "Maximum resident set size (kbytes): 4096\n")
    record = {"module": "Cloning.A", "source": "Cloning/A.lean", "source_snapshot": "source.lean.txt",
              "source_sha256": hashlib.sha256(source).hexdigest(), "log": "run.log", "resources": "resources.txt",
              "repetition": 1, "exit_code": 0, "measurement_valid": True, "command": ["lean", "--profile", "--stats"]}
    if native:
        record.update(trace_mode="native", events=None)
        data = b'{"options":{}}\n'
        (directory / "setup.json").write_bytes(data)
        record.update(setup_snapshot="setup.json", setup_sha256=hashlib.sha256(data).hexdigest())
    else:
        record["events"] = "events.json"
        (directory / "events.json").write_text('{"threads":[]}\n')
    (directory / "profiles.json").write_text(json.dumps([record]))
    return record


class ProfileSummaryTests(unittest.TestCase):
    def test_native_has_elapsed_timers_stats_and_gnu_cpu_without_firefox(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            original = fixture(directory)
            summary, paths = summarize(directory)
            row = summary["profiles"][0]
            self.assertEqual(row["profile"], original)
            self.assertIsNone(row["firefox_profile"])
            self.assertTrue(row["native_setup_trace_options_absent"])
            self.assertNotIn("events", row["input_sha256"])
            self.assertFalse(any(path.name == "events.json" for path in paths))
            self.assertEqual(row["text_profile"]["exclusive_phase_ms"], {"elaboration": 1250.0})
            self.assertEqual(row["environment_stats"]["imported_regions"], 3)
            self.assertEqual(row["native_resources"], {"wall": 6.0, "user": 9.2, "system": 1.8,
                "cpu": 11.0, "cpu_percent": "183%", "rss_kib": 4096.0})
            self.assertTrue(any("not matched" in warning for warning in row["warnings"]))

    def test_legacy_firefox_still_requires_real_recorded_events(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            original = fixture(directory, native=False)
            self.assertEqual(profile_trace_mode(original), "firefox")
            summary, _ = summarize(directory)
            self.assertIsInstance(summary["profiles"][0]["firefox_profile"], dict)
            self.assertIn("events", summary["profiles"][0]["input_sha256"])
            (directory / "events.json").unlink()
            with self.assertRaises(ValueError):
                summarize(directory)

    def test_native_cannot_be_inferred_from_missing_events_or_include_trace_flags(self):
        for record in ({"events": None}, {"trace_mode": "native", "events": "fake.json"},
                       {"trace_mode": "native", "events": None, "command": ["--profile", "--stats", "-Dtrace.profiler=true"]},
                       {"trace_mode": "unknown", "events": None}):
            with self.subTest(record=record), self.assertRaises(ValueError):
                profile_trace_mode(record)

    def test_native_captured_setup_options_are_checked_and_attempt_inputs_protected(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            original = fixture(directory)
            (directory / "setup.json").write_text('{"options":{"trace.profiler":true}}\n')
            original["setup_sha256"] = hashlib.sha256((directory / "setup.json").read_bytes()).hexdigest()
            (directory / "profiles.json").write_text(json.dumps([original]))
            with self.assertRaises(ValueError):
                summarize(directory)
            original = fixture(directory)
            (directory / "receipt.json").write_text(json.dumps([original]))
            (directory / "failed.log").write_text("failed trace attempt\n")
            failed = dict(original, log="failed.log", events="missing.json", trace_mode="firefox", exit_code=1, measurement_valid=False)
            (directory / "receipt.json").write_text(json.dumps([failed]))
            (directory / "profile-attempts.json").write_text(json.dumps({"schema":"cloning-elaboration-profile-attempts-v1",
                "attempts":[{"profile":failed,"original_index":"receipt.json","original_index_sha256":"a"*64,
                             "original_record_index":0,"input_prefix":"","reason":"preserved failure",
                             "evidence_role":"failed-profile-attempt","expected_missing_inputs":["events"]}]}))
            summary, paths = summarize(directory)
            self.assertIn((directory / "receipt.json").resolve(), paths)
            self.assertIn((directory / "failed.log").resolve(), paths)
            self.assertIn((directory / "setup.json").resolve(), paths)
            self.assertEqual(summary["profile_attempts"]["attempt_count"], 1)
            from unittest.mock import patch
            from summarize_elaboration_profiles import main
            for protected in ("receipt.json", "failed.log"):
                saved = (directory / protected).read_bytes()
                with patch("sys.argv", ["summarize", "--profiles", str(directory), "--output", str(directory / protected)]), self.assertRaises(SystemExit):
                    main()
                self.assertEqual((directory / protected).read_bytes(), saved)

    def test_native_resource_hours_units_and_invalid_numbers(self):
        self.assertEqual(parse_native_resources("Elapsed (wall clock) time (h:mm:ss or m:ss): 1:02:03.50\n")["wall"], 3723.5)
        for text in ("User time (seconds): nan\n", "User time (seconds): -1\n",
                     "User time (seconds): 1\nUser time (seconds): 2\n"):
            with self.subTest(text=text), self.assertRaises(ValueError):
                parse_native_resources(text)


if __name__ == "__main__":
    unittest.main()
