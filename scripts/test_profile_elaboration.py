"""Guard the real pinned Lean header envelope used for profile provenance."""
import copy
import unittest

from profile_elaboration import deps_json_imports, profiling_flags, validate_native_setup


RC6_HEADER = {"imports": [{"errors": [], "result": {
    "imports": [
        {"importAll": False, "isExported": True, "isMeta": False, "module": "Init"},
        {"importAll": False, "isExported": True, "isMeta": False,
         "module": "Cloning.HeisenbergDualContinuity"}],
    "isModule": False}}]}


class HeaderEnvelopeTests(unittest.TestCase):
    def test_native_setup_cannot_enable_profiler_through_saved_options(self):
        validate_native_setup({"options": {}})
        for options in ({"trace.profiler": True}, {"trace.profiler.output": "hidden.json"},
                        {"trace.profiler.output.pp": True}, []):
            with self.subTest(options=options), self.assertRaises(ValueError):
                validate_native_setup({"options": options})

    def test_trace_modes_preserve_default_flags_and_native_has_no_firefox_output(self):
        self.assertEqual(profiling_flags("firefox", "fixture.json"), [
            "--profile", "--stats", "-Dtrace.profiler=true", "-Dtrace.profiler.output.pp=true",
            "-Dtrace.profiler.output=fixture.json"])
        self.assertEqual(profiling_flags("native", "unused.json"), ["--profile", "--stats"])
        with self.assertRaises(ValueError):
            profiling_flags("guess", "unused.json")

    def test_real_rc6_result_preserves_import_names_and_modifiers(self):
        self.assertEqual(deps_json_imports(RC6_HEADER), RC6_HEADER["imports"][0]["result"]["imports"])

    def test_header_diagnostics_and_incomplete_results_are_rejected(self):
        diagnosed = copy.deepcopy(RC6_HEADER)
        diagnosed["imports"][0]["errors"] = [{"message": "invalid import"}]
        legacy_guess = {"imports": [{"errors": [], "result?": RC6_HEADER["imports"][0]["result"]}]}
        for data in (diagnosed, legacy_guess, {"imports": []}, {"imports": [None]}, None):
            with self.subTest(data=data), self.assertRaises(ValueError):
                deps_json_imports(data)

    def test_invalid_direct_import_cannot_become_an_artifact_path(self):
        for row in ({}, {"module": ""}, {"module": 7}, "Init"):
            data = copy.deepcopy(RC6_HEADER)
            data["imports"][0]["result"]["imports"] = [row]
            with self.subTest(row=row), self.assertRaises(ValueError):
                deps_json_imports(data)


if __name__ == "__main__":
    unittest.main()
