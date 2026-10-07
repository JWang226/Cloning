#!/usr/bin/env python3
"""Inspect an elaboration evidence bundle; --write builds it in a fresh directory.

No Lean commands are run. Inspection never hashes or parses large profile traces.
Writing, summary reconstruction, compression and extraction checks are explicit,
and must be scheduled by the caller outside timed Lean activity.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
from datetime import datetime, timezone
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile

BENCHMARK_FILES = (
    "summary.json", "size.json", "imports.json", "source-config-hashes.json",
    "source-config-stability.json", "skill-size.txt", "dependencies-before.json",
    "dependencies-after.json", "invalidated.json", "benchmark-runner.py",
    "resources.txt", "build.log",
)
REQUIRED_BENCHMARK_FILES = set(BENCHMARK_FILES) - {"source-config-stability.json"}
PROFILE_INPUT_KEYS = ("log", "events", "resources", "setup_snapshot", "trace_snapshot", "import_context")
BARE_INPUT_KEYS = tuple(key for key in PROFILE_INPUT_KEYS if key != "events")
INTERVENTION_RECORDS = ("profiles.json", "bare.json", "summary.json", "plan.json", "verdict.json",
                        "proof-vs-statement-diagnostic.json", "candidate.patch")
INTERVENTION_OPTIONAL_RECORDS = ("REPORT.md",)
ENVIRONMENT_KEYS = {"LEAN_NUM_THREADS", "LAKE_ARTIFACT_CACHE", "LAKE_NO_CACHE", "LEAN_GITHASH", "LANG", "LC_ALL"}
HELPERS = ("benchmark_elaboration.py", "profile_elaboration.py",
           "summarize_elaboration_profiles.py", "report_elaboration.py")
SKILL_PIN = "70bb859295edc2abb9ad81f8f6e31ab2adf8ca07"
SKILL_REPOSITORY = "https://github.com/scottnarmstrong/LeanAutoformalizationSkills"
SKILL_COPY_SOURCES = {
    "count_lean_lines.py": ("skills/lean-elaboration-test/scripts/count_lean_lines.py",
        "6690ea76cf6031fa082bf5b1f85f3606db19508df511d0bb8d934048fa583220"),
    "lean-elaboration-test.md": ("skills/lean-elaboration-test/SKILL.md",
        "ea9fa6123d8c3a5085d480eb7fa1f87e497c3bd5f5e7bfd9e4f4d0b8d12bd284"),
    "lean-elaboration.md": ("skills/lean-elaboration/SKILL.md",
        "f7a3ed0be7bfed0535122a11878b57331d59b464122158339ab9445a12beb608"),
    "evidence.md": ("skills/lean-elaboration/references/evidence.md",
        "065d9495d5f95a4770ec888d47ab763fced7be88f4385a83daadb2d011a500bc"),
    "LICENSE": ("LICENSE", "9ba9550ad48438d0836ddab3da480b3b69ffa0aac7b7878b5a0039e7ab429411"),
}
SKILLS = tuple(SKILL_COPY_SOURCES)
SKILL_ATTRIBUTION_FILES = ("provenance.json", "ATTRIBUTION.md")
PROFILE_AUX_FILES = ("aggregation.json", "native-exploratory/driver.py",
                     "native-guarded/profile-runner.py", "native-guarded/profile-runner-provenance.json",
                     "continuation/profile-runner.py", "continuation/profile-runner-provenance.json")
HASH = re.compile(r"[0-9a-f]{64}\Z")
COMMIT = re.compile(r"[0-9a-f]{40}\Z")
# URLs and Lean syntax are deliberately not interpreted as host file paths.
HOST_PATH = re.compile(r"/(?:Users|home|private|var|opt|Applications|Volumes|tmp|usr|Library|System)"
                       r"(?:/[A-Za-z0-9_@.+~=%-]+)+")
LABEL = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*\Z")


def json_bytes(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def file_digest(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def load_json(path):
    return json.loads(path.read_bytes())


def relative_name(name):
    """A strict cross-platform relative archive name."""
    if not isinstance(name, str) or not name or "\\" in name or "\x00" in name:
        raise ValueError("Invalid relative evidence name")
    parts = name.split("/")
    if any(part in {"", ".", ".."} for part in parts) or ":" in parts[0]:
        raise ValueError("Absolute, escaping, or ambiguous evidence name")
    if PurePosixPath(name).is_absolute():
        raise ValueError("Absolute evidence name")
    return name


def safe_file(directory, name):
    name = relative_name(name)
    base = directory.resolve()
    current = base
    for component in name.split("/"):
        current = current / component
        if current.is_symlink():
            raise ValueError("Symlink evidence input: " + name)
    if not current.is_file() or not current.resolve().is_relative_to(base):
        raise ValueError("Missing, special, or escaping evidence input: " + name)
    # Reject input hardlinks too: published evidence must have one identifiable input.
    if current.stat().st_nlink != 1:
        raise ValueError("Hardlinked evidence input: " + name)
    return current


def skill_provenance():
    """Pinned source digests were verified against upstream before publication."""
    return {
        "schema": "cloning-elaboration-external-skills-provenance-v1",
        "creator": {"name": "Scott Armstrong", "github": "scottnarmstrong",
                    "url": "https://github.com/scottnarmstrong"},
        "repository": SKILL_REPOSITORY, "commit": SKILL_PIN,
        "license": {"identifier": "CC-BY-4.0", "local_copy": "LICENSE",
                    "source_url": SKILL_REPOSITORY + "/blob/" + SKILL_PIN + "/LICENSE",
                    "canonical_url": "https://creativecommons.org/licenses/by/4.0/",
                    "sha256": SKILL_COPY_SOURCES["LICENSE"][1]},
        "copies": [{"original_path": original, "local_copy": name, "sha256": sha,
                    "source_url": SKILL_REPOSITORY + "/blob/" + SKILL_PIN + "/" + original,
                    "raw_source_url": "https://raw.githubusercontent.com/scottnarmstrong/LeanAutoformalizationSkills/"
                                      + SKILL_PIN + "/" + original,
                    "content_status": "unmodified", "content_modified": False,
                    "filename_renamed": PurePosixPath(original).name != name}
                   for name, (original, sha) in SKILL_COPY_SOURCES.items()],
        "notes": ["Saved contents were byte-compared with the pinned upstream raw sources during attribution preparation.",
                  "The two SKILL.md copies have descriptive local filenames; file contents are unmodified.",
                  "This is attribution and source provenance, not an endorsement or a benchmark result."],
    }


def skill_attribution_notice(provenance):
    rows = "\n".join(f"| [{row['original_path']}]({row['source_url']}) | `{row['local_copy']}` | Unmodified |"
                     for row in provenance["copies"])
    return f"""# External skill attribution

These files are by [Scott Armstrong (`scottnarmstrong`)](https://github.com/scottnarmstrong),
from [LeanAutoformalizationSkills]({SKILL_REPOSITORY}) at commit
`{SKILL_PIN}`. They are licensed under
[Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/).
The exact pinned [LICENSE](LICENSE) is preserved, including its warranty disclaimer;
the [upstream license]({provenance['license']['source_url']}) is linked for reference.

| Original source path | Local copy | Contents |
|---|---|---|
{rows}

All copied contents are unmodified and were compared byte-for-byte against the
pinned upstream sources. Only the two `SKILL.md` filenames were renamed for clarity.
`provenance.json` records the original paths, source/license links and SHA-256 values.
This notice and the provenance record were generated for this evidence bundle;
they do not imply endorsement by the original creator.
"""


def validate_skill_copies(campaign):
    directory = campaign / "skills"
    provenance = skill_provenance()
    for name, (_, expected) in SKILL_COPY_SOURCES.items():
        if file_digest(safe_file(directory, name)) != expected:
            raise ValueError("External skill copy differs from its pinned upstream digest: " + name)
    if load_json(safe_file(directory, "provenance.json")) != provenance:
        raise ValueError("External skill provenance differs from its pinned attribution mapping")
    if safe_file(directory, "ATTRIBUTION.md").read_bytes() != skill_attribution_notice(provenance).encode():
        raise ValueError("External skill attribution notice differs from its generated provenance")
    return provenance


def copy_skill_evidence(bundle, campaign):
    provenance = validate_skill_copies(campaign)
    for row in provenance["copies"]:
        bundle.add("skills/" + row["local_copy"], source=safe_file(campaign / "skills", row["local_copy"]),
                   provenance={"creator": "Scott Armstrong (scottnarmstrong)", "commit": SKILL_PIN,
                               "source_url": row["source_url"], "content_status": "unmodified",
                               "license": "CC-BY-4.0"}, purpose="pinned external skill or license")
    for name in SKILL_ATTRIBUTION_FILES:
        bundle.add("skills/" + name, source=safe_file(campaign / "skills", name), role="derived",
                   purpose="generated external skill attribution and pinned source provenance")


def load_tool(repo, name):
    path = safe_file(repo / "scripts", name + ".py")
    spec = importlib.util.spec_from_file_location("bundle_" + name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def parse_assignment(value):
    if "=" not in value:
        raise ValueError("Expected NAME=VALUE")
    return value.split("=", 1)


def source_bytes(repo, directory, record):
    """Never substitute the current working source for a measured source."""
    expected = record.get("source_sha256", "")
    if not HASH.fullmatch(expected):
        raise ValueError("Missing profile source SHA-256")
    source = relative_name(record["source"])
    source = source if source.startswith("formalization/") else "formalization/" + source
    if not source.endswith(".lean") or not source.startswith("formalization/"):
        raise ValueError("Invalid owned profile source")
    if record.get("source_snapshot"):
        data = safe_file(directory, record["source_snapshot"]).read_bytes()
        if digest(data) != expected:
            raise ValueError("Preserved variant source hash differs")
        return data, {"origin": "preserved-profile-source", "source": source}
    for commit in dict.fromkeys((record.get("commit"), record.get("benchmark_commit"))):
        if not commit or not COMMIT.fullmatch(commit):
            continue
        result = subprocess.run(["git", "show", f"{commit}:{source}"], cwd=repo,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if result.returncode == 0 and digest(result.stdout) == expected:
            return result.stdout, {"origin": "measured-git-blob", "commit": commit, "source": source}
    raise ValueError("Profile source matches neither a preserved snapshot nor its Git commits")


def derived_record(record, source_snapshot, original_index_hash, position):
    result = deepcopy(record)
    removed = []
    for location, environment in (("environment", result.get("environment")),
                                  ("toolchain.environment", result.get("toolchain", {}).get("environment"))):
        if isinstance(environment, dict):
            for key in list(environment):
                if key not in ENVIRONMENT_KEYS:
                    removed.append(location + "." + key)
                    del environment[key]
    result["source_snapshot"] = source_snapshot
    result["publication"] = {
        "original_index_sha256": original_index_hash, "original_record_index": position,
        "transformations": [
            "Preserved an identical source snapshot bound to source_sha256.",
            "Removed inherited path-valued environment fields; exact task setup/import paths remain."
        ],
        "omitted_environment_fields": sorted(removed),
    }
    return result


def receipt_identity(record):
    module, arm, mode, repetition = (record.get(key) for key in ("module", "arm", "mode", "repetition"))
    if (not isinstance(module, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", module)
            or not isinstance(arm, str) or not LABEL.fullmatch(arm)
            or mode not in {"profile", "bare"} or type(repetition) is not int or repetition < 1):
        raise ValueError("Invalid intervention module/arm/mode/repetition identity")
    return module, arm, mode, repetition


def receipt_label(record):
    _, arm, mode, repetition = receipt_identity(record)
    return f"{arm}-{repetition}-{mode}"


def receipt_role(record):
    if record["arm"] == "diagnostic":
        return "diagnostic-sorry-outside-production"
    if record["arm"] == "A":
        return "baseline-control-" + record["mode"]
    return "candidate-" + record["mode"]


def profile_input_keys(record):
    mode = record.get("trace_mode", "firefox")
    if mode not in {"firefox", "native"}:
        raise ValueError("Unknown profile trace mode")
    if mode == "native":
        command = record.get("command", [])
        if ("events" not in record or record["events"] is not None
                or "--profile" not in command or "--stats" not in command
                or any(token.startswith("-Dtrace.profiler") for token in command)):
            raise ValueError("Native profile must have explicit null events and no Firefox flags")
        return BARE_INPUT_KEYS
    if not isinstance(record.get("events"), str) or not record["events"]:
        raise ValueError("Firefox profile requires recorded events")
    return PROFILE_INPUT_KEYS


def rebase_record(record, prefix):
    public = deepcopy(record)
    if prefix:
        relative_name(prefix)
    for key in (*PROFILE_INPUT_KEYS, "source_snapshot"):
        if public.get(key):
            name = relative_name(public[key])
            public[key] = prefix + "/" + name if prefix else name
    return public


def record_projection(record):
    projected = deepcopy(record)
    # Publication inserts an identical source copy; its content is independently SHA-bound.
    for key in ("receipt_origin", "publication", "source_snapshot"):
        projected.pop(key, None)
    return projected


def checked_origin(directory, origin):
    name = relative_name(origin["index"])
    prefix = origin.get("input_prefix", "")
    if prefix and relative_name(prefix) != prefix:
        raise ValueError("Invalid origin input prefix")
    parent = str(PurePosixPath(name).parent)
    if prefix != ("" if parent == "." else parent):
        raise ValueError("Receipt input prefix differs from its original index directory")
    original = safe_file(directory, name)
    public_form = origin.get("binding_form") == "derived-public-index"
    expected = origin.get("public_index_sha256") if public_form else origin.get("sha256")
    if not HASH.fullmatch(expected or "") or file_digest(original) != expected:
        raise ValueError("Receipt origin index SHA-256 differs")
    if public_form and not HASH.fullmatch(origin.get("original_index_sha256", "")):
        raise ValueError("Public origin lacks its historical original-index SHA-256")
    records = load_json(original)
    position = origin["record_index"]
    if (not isinstance(records, list) or type(position) is not int or not 0 <= position < len(records)
            or not isinstance(records[position], dict)):
        raise ValueError("Receipt origin position is outside its index")
    return records[position], original, public_form


def validate_profile_origins(directory, records):
    if not any(record.get("receipt_origin") for record in records):
        return {}
    originals = {}
    for record in records:
        origin = record.get("receipt_origin")
        if not isinstance(origin, dict):
            raise ValueError("Derived aggregate requires an origin for every completed receipt")
        raw, path, public_form = checked_origin(directory, origin)
        expected = rebase_record(raw, origin["input_prefix"])
        if public_form:
            if record_projection(record) != record_projection(expected):
                raise ValueError("Public aggregate differs from its redacted/rebased origin projection")
        else:
            actual = deepcopy(record)
            del actual["receipt_origin"]
            if actual != expected:
                raise ValueError("Aggregate receipt differs from its unchanged original record")
        previous = originals.setdefault(origin["index"], path)
        if previous != path:
            raise ValueError("Conflicting receipt origin indexes")
    return originals


def validate_profile_attempts(repo, directory, snapshot=None):
    path = directory / "profile-attempts.json"
    if not path.exists():
        return []
    raw = load_json(safe_file(directory, "profile-attempts.json"))
    if (raw.get("schema") != "cloning-elaboration-profile-attempts-v1"
            or not isinstance(raw.get("attempts"), list) or not raw["attempts"]):
        raise ValueError("Invalid diagnostic profile-attempt index")
    seen = set()
    for attempt in raw["attempts"]:
        origin = {"index": attempt["original_index"], "sha256": attempt["original_index_sha256"],
                  "record_index": attempt["original_record_index"], "input_prefix": attempt["input_prefix"]}
        if attempt.get("binding_form") == "derived-public-index":
            origin.update(binding_form="derived-public-index",
                          original_index_sha256=attempt["original_index_sha256"],
                          public_index_sha256=attempt["public_index_sha256"])
        original, _, public_form = checked_origin(directory, origin)
        identity = (origin["index"], origin["record_index"])
        expected = rebase_record(original, origin["input_prefix"]) if public_form else original
        identical = (record_projection(expected) == record_projection(attempt["profile"])) if public_form else expected == attempt["profile"]
        if identity in seen or not identical:
            raise ValueError("Diagnostic receipt duplicates or differs from its original index record")
        seen.add(identity)
        role = attempt["evidence_role"]
        if (role not in {"failed-profile-attempt", "diagnostic-native-control"}
                or not isinstance(attempt.get("reason"), str) or not attempt["reason"].strip()):
            raise ValueError("Diagnostic receipt requires an explicit role and reason")
        if role == "failed-profile-attempt" and original.get("exit_code") == 0 and original.get("measurement_valid") is True:
            raise ValueError("A successful valid receipt cannot be relabeled as a failed attempt")
        if role == "diagnostic-native-control" and original.get("trace_mode") != "native":
            raise ValueError("Exploratory native diagnostic must record native trace mode")
        record = attempt["profile"] if public_form else rebase_record(original, origin["input_prefix"])
        required = profile_input_keys(record)
        missing = []
        for key in required:
            name = record.get(key)
            if key == "events" and name and not (directory / name).exists():
                relative_name(name)
                current = directory
                for component in name.split("/"):
                    current = current / component
                    if current.is_symlink():
                        raise ValueError("Symlink in expected missing diagnostic input")
                missing.append(key)
            else:
                safe_file(directory, name or "")
        if attempt.get("expected_missing_inputs") != missing or any(key != "events" for key in missing):
            raise ValueError("Diagnostic missing inputs differ from the explicit expected events absence")
        data, _ = source_bytes(repo, directory, record)
        if snapshot is not None:
            source = record["source"]
            source = source if source.startswith("formalization/") else "formalization/" + source
            owned = {row["module"]: row["source"] for row in snapshot.sizes}
            if (owned.get(record["module"]) != source
                    or record.get("benchmark_commit") != snapshot.summary["commit"]
                    or record.get("config_sha256") != snapshot.provenance["config_sha256"]
                    or digest(snapshot.sources[source].encode()) != digest(data)):
                raise ValueError("Diagnostic attempt differs from its measured production source/config")
    return raw["attempts"]


def validate_profile_aux(directory, attempts):
    for name in PROFILE_AUX_FILES:
        if (directory / name).exists():
            safe_file(directory, name)
    for prefix in ("native-guarded", "continuation"):
        record_path = directory / prefix / "profile-runner-provenance.json"
        if record_path.exists():
            provenance = load_json(safe_file(directory, prefix + "/profile-runner-provenance.json"))
            if file_digest(safe_file(directory, prefix + "/profile-runner.py")) != provenance.get("sha256"):
                raise ValueError("Saved profile runner differs from its recorded provenance")
    for attempt in attempts:
        sha = attempt["profile"].get("native_control_driver_sha256")
        if sha:
            name = attempt["input_prefix"] + "/driver.py" if attempt["input_prefix"] else "driver.py"
            if file_digest(safe_file(directory, name)) != sha:
                raise ValueError("Exploratory native driver differs from its recorded digest")


def validate_original_profiles(directory, summary, intervention=False):
    index = load_json(safe_file(directory, "profiles.json"))
    rows = summary.get("profiles", [])
    if (summary.get("schema") != "cloning-elaboration-profile-summary-v1"
            or summary.get("profile_count") != len(rows)
            or not rows or [row.get("profile") for row in rows] != index):
        raise ValueError("Profile index and completed summary differ")
    identities = ([receipt_identity(record) for record in index] if intervention else
                  [(record.get("module"), record.get("repetition")) for record in index])
    if len(set(identities)) != len(identities):
        raise ValueError("Duplicate profile module/repetition")
    if any(type(record.get("repetition")) is not int or record["repetition"] < 1 for record in index):
        raise ValueError("Missing or invalid profile repetition")
    for record in index:
        if intervention and record["mode"] != "profile":
            raise ValueError("Bare receipt supplied as a trace profile")
        if record.get("measurement_valid") is not True or record.get("exit_code") != 0:
            raise ValueError("Invalid or unfinished profile")
        for key in profile_input_keys(record):
            safe_file(directory, record.get(key, ""))
        if record.get("trace_mode") == "native":
            options = load_json(safe_file(directory, record["setup_snapshot"])).get("options", {})
            if not isinstance(options, dict) or any(key.startswith("trace.profiler") for key in options):
                raise ValueError("Native captured setup contains profiler options")
        if record.get("source_snapshot"):
            safe_file(directory, record["source_snapshot"])
    validate_profile_origins(directory, index)
    return index


def expectation_check(index, expected, required=False):
    if expected is None:
        if required:
            raise ValueError("--write requires an explicit --expect module list for every profile set")
        return False
    planned = []
    for token in expected:
        parts = token.rsplit("@", 1)
        module = parts[0]
        repetition = int(parts[1]) if len(parts) == 2 and parts[1].isdigit() else 1
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", module) or repetition < 1:
            raise ValueError("Invalid expected MODULE@REPETITION")
        if len(parts) == 2 and not parts[1].isdigit():
            raise ValueError("Invalid expected repetition")
        planned.append((module, repetition))
    if not planned or len(set(planned)) != len(planned):
        raise ValueError("Expected module/repetition pairs must be nonempty and unique")
    actual = {(record["module"], record["repetition"]) for record in index}
    if actual != set(planned):
        raise ValueError("Completed module/repetition set differs from the explicitly planned set")
    return True


def intervention_expectation(index, expected, required=False):
    if expected is None:
        if required:
            raise ValueError("--write requires --expect-intervention for each receipt set")
        return False
    labels = [receipt_label(record) for record in index]
    if len(set(labels)) != len(labels):
        raise ValueError("Intervention receipt labels collide across modules")
    if (not expected or len(set(expected)) != len(expected)
            or any(not re.fullmatch(r"[A-Za-z0-9._-]+-[1-9][0-9]*-(profile|bare)", token)
                   for token in expected) or set(labels) != set(expected)):
        raise ValueError("Intervention receipts differ from the exact expected label plan")
    return True


def canonical_plan_label(token):
    # Current campaign drivers record diagnostic-profile and A1-profile.
    if token == "diagnostic-profile":
        return "diagnostic-1-profile"
    match = re.fullmatch(r"([AB])([1-9][0-9]*)-(profile|bare)", token)
    if match:
        return f"{match[1]}-{match[2]}-{match[3]}"
    if re.fullmatch(r"[A-Za-z0-9._-]+-[1-9][0-9]*-(profile|bare)", token):
        return token
    raise ValueError("Unrecognized intervention plan order label")


def scrub_environment_fields(value, prefix=""):
    public, removed = deepcopy(value), []
    def walk(node, path):
        if isinstance(node, dict):
            for key, entry in node.items():
                label = path + "." + key if path else key
                if key == "environment" and isinstance(entry, dict):
                    for name in list(entry):
                        if name not in ENVIRONMENT_KEYS:
                            del entry[name]
                            removed.append(label + "." + name)
                else:
                    walk(entry, label)
        elif isinstance(node, list):
            for i, entry in enumerate(node):
                walk(entry, path + f"[{i}]")
    walk(public, prefix)
    return public, sorted(removed)


def validate_intervention(repo, directory, expected, driver, snapshots, strict=False):
    """Small-record gate only; no trace parsing/compression or raw-log hashing."""
    plan = load_json(safe_file(directory, "plan.json"))
    verdict = load_json(safe_file(directory, "verdict.json"))
    summary = load_json(safe_file(directory, "summary.json"))
    profiles = validate_original_profiles(directory, summary, intervention=True)
    bare = load_json(safe_file(directory, "bare.json"))
    if not isinstance(bare, list) or not bare:
        raise ValueError("Completed bare control receipts are required")
    index = profiles + bare
    identities = [receipt_identity(record) for record in index]
    if len(set(identities)) != len(identities) or len({r["module"] for r in index}) != 1:
        raise ValueError("Intervention identities duplicate or span multiple owned modules")
    intervention_expectation(index, expected, strict)
    if not isinstance(plan.get("schema"), str) or not plan["schema"].endswith("-ab-plan-v1"):
        raise ValueError("Unexpected intervention plan schema")
    if not isinstance(verdict.get("schema"), str) or not verdict["schema"].endswith("-ab-verdict-v1"):
        raise ValueError("Unexpected intervention verdict schema")
    if verdict.get("decision") not in {"accept", "reject", "inconclusive"}:
        raise ValueError("Intervention must preserve an explicit acceptance/rejection verdict")
    order = [canonical_plan_label(token) for token in plan["order"]]
    for record in index:
        start, end = (datetime.fromisoformat(record[key]) for key in ("start_utc", "end_utc"))
        if start.utcoffset() is None or end.utcoffset() is None or end < start:
            raise ValueError("Invalid intervention UTC interval")
    chronology = sorted(index, key=lambda row: datetime.fromisoformat(row["start_utc"]))
    if any(datetime.fromisoformat(current["start_utc"]) < datetime.fromisoformat(previous["end_utc"])
           for previous, current in zip(chronology, chronology[1:])):
        raise ValueError("Intervention runs overlap; serial timing evidence is required")
    if order != [receipt_label(record) for record in chronology]:
        raise ValueError("Completed intervention order differs from its recorded plan")
    if driver is None:
        raise ValueError("Supply --intervention-driver matching plan.script_sha256")
    if driver.is_symlink() or not driver.is_file() or driver.stat().st_nlink != 1:
        raise ValueError("Unsafe intervention driver")
    if file_digest(driver) != plan.get("script_sha256"):
        raise ValueError("Intervention driver differs from the recorded script SHA-256")
    matched = [snapshot for snapshot in snapshots.values()
               if snapshot.summary["commit"] == plan.get("benchmark_commit")]
    if not matched or plan.get("config_sha256") != matched[0].provenance["config_sha256"]:
        raise ValueError("Intervention plan does not bind to a supplied benchmark/config")
    snapshot = matched[0]
    owned = {row["module"]: row["source"] for row in snapshot.sizes}
    if verdict.get("source_commit") != plan["benchmark_commit"]:
        raise ValueError("Intervention verdict benchmark differs")
    guards = ("inputs_stable", "measurement_valid", "source_hash_unchanged",
              "config_hashes_unchanged", "import_artifacts_unchanged",
              "build_setup_unchanged", "build_trace_unchanged", "tracked_source_unchanged")
    command_controls = {}
    for record in index:
        identity = receipt_identity(record)
        source = relative_name(record["source"])
        source = source if source.startswith("formalization/") else "formalization/" + source
        if (owned.get(identity[0]) != source or record.get("benchmark_commit") != plan["benchmark_commit"]
                or record.get("config_sha256") != plan["config_sha256"]
                or record.get("config_matches_benchmark") is not True or record.get("exit_code") != 0
                or any(record.get(key) is not True for key in guards)):
            raise ValueError("Invalid or unstable intervention source/config/input receipt")
        if (record["source_sha256"] != plan["variant_sha256"].get(record["arm"])
                or record["setup_sha256"] != plan.get("setup_sha256")
                or record["trace_sha256"] != plan.get("build_trace_sha256")):
            raise ValueError("Intervention source/setup/build trace differs from its plan")
        data, _ = source_bytes(repo, directory, record)
        if record.get("source_matches_benchmark") is True:
            if digest(snapshot.sources[source].encode()) != digest(data):
                raise ValueError("Intervention benchmark-match flag contradicts its source")
        keys = PROFILE_INPUT_KEYS if record["mode"] == "profile" else BARE_INPUT_KEYS
        for key in keys:
            safe_file(directory, record[key])
        if record["mode"] == "bare" and record.get("events"):
            raise ValueError("Bare control must not have fabricated trace events")
        command = record["command"]
        if record["mode"] == "bare" and any(
                token in {"--profile", "--stats"} or token.startswith("-Dtrace.profiler")
                for token in command):
            raise ValueError("Bare control command contains profiler/statistics instrumentation")
        if record["arm"] != "diagnostic":
            # Ignore output filenames only; source entry/setup/thread/options remain matched.
            normalized, i = [], 0
            while i < len(command):
                if command[i] == "-o" and i + 1 < len(command):
                    i += 2
                elif command[i].startswith("-Dtrace.profiler.output="):
                    i += 1
                else:
                    normalized.append(command[i])
                    i += 1
            prior = command_controls.setdefault(record["mode"], normalized)
            if prior != normalized:
                raise ValueError("A/B command controls differ within a measurement mode")
    if any(record["mode"] != "bare" for record in bare):
        raise ValueError("Traced receipt supplied as a bare control")
    for name in INTERVENTION_RECORDS:
        safe_file(directory, name)
    for name in INTERVENTION_OPTIONAL_RECORDS:
        if (directory / name).exists():
            safe_file(directory, name)
    return {"plan": plan, "verdict": verdict, "summary": summary,
            "profiles": profiles, "bare": bare, "chronology": chronology,
            "driver": driver, "decision": verdict["decision"]}


def validate_api_source_guard(repo, guard_path, driver, snapshots, interventions):
    """Validate a saved source/API receipt; do not rerun its source checker."""
    guard_path = safe_file(guard_path.parent, guard_path.name)
    driver = safe_file(driver.parent, driver.name)
    guard = load_json(guard_path)
    if guard.get("schema") != "cloning-elaboration-cleanup-api-source-guard-v1":
        raise ValueError("Unexpected source/API guard schema")
    matched = [snapshot for snapshot in snapshots.values()
               if snapshot.summary["commit"] == guard.get("baseline_commit")]
    if not matched or not COMMIT.fullmatch(guard.get("current_commit", "")):
        raise ValueError("Source/API guard does not bind to a supplied baseline")
    snapshot = matched[0]
    changes = guard.get("proof_only_changes")
    if (not isinstance(changes, list) or not changes
            or guard.get("owned_sources_checked") != len(snapshot.sizes)
            or guard.get("unchanged_owned_sources") != len(snapshot.sizes) - len(changes)
            or guard.get("public_check_commands_byte_identical") is not True
            or type(guard.get("public_check_count")) is not int or guard["public_check_count"] < 1
            or not HASH.fullmatch(guard.get("public_check_inventory_sha256", ""))):
        raise ValueError("Incomplete or inconsistent source/API guard scope")
    configs = guard.get("configuration", {})
    if set(configs) != set(snapshot.provenance["config_sha256"]):
        raise ValueError("Source/API guard configuration scope differs")
    for source, expected in snapshot.provenance["config_sha256"].items():
        if (configs[source].get("sha256") != expected
                or configs[source].get("byte_identical_to_baseline") is not True):
            raise ValueError("Source/API guard configuration differs from its baseline")
    candidates = {}
    for label, directory in interventions.items():
        verdict = load_json(safe_file(directory, "verdict.json"))
        if verdict.get("decision") != "accept":
            continue
        for record in load_json(safe_file(directory, "bare.json")):
            if record.get("arm") != "B":
                continue
            source = record["source"]
            source = source if source.startswith("formalization/") else "formalization/" + source
            data, _ = source_bytes(repo, directory, record)
            sha = digest(data)
            prior = candidates.setdefault(source, (sha, label))
            if prior != (sha, label):
                raise ValueError("Accepted source/API candidate receipts disagree")
    owned = {row["source"] for row in snapshot.sizes}
    seen = set()
    for change in changes:
        source = relative_name(change["source"])
        if (source not in owned or source in seen or not change.get("theorem")
                or change.get("statement_byte_identical") is not True
                or change.get("source_outside_body_byte_identical") is not True
                or any(not HASH.fullmatch(change.get(key, "")) for key in
                    ("source_before_sha256", "source_after_sha256", "outside_body_sha256", "signature_sha256"))):
            raise ValueError("Invalid source/API proof-body receipt")
        seen.add(source)
        if digest(snapshot.sources[source].encode()) != change["source_before_sha256"]:
            raise ValueError("Source/API original bytes differ from the measured baseline")
        if source not in candidates or candidates[source][0] != change["source_after_sha256"]:
            raise ValueError("Source/API candidate bytes lack a matching accepted intervention")
    if seen != set(candidates):
        raise ValueError("Source/API proof changes differ from accepted intervention scope")
    recorded_driver_hash = guard.get("driver_sha256")
    actual_driver_hash = file_digest(driver)
    if recorded_driver_hash is not None and recorded_driver_hash != actual_driver_hash:
        raise ValueError("Source/API driver differs from its recorded digest")
    return {"guard": guard, "guard_path": guard_path, "driver": driver,
            "guard_sha256": file_digest(guard_path), "driver_sha256": actual_driver_hash,
            "driver_digest_recorded_at_guard_run": recorded_driver_hash is not None,
            "candidate_interventions": {source: label for source, (_, label) in candidates.items()}}


def copy_api_source_guard(bundle, evidence):
    prefix = "source-api-guard"
    bundle.add(prefix + "/cleanup-api-source-guard.json", source=evidence["guard_path"],
               purpose="original source/API guard; not an independent proof verification")
    bundle.add(prefix + "/driver.py", source=evidence["driver"],
               purpose="source/API guard driver; digest captured at publication",
               provenance={"original_name": evidence["driver"].name,
                           "sha256_capture": "publication-time",
                           "original_sha256": evidence["driver_sha256"]})
    guard = evidence["guard"]
    bundle.add(prefix + "/receipt.json", data=json_bytes({
        "schema": "cloning-elaboration-source-api-guard-publication-v1",
        "evidence_role": "source-api-guard-not-independent-proof-verification",
        "original_guard_sha256": evidence["guard_sha256"],
        "driver_sha256": evidence["driver_sha256"], "driver_sha256_capture": "publication-time",
        "driver_digest_recorded_at_guard_run": evidence["driver_digest_recorded_at_guard_run"],
        "baseline_commit": guard["baseline_commit"], "historical_current_commit": guard["current_commit"],
        "candidate_interventions": evidence["candidate_interventions"],
        "notes": ["The original guard and its historical Git context are preserved without modification.",
                  "Candidate source hashes bind to preserved accepted intervention snapshots, including dirty working sources.",
                  "Historical current_commit is context, not a claim that every candidate source was committed then.",
                  "The driver digest is measured during publication; an absent original driver digest supplies no run-time attestation.",
                  "This receipt validates saved source/API bindings and does not replace the full build and axiom checks.",
                  "The bundler does not rerun the source/API checker or recompute signature, outside-body or public-check inventory digests."]}),
        role="derived", purpose="source/API supplemental role and honest provenance")


def inspect_campaign(repo, campaign, stages, expectations, extra_sets, strict=False,
                     interventions=None, intervention_expectations=None, intervention_drivers=None,
                     api_source_guard=None):
    report = load_tool(repo, "report_elaboration")
    result, snapshots = {"schema": "cloning-evidence-bundle-inspection-v1", "sets": []}, {}
    for stage in stages:
        row = {"name": stage, "ready": False}
        benchmark, profiles = campaign / stage, campaign / ("profiles-" + stage)
        missing = [stage + "/" + name for name in REQUIRED_BENCHMARK_FILES
                   if not (benchmark / name).is_file()]
        missing += ["profiles-" + stage + "/" + name for name in ("profiles.json", "summary.json")
                    if not (profiles / name).is_file()]
        if not ((benchmark / "process-samples.json").is_file()
                or (benchmark / "process-inventory.json").is_file()):
            missing.append(stage + "/process inventory")
        row["missing_records"] = sorted(missing)
        try:
            if missing:
                raise ValueError("Completed benchmark and profile records are still missing")
            if benchmark.is_symlink() or profiles.is_symlink():
                raise ValueError("Symlink campaign stage directory")
            for name in BENCHMARK_FILES:
                if (benchmark / name).exists():
                    safe_file(benchmark, name)
            for name in ("process-samples.json", "process-inventory.json"):
                if (benchmark / name).exists():
                    safe_file(benchmark, name)
            snapshot = report.Snapshot.read(benchmark)
            summary = load_json(safe_file(profiles, "summary.json"))
            index = validate_original_profiles(profiles, summary)
            report.require_complete_measurement(snapshot, report.derive_native_setup_guards(summary, profiles))
            attempts = validate_profile_attempts(repo, profiles, snapshot)
            validate_profile_aux(profiles, attempts)
            planned = expectation_check(index, expectations.get(stage), strict)
            row.update(ready=True, measured_commit=snapshot.summary["commit"],
                       modules=snapshot.summary["module_count"], profiles=len(index),
                       profile_modules=sorted({record["module"] for record in index}),
                       explicit_plan_checked=planned,
                       detailed_input_bytes=sum(safe_file(profiles, record[key]).stat().st_size
                           for record in index for key in profile_input_keys(record)),
                       diagnostic_attempts=len(attempts),
                       native_profiles=sum(record.get("trace_mode") == "native" for record in index))
            snapshots[stage] = snapshot
        except (ValueError, OSError, KeyError, TypeError, subprocess.CalledProcessError) as error:
            # Never print raw process/metadata contents or a foreign-path offending value.
            row["reason"] = type(error).__name__ + ": " + str(error)
            if strict:
                raise
        result["sets"].append(row)
    for name, directory in extra_sets.items():
        row = {"name": name, "ready": False}
        try:
            summary = load_json(safe_file(directory, "summary.json"))
            index = validate_original_profiles(directory, summary)
            expectation_check(index, expectations.get(name), strict)
            for record in index:
                matched = [s for s in snapshots.values()
                           if s.summary["commit"] == record.get("benchmark_commit")]
                if not matched or record.get("config_sha256") != matched[0].provenance["config_sha256"]:
                    raise ValueError("Supplemental profiles do not match a supplied benchmark/config")
                owned = {r["module"]: r["source"] for r in matched[0].sizes}
                source = record["source"]
                source = source if source.startswith("formalization/") else "formalization/" + source
                if owned.get(record["module"]) != source:
                    raise ValueError("Supplemental source is outside its recorded benchmark scope")
                # Variants need not equal the benchmark source, but must be preserved/hash-bound.
                source_bytes(repo, directory, record)
            row.update(ready=True, profiles=len(index),
                       profile_modules=sorted({record["module"] for record in index}),
                       explicit_plan_checked=name in expectations)
        except (ValueError, OSError, KeyError, TypeError, subprocess.CalledProcessError) as error:
            row["reason"] = type(error).__name__ + ": " + str(error)
            if strict:
                raise
        result["sets"].append(row)
    for label, directory in (interventions or {}).items():
        row = {"name": "interventions/" + label, "kind": "intervention", "ready": False}
        try:
            evidence = validate_intervention(repo, directory,
                (intervention_expectations or {}).get(label),
                (intervention_drivers or {}).get(label), snapshots, strict)
            row.update(ready=True, decision=evidence["decision"],
                       profile_records=len(evidence["profiles"]), bare_records=len(evidence["bare"]),
                       receipts=[receipt_label(record) for record in evidence["chronology"]],
                       explicit_plan_checked=label in (intervention_expectations or {}))
        except (ValueError, OSError, KeyError, TypeError, subprocess.CalledProcessError) as error:
            row["reason"] = type(error).__name__ + ": " + str(error)
            if strict:
                raise
        result["sets"].append(row)
    if api_source_guard is not None:
        row = {"name": "source-api-guard", "kind": "source-api-guard", "ready": False}
        try:
            evidence = validate_api_source_guard(repo, *api_source_guard, snapshots, interventions or {})
            row.update(ready=True, evidence_role="source-api-guard-not-independent-proof-verification",
                       original_guard_sha256=evidence["guard_sha256"],
                       driver_sha256=evidence["driver_sha256"], driver_sha256_capture="publication-time",
                       driver_digest_recorded_at_guard_run=evidence["driver_digest_recorded_at_guard_run"],
                       proof_body_changes=len(evidence["guard"]["proof_only_changes"]))
        except (ValueError, OSError, KeyError, TypeError, subprocess.CalledProcessError) as error:
            row["reason"] = type(error).__name__ + ": " + str(error)
            if strict:
                raise
        result["sets"].append(row)
    row = {"name": "external-skills", "kind": "attribution", "ready": False}
    try:
        provenance = validate_skill_copies(campaign)
        row.update(ready=True, source_commit=provenance["commit"], license=provenance["license"]["identifier"],
                   copied_files=len(provenance["copies"]), contents_unmodified=True)
    except (ValueError, OSError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        row["reason"] = type(error).__name__ + ": " + str(error)
        if strict:
            raise
    result["sets"].append(row)
    result["ready"] = bool(result["sets"]) and all(row["ready"] for row in result["sets"])
    result["inspection_only"] = not strict
    result["note"] = ("This completion inspection did not parse, compress or hash large traces. Writing requires explicit plans "
                      "and repeats validation, source/raw hashes, content screening and extraction checks.")
    return result, report


def approved_paths(repo, campaign, index, directory):
    roots = {str(repo.resolve()), str(campaign.resolve()), str(directory.resolve())}
    exact = set()
    for record in index:
        for value in record.get("command", []):
            if isinstance(value, str) and value.startswith("/"):
                exact.add(value)
        toolchain = record.get("toolchain", {})
        for key in ("lean_binary", "lean_libdir"):
            value = toolchain.get(key)
            if isinstance(value, str) and value.startswith("/"):
                exact.add(value)
                if key == "lean_libdir":
                    roots.add(value.rstrip("/"))
        for key in ("setup_snapshot", "import_context"):
            value = load_json(safe_file(directory, record[key]))
            def collect(node):
                if isinstance(node, dict):
                    for k, v in node.items():
                        if k == "path" and isinstance(v, str) and v.startswith("/"):
                            exact.add(v)
                        elif k == "importArts" and isinstance(v, dict):
                            for parts in v.values():
                                exact.update(p for p in parts if isinstance(p, str) and p.startswith("/"))
                        else:
                            collect(v)
                elif isinstance(node, list):
                    for v in node:
                        collect(v)
            collect(value)
    return roots, exact


def scan_content(path, roots, exact):
    """Fail closed on unapproved host paths; don't disclose offending values."""
    rejected = set()
    pending = ""

    def inspect(text):
        for match in HOST_PATH.finditer(text):
            value = match.group(0).rstrip(" .,")
            approved = value in exact or any(value == root or value.startswith(root + "/")
                                            for root in roots)
            if not approved:
                rejected.add(digest(value.encode()))

    # Do not classify a path prefix at a block boundary as a complete token.
    # Preserve the unfinished token until its separator (or EOF) is available.
    with path.open("r", encoding="utf-8", errors="strict") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), ""):
            text = pending + block
            unfinished = re.search(r"[A-Za-z0-9_@.+~=%/-]+$", text)
            boundary = unfinished.start() if unfinished else len(text)
            inspect(text[:boundary])
            pending = text[boundary:]
        inspect(pending)
    if rejected:
        raise ValueError(f"Content screening rejected {len(rejected)} unapproved host-path tokens "
                         f"in {path.name}; values are omitted")


def screen_publication_helpers(repo, campaign, helpers):
    """Check small publication code/notes before any trace reconstruction."""
    paths = {"tools/" + name: safe_file(repo / "scripts", name) for name in HELPERS}
    paths["tools/bundle_elaboration_evidence.py"] = Path(__file__).resolve()
    for name, path in helpers.items():
        if not path.resolve().is_relative_to(repo.resolve()):
            raise ValueError("Publication helper must be a repository/campaign file")
        paths["tools/" + relative_name(name)] = safe_file(path.parent, path.name)
    for name in (*SKILLS, *SKILL_ATTRIBUTION_FILES):
        paths["skills/" + name] = safe_file(campaign / "skills", name)
    roots = {str(repo.resolve()), str(campaign.resolve())}
    exact = {"/usr/bin/env", "/usr/bin/time", "/opt/homebrew/bin/gtime"}
    for path in paths.values():
        scan_content(path, roots, exact)
    return {"files": len(paths), "passed": True,
            "scope": "Small publication helpers, notes and external skill copies; before large trace work"}


class Bundle:
    def __init__(self, root):
        self.root, self.members, self.folded = root, {}, {}
        self.omitted, self.archives = [], []

    def add(self, name, *, data=None, source=None, role="raw", provenance=None, purpose=None):
        name = relative_name(name)
        if role not in {"raw", "derived"}:
            raise ValueError("Evidence role must be raw or derived")
        folded = name.casefold()
        if folded in self.folded:
            raise ValueError("Duplicate or case-colliding bundle member: " + name)
        self.folded[folded] = name
        destination = self.root / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        if source is not None:
            if source.is_symlink() or not source.is_file() or source.stat().st_nlink != 1:
                raise ValueError("Unsafe input file")
            shutil.copyfile(source, destination)
        else:
            destination.write_bytes(data)
        self.members[name] = {"path": name, "bytes": destination.stat().st_size,
                             "sha256": file_digest(destination), "role": role,
                             "locations": ["tree"]}
        if provenance:
            self.members[name]["provenance"] = provenance
        if purpose:
            self.members[name]["purpose"] = purpose
        return destination

    def omit(self, name, original_sha256, reason):
        relative_name(name)
        if not HASH.fullmatch(original_sha256):
            raise ValueError("Invalid omitted-original digest")
        self.omitted.append({"path": name, "sha256": original_sha256,
                             "role": "omitted-original", "reason": reason})

    def archive(self, prefix):
        names = sorted(name for name in self.members if name.startswith(prefix + "/"))
        archive_name = prefix + ".tar.gz"
        archive_path = self.root / archive_name
        archive_path.parent.mkdir(parents=True, exist_ok=True)
        # Explicit allowlist only; deterministic metadata, no filesystem recursion.
        with archive_path.open("wb") as target:
            with gzip.GzipFile(filename="", fileobj=target, mode="wb", mtime=0, compresslevel=6) as compressed:
                with tarfile.open(fileobj=compressed, mode="w", format=tarfile.PAX_FORMAT) as archive:
                    for name in names:
                        path = self.root / name
                        info = tarfile.TarInfo(name)
                        info.size = self.members[name]["bytes"]
                        info.mode, info.mtime, info.uid, info.gid = 0o644, 0, 0, 0
                        info.uname = info.gname = ""
                        with path.open("rb") as stream:
                            archive.addfile(info, stream)
        validate_archive(archive_path, {name: self.members[name] for name in names})
        self.archives.append({"path": archive_name, "bytes": archive_path.stat().st_size,
                              "sha256": file_digest(archive_path), "members": names,
                              "extraction_validated": True})
        for name in names:
            self.members[name]["locations"].append(archive_name)
            if PurePosixPath(name).name not in {"summary.json", "profiles.json", "bare.json",
                    "bare-summary.json", "receipts.json", "plan.json", "verdict.json",
                    "proof-vs-statement-diagnostic.json", "candidate.patch", "REPORT.md",
                    "profile-attempts.json", "profile-attempts-receipt.json", "aggregation.json"} and self.members[name].get("purpose") != "derived origin index":
                (self.root / name).unlink()
                self.members[name]["locations"].remove("tree")


def validate_archive(path, expected):
    """Manual safe extraction; no extractall, symlinks, hardlinks or escaping names."""
    seen = set()
    with tempfile.TemporaryDirectory(prefix="cloning-evidence-check-") as temporary:
        root = Path(temporary)
        with tarfile.open(path, "r:gz") as archive:
            for info in archive:
                name = relative_name(info.name)
                if (info.type != tarfile.REGTYPE or info.issym() or info.islnk() or name not in expected
                        or name.casefold() in seen):
                    raise ValueError("Unexpected, duplicate or special archive member")
                seen.add(name.casefold())
                row = expected[name]
                if info.size != row["bytes"]:
                    raise ValueError("Archive member size differs")
                destination = root / name
                destination.parent.mkdir(parents=True, exist_ok=True)
                source = archive.extractfile(info)
                if source is None:
                    raise ValueError("Missing archive member data")
                with destination.open("wb") as output:
                    shutil.copyfileobj(source, output, 1024 * 1024)
                if file_digest(destination) != row["sha256"]:
                    raise ValueError("Extracted archive member hash differs")
        if seen != {name.casefold() for name in expected}:
            raise ValueError("Archive member set is incomplete")


def copy_benchmark(bundle, report, campaign, stage, repo):
    directory = campaign / stage
    for name in BENCHMARK_FILES:
        if (directory / name).exists():
            bundle.add(stage + "/" + name, source=safe_file(directory, name))
    samples, inventory = report.read_process_inventory(directory)
    original = inventory["original_sha256"]
    redacted = report.redact_process_inventory(samples, original, repo=repo)
    # Already-redacted inputs contain counts rather than commands; no lost census.
    if inventory["form"] != "raw":
        redacted = load_json(safe_file(directory, "process-inventory.json"))
    bundle.add(stage + "/process-inventory.json", data=json_bytes(redacted), role="derived",
               provenance={"original_sha256": original, "transformation": "UTC/count-only process inventory"})
    bundle.omit(stage + "/process-samples.json", original, "Unrelated process commands/paths omitted")


def publish_origin_index(bundle, prefix, directory, name):
    """Keep a self-contained redacted origin array with separate raw/public hashes."""
    original = safe_file(directory, name)
    original_sha = file_digest(original)
    logical = prefix + "/" + name
    public, removed = scrub_environment_fields(load_json(original))
    public_bytes = json_bytes(public)
    if logical in bundle.members:
        member = bundle.members[logical]
        if member["sha256"] != digest(public_bytes) or member.get("provenance", {}).get("original_sha256") != original_sha:
            raise ValueError("Conflicting published origin index")
    else:
        bundle.add(logical, data=public_bytes, role="derived", purpose="derived origin index",
                   provenance={"original_sha256": original_sha, "omitted_environment_fields": removed,
                               "transformation": "Removed inherited environment path fields; original record positions retained"})
        bundle.omit(logical, original_sha, "Redacted public origin index has an explicitly distinct digest")
    return {"original_index_sha256": original_sha, "public_index_sha256": digest(public_bytes)}


def copy_profile_attempts(bundle, repo, prefix, directory):
    attempts = validate_profile_attempts(repo, directory)
    if not attempts:
        return
    path = safe_file(directory, "profile-attempts.json")
    original_sha = file_digest(path)
    public_attempts, receipts = [], []
    for position, attempt in enumerate(attempts):
        record = rebase_record(attempt["profile"], attempt["input_prefix"])
        origin_hashes = publish_origin_index(bundle, prefix, directory, attempt["original_index"])
        hashes = {}
        for key in profile_input_keys(record):
            if key in attempt["expected_missing_inputs"]:
                continue
            source = safe_file(directory, record[key])
            sha = file_digest(source)
            bound = {"setup_snapshot": "setup_sha256", "trace_snapshot": "trace_sha256",
                     "import_context": "import_context_sha256"}.get(key)
            if bound and sha != record.get(bound):
                raise ValueError("Diagnostic source/setup/import context differs from its recorded digest")
            hashes[key] = sha
            logical = prefix + "/" + record[key]
            if logical in bundle.members:
                if bundle.members[logical]["sha256"] != sha:
                    raise ValueError("Conflicting shared diagnostic input")
            else:
                bundle.add(logical, source=source, purpose="diagnostic profile attempt; excluded from valid coverage")
        data, provenance = source_bytes(repo, directory, record)
        source_name = f"attempts/attempt-{position + 1:04d}.source.lean.txt"
        bundle.add(prefix + "/" + source_name, data=data, provenance=provenance,
                   purpose="hash-bound diagnostic production source copy")
        hashes["source_snapshot"] = digest(data)
        public = deepcopy(attempt)
        public["profile"] = derived_record(record, source_name, attempt["original_index_sha256"], attempt["original_record_index"])
        public.update(public_index_sha256=origin_hashes["public_index_sha256"], binding_form="derived-public-index")
        public_attempts.append(public)
        status = "disabled" if record.get("trace_mode") == "native" else ("not-produced" if "events" in attempt["expected_missing_inputs"] else "present")
        receipts.append({"module": record["module"], "trace_mode": record.get("trace_mode", "firefox"),
            "evidence_role": attempt["evidence_role"], "reason": attempt["reason"], "exit_code": record["exit_code"],
            "original_index": attempt["original_index"], **origin_hashes,
            "original_record_index": attempt["original_record_index"], "input_prefix": attempt["input_prefix"],
            "input_sha256": hashes, "expected_missing_inputs": attempt["expected_missing_inputs"],
            "event_status": status, "source_sha256": record["source_sha256"], "source_copy": source_name})
    published = {"schema": "cloning-elaboration-profile-attempts-v1", "attempts": public_attempts,
                 "publication": {"original_sha256": original_sha,
                    "transformation": "Rebased archived inputs and source copies; removed inherited environment paths; roles and reasons preserved"}}
    public_bytes = json_bytes(published)
    bundle.add(prefix + "/profile-attempts.json", data=public_bytes, role="derived",
               provenance=published["publication"], purpose="derived diagnostic attempts index")
    bundle.omit(prefix + "/profile-attempts.json", original_sha, "Redacted/rebased public diagnostic index has distinct digest")
    bundle.add(prefix + "/profile-attempts-receipt.json", data=json_bytes({
        "schema": "cloning-elaboration-profile-attempts-receipt-v1", "original_attempts_sha256": original_sha,
        "public_attempts_sha256": digest(public_bytes), "attempt_count": len(receipts), "attempts": receipts,
        "notes": ["Diagnostics are excluded from completed-profile coverage and speed comparisons.",
                  "A failed Firefox export is recorded as absent, without fabricated events or rankings.",
                  "Original guard flags are preserved as recorded; exploratory inherited flags are not asserted as validated.",
                  "Raw diagnostic log/resource hashes are captured during publication."]}),
        role="derived", purpose="derived diagnostic attempts receipt")
    validate_profile_attempts(repo, bundle.root / prefix)


def copy_profiles(bundle, repo, campaign, prefix, directory, summarizer, intervention=False):
    original_summary = load_json(safe_file(directory, "summary.json"))
    index = validate_original_profiles(directory, original_summary, intervention=intervention)
    index_sha, summary_sha = file_digest(directory / "profiles.json"), file_digest(directory / "summary.json")
    public_index, paths = [], {}
    for position, (record, result) in enumerate(zip(index, original_summary["profiles"])):
        hashes = result.get("input_sha256", {})
        for key in profile_input_keys(record):
            name = record[key]
            source = safe_file(directory, name)
            actual = file_digest(source)
            if hashes.get(key) != actual:
                raise ValueError("Raw profile input differs from its original summary hash: " + key)
            recorded_key = {"setup_snapshot": "setup_sha256", "trace_snapshot": "trace_sha256",
                            "import_context": "import_context_sha256"}.get(key)
            if recorded_key and record.get(recorded_key) != actual:
                raise ValueError("Raw profile input differs from its original record hash: " + key)
            if name in paths and paths[name] != actual:
                raise ValueError("Conflicting shared profile input")
            paths[name] = actual
        data, provenance = source_bytes(repo, directory, record)
        name = record.get("source_snapshot") or f"{record['module']}-{record['repetition']}.source.lean.txt"
        relative_name(name)
        if not name.endswith(".lean.txt"):
            # Archive as text, never introduce another owned .lean target.
            name += ".lean.txt"
        if record.get("source_snapshot") and hashes.get("source_snapshot") != digest(data):
            raise ValueError("Original source snapshot summary hash differs")
        public = derived_record(record, name, index_sha, position)
        if record.get("receipt_origin"):
            origin = record["receipt_origin"]
            origin_hashes = publish_origin_index(bundle, prefix, directory, origin["index"])
            public["receipt_origin"] = {"index": origin["index"], "record_index": origin["record_index"],
                                        "input_prefix": origin["input_prefix"], **origin_hashes,
                                        "binding_form": "derived-public-index"}
        if intervention:
            public["publication"].update(receipt_identity=list(receipt_identity(record)),
                                         receipt_label=receipt_label(record), evidence_role=receipt_role(record),
                                         diagnostic_outside_production=record["arm"] == "diagnostic",
                                         original_index="profiles.json")
        public_index.append(public)
        logical = prefix + "/" + name
        if logical in bundle.members:
            if bundle.members[logical]["sha256"] != digest(data):
                raise ValueError("Conflicting source snapshots")
        else:
            bundle.add(logical, data=data, role="raw", provenance=provenance, purpose="hash-bound source copy")
    for name in paths:
        bundle.add(prefix + "/" + name, source=safe_file(directory, name))
    bundle.add(prefix + "/profiles.json", data=json_bytes(public_index), role="derived",
               provenance={"original_sha256": index_sha,
                           "transformation": "Controlled environment fields and hash-bound source pointers"})
    copy_profile_attempts(bundle, repo, prefix, directory)
    for name in PROFILE_AUX_FILES:
        if (directory / name).exists():
            bundle.add(prefix + "/" + name, source=safe_file(directory, name),
                       purpose="saved profile runner or post-measurement aggregation provenance")
    validate_profile_origins(bundle.root / prefix, public_index)
    # Reparse the original logs/traces with the derived index to independently verify
    # source pointers and all input hashes, rather than reusing embedded raw metadata.
    published, _ = summarizer.summarize(bundle.root / prefix,
        limit=original_summary["ranking_limit"], threshold_ms=original_summary["threshold_ms"])
    for original, rebuilt in zip(original_summary["profiles"], published["profiles"]):
        for key in ("text_profile", "environment_stats", "firefox_profile", "native_resources"):
            if key == "native_resources" and key not in original:
                continue  # Legacy summaries lacked this independently regenerated GNU view.
            if original.get(key) != rebuilt.get(key):
                raise ValueError("Reconstructed profile analysis differs from the original: " + key)
        for key in profile_input_keys(original["profile"]):
            if original["input_sha256"][key] != rebuilt["input_sha256"][key]:
                raise ValueError("Reconstructed raw profile hash differs")
        if rebuilt["input_sha256"]["source_snapshot"] != rebuilt["profile"]["source_sha256"]:
            raise ValueError("Reconstructed source pointer is not hash-bound")
    published["publication"] = {
        "original_summary_sha256": summary_sha, "original_index_sha256": index_sha,
        "original_generated_utc": original_summary["generated_utc"],
        "transformation": "Regenerated from identical raw logs/traces and a redacted derived index with verified source snapshots."
    }
    bundle.add(prefix + "/summary.json", data=json_bytes(published), role="derived",
               provenance={"original_sha256": summary_sha,
                           "transformation": published["publication"]["transformation"]})
    bundle.omit(prefix + "/profiles.json", index_sha, "Original inherited environment paths omitted; derived index published")
    bundle.omit(prefix + "/summary.json", summary_sha, "Original embedded metadata omitted; derived summary published")
    return approved_paths(repo, campaign, index, directory)


def copy_intervention(bundle, repo, campaign, label, directory, driver, summarizer, report):
    """Preserve traced/diagnostic and bare receipts without changing raw identities."""
    prefix = "interventions/" + label
    summary = load_json(safe_file(directory, "summary.json"))
    profiles = validate_original_profiles(directory, summary, intervention=True)
    bare = load_json(safe_file(directory, "bare.json"))
    roots, exact = copy_profiles(bundle, repo, campaign, prefix, directory, summarizer, intervention=True)
    bare_sha = file_digest(directory / "bare.json")
    public_bare, bare_rows = [], []
    for position, record in enumerate(bare):
        hashes = {}
        for key in BARE_INPUT_KEYS:
            source = safe_file(directory, record[key])
            actual = file_digest(source)
            expected_key = {"setup_snapshot": "setup_sha256", "trace_snapshot": "trace_sha256",
                            "import_context": "import_context_sha256"}.get(key)
            if expected_key and record.get(expected_key) != actual:
                raise ValueError("Bare import/setup/build-trace input differs from its receipt")
            hashes[key] = actual
            logical = prefix + "/" + record[key]
            if logical in bundle.members:
                if bundle.members[logical]["sha256"] != actual:
                    raise ValueError("Shared bare input differs")
            else:
                bundle.add(logical, source=source,
                    purpose="bare GNU control input; content hash captured at publication")
        data, provenance = source_bytes(repo, directory, record)
        name = record.get("source_snapshot") or receipt_label(record) + ".source.lean.txt"
        if not name.endswith(".lean.txt"):
            name += ".lean.txt"
        logical = prefix + "/" + relative_name(name)
        if logical in bundle.members:
            if bundle.members[logical]["sha256"] != digest(data):
                raise ValueError("Bare source differs from its preserved profile snapshot")
        else:
            bundle.add(logical, data=data, provenance=provenance, purpose="hash-bound source copy")
        hashes["source_snapshot"] = digest(data)
        public = derived_record(record, name, bare_sha, position)
        public["publication"].update(
            receipt_identity=list(receipt_identity(record)), receipt_label=receipt_label(record),
            evidence_role=receipt_role(record), diagnostic_outside_production=record["arm"] == "diagnostic",
            original_index="bare.json")
        public_bare.append(public)
        fields = {}
        for line in safe_file(directory, record["resources"]).read_text().splitlines():
            if ": " in line:
                key, value = line.strip().rsplit(": ", 1)
                fields[key] = value
        metrics = report.resource_metrics(fields)
        if any(metrics[key] is None or not (0 <= metrics[key] < float("inf"))
               for key in ("wall", "user", "system", "cpu", "rss_kib")):
            raise ValueError("Bare GNU resources are missing or invalid")
        bare_rows.append({"record": public, "input_sha256": hashes, "native_gnu_time": metrics,
                          "notes": ["No profiler/statistics/Firefox instrumentation was requested.",
                                    "GNU log/resource hashes are captured during publication; they were not recorded by the timed runner.",
                                    "CPU is user plus system; GNU RSS is a maximum process peak in KiB."]})
    bundle.add(prefix + "/bare.json", data=json_bytes(public_bare), role="derived",
               provenance={"original_sha256": bare_sha,
                           "transformation": "Preserved arm/mode/repetition; removed inherited environment paths"})
    bundle.add(prefix + "/bare-summary.json", data=json_bytes({
        "schema": "cloning-elaboration-bare-control-summary-v1",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "original_bare_index_sha256": bare_sha, "record_count": len(bare_rows), "records": bare_rows}),
        role="derived", purpose="native GNU timing controls; no fabricated trace")
    bundle.omit(prefix + "/bare.json", bare_sha, "Inherited environment paths omitted; derived bare index published")
    # Plans may embed the effective toolchain environment; redact it consistently.
    for name in ("plan.json", "verdict.json", "proof-vs-statement-diagnostic.json"):
        original = safe_file(directory, name)
        public, removed = scrub_environment_fields(load_json(original))
        if name == "plan.json" or removed:
            original_sha = file_digest(original)
            public["publication"] = {"original_sha256": original_sha,
                "omitted_environment_fields": removed,
                "transformation": "Removed inherited environment path fields; experimental plan/decision retained"}
            bundle.add(prefix + "/" + name, data=json_bytes(public), role="derived",
                       provenance={"original_sha256": original_sha,
                                   "transformation": public["publication"]["transformation"]})
            bundle.omit(prefix + "/" + name, original_sha, "Derived public metadata replaces the environment-bearing original")
        else:
            bundle.add(prefix + "/" + name, source=original,
                purpose="recorded diagnostic" if name.startswith("proof-") else "recorded experiment verdict")
    bundle.add(prefix + "/candidate.patch", source=safe_file(directory, "candidate.patch"),
               purpose="measured candidate proof-body patch")
    for name in INTERVENTION_OPTIONAL_RECORDS:
        if (directory / name).exists():
            bundle.add(prefix + "/" + name, source=safe_file(directory, name),
                       purpose="recorded experiment interpretation; not independent verification")
    bundle.add(prefix + "/driver.py", source=driver, purpose="experimental driver bound by plan.script_sha256",
               provenance={"original_name": driver.name, "original_sha256": file_digest(driver)})
    records = []
    for index_name, index in (("profiles.json", profiles), ("bare.json", bare)):
        original_sha = file_digest(directory / index_name)
        for position, record in enumerate(index):
            records.append({"identity": list(receipt_identity(record)), "label": receipt_label(record),
                "evidence_role": receipt_role(record), "start_utc": record["start_utc"],
                "index": index_name, "record_index": position, "original_index_sha256": original_sha,
                "source_sha256": record["source_sha256"], "diagnostic_outside_production": record["arm"] == "diagnostic"})
    records.sort(key=lambda row: row["start_utc"])
    bundle.add(prefix + "/receipts.json", data=json_bytes({
        "schema": "cloning-elaboration-intervention-receipts-v1", "record_count": len(records),
        "identity_fields": ["module", "arm", "mode", "repetition"], "records": records,
        "notes": ["Raw measured repetitions, arm/mode labels, chronological order and hashes are retained.",
                  "Diagnostic sorry source is navigation evidence outside production, not an accepted proof.",
                  "Traced and bare measurements have separate summaries; bare controls have no Firefox events."]}),
        role="derived", purpose="complete experiment identity and role mapping")
    more_roots, more_exact = approved_paths(repo, campaign, bare, directory)
    return roots | more_roots, exact | more_exact


def readme(stages, profile_sets, api_source_guard=False):
    stage = stages[0]
    supplemental = ", ".join(profile_sets) or "none"
    after_command = ("\npython3 scripts/report_elaboration.py --benchmark EVIDENCE_DIRECTORY/after "
                     "--prior EVIDENCE_DIRECTORY/before --profiles EVIDENCE_DIRECTORY/profiles-after "
                     "--portable --require-complete --output ELABORATION_REPORT_AFTER.md"
                     if "before" in stages and "after" in stages else "")
    guard_note = ("\nThe source-api-guard/ directory preserves the original source/API guard and driver.\n"
                  "Its receipt labels the driver digest as captured at publication, retains the\n"
                  "historical Git context, and binds candidate bytes to accepted intervention\n"
                  "snapshots. This supplemental source guard does not replace proof verification.\n"
                  if api_source_guard else "")
    return f"""# Elaboration evidence

These records contain completed cold own-module builds and serial warm profiles.
Benchmark records are unchanged. Process inventories contain UTC/counts only;
the original omitted records' hashes are in manifest.json. Public profile indexes
remove inherited path-valued environment fields. Summaries are regenerated from
the same raw traces with source copies verified against each source_sha256.

Detailed traces, logs, resources, source copies, matching Lake setups, build traces
and import contexts are compressed in each profiles-*.tar.gz. Supplemental sets:
{supplemental}. Every member has a SHA-256, size and role in manifest.json; each
archive was safely extracted and checked against the exact member set before
publication. Task-specific source/setup/import paths remain as measurement
provenance. Saved setups should be replaced by locally generated ones for a new run.

Intervention receipts retain module, arm, mode and measured repetition. Traced runs
and bare GNU controls have separate summaries; bare controls have no Firefox data.
Diagnostic sorry snapshots are explicitly labeled outside production. Plans,
verdicts (including rejected candidates), driver bytes, patches and source/artifact
hashes are preserved, with original hashes for redacted metadata.
{guard_note}

The copied measurement helper and elaboration guides are by
[Scott Armstrong (`scottnarmstrong`)](https://github.com/scottnarmstrong), from
[LeanAutoformalizationSkills]({SKILL_REPOSITORY}/tree/{SKILL_PIN}), under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). Their contents are
unmodified. [Attribution](skills/ATTRIBUTION.md) and [provenance](skills/provenance.json)
map each pinned original source path to its local filename and digest; the exact
upstream [license and warranty disclaimer](skills/LICENSE) are preserved.

From a Git checkout containing the recorded measured commits, extract the profile
archives into this evidence directory (their members include the relative prefix).
For example, run `tar -xzf EVIDENCE_DIRECTORY/profiles-{stage}.tar.gz -C EVIDENCE_DIRECTORY`.
Keep its small profiles-*/summary.json and profiles.json files in place. Then:

```sh
python3 scripts/report_elaboration.py --benchmark EVIDENCE_DIRECTORY/{stage} --profiles EVIDENCE_DIRECTORY/profiles-{stage} --portable --require-complete --output ELABORATION_REPORT_{stage.upper()}.md{after_command}
python3 scripts/summarize_elaboration_profiles.py --profiles EVIDENCE_DIRECTORY/profiles-{stage} --output .verify-work/cloning-profile-summary-review.json
```

For a fresh measurement with populated pinned dependency caches and GNU time
available as gtime, use fresh output directories from the repository root:

```sh
python3 scripts/benchmark_elaboration.py --output .verify-work/elaboration-reproduce --threads 2 --size-helper EVIDENCE_DIRECTORY/skills/count_lean_lines.py --time gtime
python3 scripts/profile_elaboration.py --benchmark .verify-work/elaboration-reproduce --output .verify-work/elaboration-reproduce-profiles --top 5 --threads 2 --time gtime
python3 scripts/summarize_elaboration_profiles.py --profiles .verify-work/elaboration-reproduce-profiles
```

The recorded commands, commits, environment overrides and configuration hashes
identify historical inputs; publication helper copies in tools/ identify the
bundling/reconstruction version, and are not proof that those versions were used
during the original timed processes. Historical reproduction requires the recorded
proof/config state and compatible helpers; rebuild local setups instead of running
host-specific saved paths. Cold Lake job durations are rounded elapsed estimates.
Profiler intervals can overlap and are not native CPU time. GNU peak RSS is a
maximum process peak rather than aggregate concurrent memory.
"""


def write_bundle(repo, campaign, stages, expectations, extra_sets, output, interventions=None,
                 intervention_expectations=None, intervention_drivers=None, api_source_guard=None,
                 publication_helpers=None):
    interventions, intervention_expectations, intervention_drivers = (
        interventions or {}, intervention_expectations or {}, intervention_drivers or {})
    output = output.absolute()
    if output.exists() or output.is_symlink():
        raise ValueError("Refusing to overwrite an evidence bundle")
    sources = [campaign.resolve(), *(directory.resolve() for directory in extra_sets.values()),
               *(directory.resolve() for directory in interventions.values())]
    if any(output.resolve().is_relative_to(source) for source in sources):
        raise ValueError("Output must not be nested in measured input directories")
    inspection, report = inspect_campaign(repo, campaign, stages, expectations, extra_sets, strict=True,
        interventions=interventions, intervention_expectations=intervention_expectations,
        intervention_drivers=intervention_drivers, api_source_guard=api_source_guard)
    inspection["publication_content_preflight"] = screen_publication_helpers(repo, campaign, publication_helpers or {})
    summarizer = load_tool(repo, "summarize_elaboration_profiles")
    small_inputs = {}
    for stage in stages:
        directory = campaign / stage
        for name in (*BENCHMARK_FILES, "process-samples.json", "process-inventory.json"):
            if (directory / name).exists():
                small_inputs[stage + "/" + name] = safe_file(directory, name)
    profile_directories = {"profiles-" + stage: campaign / ("profiles-" + stage) for stage in stages}
    profile_directories.update(extra_sets)
    for prefix, directory in profile_directories.items():
        for name in ("profiles.json", "summary.json"):
            small_inputs[prefix + "/" + name] = safe_file(directory, name)
        index = load_json(directory / "profiles.json")
        origins = validate_profile_origins(directory, index)
        attempts = validate_profile_attempts(repo, directory)
        for attempt in attempts:
            origins[attempt["original_index"]] = safe_file(directory, attempt["original_index"])
        for name, path in origins.items():
            small_inputs[prefix + "/" + name] = path
        for name in ("profile-attempts.json", *PROFILE_AUX_FILES):
            if (directory / name).exists():
                small_inputs[prefix + "/" + name] = safe_file(directory, name)
    for label, directory in interventions.items():
        for name in (*INTERVENTION_RECORDS, *INTERVENTION_OPTIONAL_RECORDS):
            if (directory / name).exists():
                small_inputs["interventions/" + label + "/" + name] = safe_file(directory, name)
        small_inputs["interventions/" + label + "/driver.py"] = intervention_drivers[label]
    api_evidence = None
    if api_source_guard is not None:
        guard_commit = load_json(safe_file(api_source_guard[0].parent, api_source_guard[0].name))["baseline_commit"]
        guard_snapshots = {stage: report.Snapshot.read(campaign / stage) for stage in stages
                           if load_json(campaign / stage / "summary.json")["commit"] == guard_commit}
        api_evidence = validate_api_source_guard(repo, *api_source_guard, guard_snapshots, interventions)
        small_inputs["source-api-guard/cleanup-api-source-guard.json"] = api_evidence["guard_path"]
        small_inputs["source-api-guard/driver.py"] = api_evidence["driver"]
    for name in (*SKILLS, *SKILL_ATTRIBUTION_FILES):
        small_inputs["skills/" + name] = safe_file(campaign / "skills", name)
    for name, path in (publication_helpers or {}).items():
        if not path.resolve().is_relative_to(repo):
            raise ValueError("Publication helper must be a repository/campaign file")
        small_inputs["tools/" + relative_name(name)] = safe_file(path.parent, path.name)
    original_small_hashes = {name: file_digest(path) for name, path in small_inputs.items()}
    # Resolve repository roots explicitly for a relocated helper file.
    report.REPO, summarizer.REPO, summarizer.PROJECT = repo, repo, repo / "formalization"
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=".elaboration-bundle-", dir=output.parent) as temporary:
        root = Path(temporary) / "bundle"
        root.mkdir()
        bundle = Bundle(root)
        roots = {str(repo.resolve()), str(campaign.resolve())}
        # Published scripts/skill instructions refer to these standard tool names.
        exact = {"/usr/bin/env", "/usr/bin/time", "/opt/homebrew/bin/gtime"}
        for stage in stages:
            copy_benchmark(bundle, report, campaign, stage, repo)
            more_roots, more_exact = copy_profiles(bundle, repo, campaign, "profiles-" + stage,
                                                   campaign / ("profiles-" + stage), summarizer)
            roots.update(more_roots)
            exact.update(more_exact)
            summary = load_json(campaign / stage / "summary.json")
            exact.update(value for value in summary["command"]
                         if isinstance(value, str) and value.startswith("/"))
        for name, directory in extra_sets.items():
            more_roots, more_exact = copy_profiles(bundle, repo, campaign, name, directory, summarizer)
            roots.update(more_roots)
            exact.update(more_exact)
        for label, directory in interventions.items():
            more_roots, more_exact = copy_intervention(bundle, repo, campaign, label, directory,
                intervention_drivers[label], summarizer, report)
            roots.update(more_roots)
            exact.update(more_exact)
        if api_evidence is not None:
            copy_api_source_guard(bundle, api_evidence)
        copy_skill_evidence(bundle, campaign)
        for name in HELPERS:
            bundle.add("tools/" + name, source=safe_file(repo / "scripts", name),
                       purpose="publication-helper")
        for name, path in (publication_helpers or {}).items():
            bundle.add("tools/" + relative_name(name), source=path, purpose="publication-helper",
                       provenance={"original_name": path.name, "sha256_capture": "publication-time",
                                   "note": "Untimed report/support/aggregation snapshot; not a timed Lean driver unless separately bound"})
            if name == "aggregate-after-profiles.py":
                for stage in stages:
                    aggregation = campaign / ("profiles-" + stage) / "aggregation.json"
                    if aggregation.exists() and load_json(aggregation).get("driver_sha256") != file_digest(path):
                        raise ValueError("Aggregation driver copy differs from its recorded source digest")
        bundle.add("tools/bundle_elaboration_evidence.py", source=Path(__file__).resolve(),
                   purpose="publication-helper")
        supplemental = list(extra_sets) + ["interventions/" + label for label in interventions]
        bundle.add("README.md", data=readme(stages, supplemental, api_evidence is not None).encode(),
                   role="derived", purpose="publication-guide")
        # Screen before compression; never publish the raw process sample file.
        for name in bundle.members:
            scan_content(root / name, roots, exact)
        for prefix in ["profiles-" + stage for stage in stages] + supplemental:
            bundle.archive(prefix)
        manifest = {
            "schema": "cloning-elaboration-evidence-bundle-v1",
            "generated_utc": datetime.now(timezone.utc).isoformat(),
            "inspection": inspection, "members": [bundle.members[name] for name in sorted(bundle.members)],
            "archives": bundle.archives, "omitted_originals": bundle.omitted,
            "original_small_records_sha256": original_small_hashes,
            "publication_notes": [
                "Raw benchmark and profile input records are byte-identical where labeled raw.",
                "Derived metadata and original omitted-file digests are explicitly labeled.",
                "Content screening allows task source/setup/import/tool paths; it rejects unapproved host-path tokens.",
                "The manifest cannot hash itself; manifest.sha256 checks its bytes."
            ],
        }
        manifest_path = root / "manifest.json"
        manifest_path.write_bytes(json_bytes(manifest))
        (root / "manifest.sha256").write_text(file_digest(manifest_path) + "  manifest.json\n")
        # Recheck measured small records immediately before atomic publication.
        second, _ = inspect_campaign(repo, campaign, stages, expectations, extra_sets, strict=True,
            interventions=interventions, intervention_expectations=intervention_expectations,
            intervention_drivers=intervention_drivers, api_source_guard=api_source_guard)
        if second["sets"] != inspection["sets"]:
            raise ValueError("Campaign records changed during publication preparation")
        if any(file_digest(path) != original_small_hashes[name] for name, path in small_inputs.items()):
            raise ValueError("Original small campaign records changed during publication preparation")
        for name, expected in original_small_hashes.items():
            if name in bundle.members and bundle.members[name]["role"] == "raw":
                if bundle.members[name]["sha256"] != expected:
                    raise ValueError("Copied raw record differs from its original: " + name)
        # Claim a fresh output name immediately before the directory rename;
        # an output created concurrently must never be replaced.
        output.mkdir(exist_ok=False)
        try:
            os.rename(root, output)
        except BaseException:
            output.rmdir()  # Only our still-empty reservation can be removed.
            raise
    return {"output": str(output), "archives": len(bundle.archives),
            "members": len(bundle.members), "manifest_sha256": file_digest(output / "manifest.json")}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--campaign", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--stage", choices=("before", "after"), action="append")
    parser.add_argument("--expect", action="append", default=[],
                        help="STAGE=MODULE[@REPETITION],... (default repetition 1); required for every --write profile set")
    parser.add_argument("--profile-set", action="append", default=[],
                        help="LABEL=COMPLETED_DIRECTORY; ordinary supplemental profiles with unique module/repetitions")
    parser.add_argument("--intervention", action="append", default=[], help="LABEL=COMPLETED_AB_DIRECTORY")
    parser.add_argument("--expect-intervention", action="append", default=[],
                        help="LABEL=ARM-REPETITION-MODE,...; exact traced/diagnostic/bare receipt plan")
    parser.add_argument("--intervention-driver", action="append", default=[],
                        help="LABEL=DRIVER_FILE; source bytes must match plan.script_sha256")
    parser.add_argument("--api-source-guard", type=Path,
                        help="Original saved source/API guard; requires its driver and accepted intervention receipts")
    parser.add_argument("--api-source-guard-driver", type=Path,
                        help="Source/API guard driver; digest is captured at publication, not asserted to be recorded at run time")
    parser.add_argument("--publication-helper", action="append", default=[],
                        help="NAME=FILE; save exact untimed report/support/aggregation helper as tools/NAME")
    parser.add_argument("--write", action="store_true", help="Explicitly reconstruct, compress, validate and write; schedule while Lean is idle")
    args = parser.parse_args()
    try:
        repo, campaign = args.repo.resolve(), args.campaign.resolve()
        stages = list(dict.fromkeys(args.stage or ["before"]))
        expectations, extra_sets = {}, {}
        interventions, intervention_expectations, intervention_drivers = {}, {}, {}
        for value in args.expect:
            name, modules = parse_assignment(value)
            if name in expectations:
                raise ValueError("Repeated --expect name")
            expectations[relative_name(name)] = modules.split(",")
        for value in args.profile_set:
            label, path = parse_assignment(value)
            if not LABEL.fullmatch(label) or label in {".", ".."}:
                raise ValueError("Invalid supplemental profile-set label")
            name = "interventions/" + label
            if name in extra_sets:
                raise ValueError("Repeated supplemental profile set")
            extra_sets[name] = Path(path).resolve()
        if set(expectations) - set(stages) - set(extra_sets):
            raise ValueError("Unexpected --expect set name")
        for values, target, transform in ((args.intervention, interventions, lambda value: Path(value).resolve()),
                (args.expect_intervention, intervention_expectations, lambda value: value.split(",")),
                (args.intervention_driver, intervention_drivers, lambda value: Path(value).absolute())):
            for value in values:
                label, payload = parse_assignment(value)
                if not LABEL.fullmatch(label) or label in {".", ".."} or label in target:
                    raise ValueError("Invalid or repeated intervention label")
                target[label] = transform(payload)
        if (set(intervention_expectations) - set(interventions) or set(intervention_drivers) - set(interventions)
                or any("interventions/" + label in extra_sets for label in interventions)):
            raise ValueError("Unexpected or colliding intervention options")
        if (args.api_source_guard is None) != (args.api_source_guard_driver is None):
            raise ValueError("Supply both --api-source-guard and --api-source-guard-driver")
        api_source_guard = ((args.api_source_guard.absolute(), args.api_source_guard_driver.absolute())
                            if args.api_source_guard is not None else None)
        publication_helpers = {}
        for value in args.publication_helper:
            name, path = parse_assignment(value)
            relative_name(name)
            if "/" in name or name.casefold() in {key.casefold() for key in publication_helpers}:
                raise ValueError("Invalid or repeated publication helper name")
            publication_helpers[name] = Path(path).absolute()
        if args.write:
            result = write_bundle(repo, campaign, stages, expectations, extra_sets, args.output,
                interventions, intervention_expectations, intervention_drivers, api_source_guard, publication_helpers)
        else:
            result, _ = inspect_campaign(repo, campaign, stages, expectations, extra_sets,
                interventions=interventions, intervention_expectations=intervention_expectations,
                intervention_drivers=intervention_drivers, api_source_guard=api_source_guard)
            result["requested_output"] = str(args.output)
            result["publication_helpers"] = {name: {"sha256": file_digest(safe_file(path.parent, path.name)),
                "capture": "inspection-time; publication rechecks exact bytes"}
                for name, path in publication_helpers.items()}
            result["publication_content_preflight"] = screen_publication_helpers(repo, campaign, publication_helpers)
        print(json.dumps(result, indent=2, sort_keys=True))
    except (ValueError, OSError, KeyError, TypeError, UnicodeError, subprocess.CalledProcessError) as error:
        parser.exit(1, type(error).__name__ + ": " + str(error) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
