#!/usr/bin/env python3
"""Validate the relocated seventh-pass certificate without invoking Lean.

This checks saved evidence and its agreement with the current Cloning sources.
It is an integrity/replay check, not a new kernel check or a digital signature.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


class CheckpointError(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise CheckpointError(message)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def safe_path(base, relative):
    path = Path(relative)
    require(not path.is_absolute() and ".." not in path.parts,
            f"Invalid certificate path: {relative}")
    return base / path


def check_hash(path, expected):
    require(path.is_file(), f"Missing file: {path}")
    require(sha256(path) == expected, f"SHA-256 mismatch: {path}")


def proof_sources(project):
    return [project / "Cloning.lean", *sorted((project / "Cloning").rglob("*.lean"))]


def source_hashes(project):
    return {p.relative_to(project).as_posix(): sha256(p) for p in proof_sources(project)}


def copy_sources(project, destination):
    for path in proof_sources(project):
        target = destination / path.relative_to(project)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)


def historical_engine(project):
    checkpoint = project / "verification/seventh-pass"
    freeze = read_json(checkpoint / "BUILD-seventh-final-freeze.json")
    engine = checkpoint / "audit.py"
    check_hash(engine, freeze["audit_script_sha256"])
    return engine


def validate(project):
    project = project.resolve()
    checkpoint = project / "verification/seventh-pass"
    manifest = read_json(checkpoint / "SHA256SUMS.json")
    require(isinstance(manifest, dict) and manifest, "Empty checksum manifest")
    # Original presentation/config files live in the archive after reorganization.
    for relative, digest in manifest.items():
        archived = safe_path(checkpoint, relative)
        path = archived if archived.is_file() else safe_path(project, relative)
        check_hash(path, digest)
    archived_files = {p.relative_to(checkpoint).as_posix()
                      for p in checkpoint.rglob("*") if p.is_file()}
    require(archived_files - {"SHA256SUMS.json"} <= manifest.keys(),
            "Historical archive contains files absent from its checksum manifest")

    freeze = read_json(checkpoint / "BUILD-seventh-final-freeze.json")
    result = read_json(checkpoint / "AUDIT-seventh-result.json")
    original = read_json(checkpoint / "AUDIT-seventh-verification.json")
    extended = read_json(checkpoint / "verification.json")
    actual_sources = source_hashes(project)
    require(actual_sources == freeze["source_sha256"] == original["source_sha256"],
            "Current proof sources differ from the audited source inventory or hashes")
    require(all(extended.get(key) == value for key, value in original.items()),
            "Extended verification metadata changes an original audit field")
    require(result["returncode"] == 0, "Historical audit did not exit successfully")
    for key in ("source_hashes_unchanged", "artifact_hashes_unchanged",
                "lean_binary_unchanged", "audit_script_unchanged"):
        require(result.get(key) is True, f"Historical audit gate failed: {key}")
    require(freeze.get("source_and_artifact_coverage_exact") is True,
            "Historical build does not record exact artifact coverage")
    require(original.get("axiom_audit") == "passed" and original.get("lean_exit_code") == 0,
            "Original axiom audit did not pass")
    require(original.get("allowed_axioms") == ["Classical.choice", "Quot.sound", "propext"],
            "Unexpected allowed-axiom policy")
    for key in ("unexpected_axioms", "missing_modules", "missing_reports",
                "duplicate_reports", "conflicting_reports"):
        require(not original.get(key), f"Original audit records a failure: {key}")
    require(result["audit_jobs"] == original["audit_jobs"], "Audit worker counts differ")
    check_hash(checkpoint / "BUILD-seventh-final-freeze.json", result["freeze_sha256"])
    for relative, digest in result["audit_artifact_sha256"].items():
        # This digest predates the addition of semantic metadata to verification.json.
        name = "AUDIT-seventh-verification.json" if relative == "verification.json" else relative
        check_hash(safe_path(checkpoint, name), digest)
    historical_engine(project)
    check_hash(checkpoint / "check_local.py", freeze["checker_sha256"])

    artifact_names = {str(Path(name).with_suffix(".olean")) for name in actual_sources}
    require(set(freeze["compiled_artifact_sha256"]) == artifact_names,
            "Saved final compiled-artifact inventory differs from the source inventory")
    combined_log = b""
    for phase, fingerprints in freeze["clean_build_phases"].items():
        stem = f"BUILD-seventh-{phase}"
        inputs_path, result_path, log_path = (
            checkpoint / (stem + suffix) for suffix in ("-inputs.json", "-result.json", ".log"))
        for path, key in ((inputs_path, "inputs_sha256"), (result_path, "result_sha256"),
                          (log_path, "log_sha256")):
            check_hash(path, fingerprints[key])
        inputs, phase_result = read_json(inputs_path), read_json(result_path)
        require(phase_result["returncode"] == 0 and
                phase_result.get("source_hashes_unchanged") is True and
                not phase_result.get("changed_sources"), f"Build phase failed: {phase}")
        check_hash(inputs_path, phase_result["input_manifest_sha256"])
        check_hash(log_path, phase_result["build_log_sha256"])
        for name, digest in inputs["source_sha256"].items():
            if name != "Cloning.lean":  # Intermediate umbrellas intentionally gained imports.
                require(actual_sources.get(name) == digest,
                        f"Build phase {phase} source changed: {name}")
        for name, digest in phase_result["compiled_artifact_sha256"].items():
            if name != "Cloning.olean":
                require(freeze["compiled_artifact_sha256"].get(name) == digest,
                        f"Recorded build phase {phase} artifact changed: {name}")
        combined_log += log_path.read_bytes()
    require(combined_log == (checkpoint / "BUILD.log").read_bytes(),
            "Combined build log differs from the phase logs")
    check_hash(checkpoint / "BUILD.log", freeze["combined_build_log_sha256"])
    final_build = read_json(checkpoint / "BUILD-seventh-phase3-result.json")
    require(final_build["compiled_artifact_sha256"] == freeze["compiled_artifact_sha256"],
            "Final build and audit artifact inventories differ")
    require(freeze["modules"] == original["modules"] and
            freeze["source_theorems_and_lemmas"] == original["theorems"],
            "Build and audit source counts differ")

    # These active dependency pins must still match, even if copies are archived later.
    for name in ("lean-toolchain", "lake-manifest.json"):
        check_hash(project / name, manifest[name])
    dependencies = read_json(project / "lake-manifest.json")["packages"]
    mathlib = [dep for dep in dependencies if dep["name"] == "mathlib"]
    require(len(mathlib) == 1, "Expected exactly one pinned mathlib dependency")
    lakefile = (project / "lakefile.toml").read_text(encoding="utf-8")
    requires = re.findall(r"\[\[require\]\]([^[]*)", lakefile)
    mathlib_requires = [s for s in requires if re.search(r'(?m)^name\s*=\s*"mathlib"\s*$', s)]
    require(len(mathlib_requires) == 1 and re.search(
        r'(?m)^rev\s*=\s*"' + re.escape(mathlib[0]["rev"]) + r'"\s*$', mathlib_requires[0]),
        "Active Lake configuration does not retain the audited mathlib revision")

    # Replay the original complete Python validation, never its fresh-Lean branch.
    # Copying prevents --resummarize from rewriting the archived completion record.
    with tempfile.TemporaryDirectory(prefix="cloning-checkpoint-") as temporary:
        scratch = Path(temporary)
        copy_sources(project, scratch)
        for name in ("audit.py", "Audit.lean", "AXIOMS.txt"):
            shutil.copyfile(checkpoint / name, scratch / name)
        shutil.copyfile(checkpoint / "AUDIT-seventh-verification.json", scratch / "verification.json")
        shutil.copytree(checkpoint / "audit-shards", scratch / "audit-shards")
        replay = subprocess.run([sys.executable, str(scratch / "audit.py"), "--resummarize"],
                                cwd=scratch, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, check=False)
        require(replay.returncode == 0, "Saved audit replay failed:\n" + replay.stdout[-6000:])
        require(read_json(scratch / "verification.json") == original,
                "Recomputed audit summary differs from the original completion record")
    return {"status": "passed", "modules": original["modules"],
            "source_theorems_and_lemmas": original["theorems"],
            "audited_constants": original["audited_constants"],
            "raw_constant_reports": original["raw_constant_reports"],
            "manifest_files_checked": len(manifest), "lean_invoked": False,
            "scope": "saved certificate integrity and exact current Cloning source match"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1],
                        help="formalization directory (default: this script's project)")
    args = parser.parse_args()
    try:
        print(json.dumps(validate(args.root), indent=2))
    except (CheckpointError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"Checkpoint check failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
