#!/usr/bin/env python3
"""Build with Lake and run the archived all-constant auditor in isolated scratch.

The seventh-pass archive is never rewritten. Fresh evidence is saved separately.
Use --prepare-only to inspect generated drivers without running Lake or Lean.
"""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from check_checkpoint import (CheckpointError, copy_sources, historical_engine,
                              read_json, require, sha256, source_hashes)


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def current_inputs(project):
    paths = [*project.glob("*.lean"), *(project / "Cloning").rglob("*.lean"),
             project / "lean-toolchain", project / "lakefile.toml", project / "lake-manifest.json"]
    return {p.relative_to(project).as_posix(): sha256(p) for p in sorted(set(paths))}


def compiled_hashes(project):
    build = project / ".lake/build/lib/lean"
    result = {}
    for relative in source_hashes(project):
        path = build / Path(relative).with_suffix(".olean")
        require(path.is_file(), f"Missing Lake artifact after build: {path}")
        result[path.relative_to(build).as_posix()] = sha256(path)
    return result


def logged_command(command, cwd, env, log, progress_only=False):
    with log.open("w", encoding="utf-8") as output:
        process = subprocess.Popen(command, cwd=cwd, env=env, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        for line in process.stdout:
            output.write(line)
            output.flush()
            if not progress_only or line.startswith(("AUDIT SHARD", "SHARD ", "AXIOM REPORTS")):
                print(line, end="", flush=True)
        return process.wait()


def preserve_workspace(scratch, output):
    for item in scratch.iterdir():
        if item.name == "build":  # Never ship the link to the live compiled artifacts.
            continue
        target = output / item.name
        if item.is_dir():
            shutil.copytree(item, target)
        else:
            shutil.copyfile(item, target)


def run(project, output, jobs, prepare_only):
    archive = project / "verification/seventh-pass"
    require(not output.is_relative_to(archive.resolve()),
            "Fresh audit output must not be inside the historical checkpoint")
    require(not output.exists(), f"Output already exists: {output}")
    engine = historical_engine(project)
    output.mkdir(parents=True)
    result = {"status": "running", "started_utc": datetime.now(timezone.utc).isoformat(),
              "audit_jobs": jobs, "historical_engine_sha256": sha256(engine),
              "scope": "all compiled declarations exported by imported Cloning modules"}
    write_json(output / "run.json", result)
    try:
        inputs = current_inputs(project)
        result["input_sha256"] = inputs
        if not prepare_only:
            require(os.name != "nt", "The archived engine requires a POSIX Lean search path; use WSL")
            lake = shutil.which("lake")
            require(lake is not None, "lake is unavailable; install elan and fetch the pinned toolchain")
            result["build_command"] = [lake, "build", "All"]
            print("Building All with the project's pinned Lake toolchain...", flush=True)
            result["build_returncode"] = logged_command(
                result["build_command"], project, os.environ.copy(), output / "build.log")
            result["build_input_hashes_unchanged"] = current_inputs(project) == inputs
            require(result["build_input_hashes_unchanged"],
                    "Project sources or dependency pins changed during build")
            require(result["build_returncode"] == 0, f"Lake build failed; see {output / 'build.log'}")
        if not prepare_only:
            artifacts = compiled_hashes(project)
            result["compiled_artifact_sha256"] = artifacts
        with tempfile.TemporaryDirectory(prefix="cloning-audit-") as temporary:
            scratch = Path(temporary)
            copy_sources(project, scratch)
            shutil.copyfile(engine, scratch / "audit.py")
            require(source_hashes(scratch) == source_hashes(project),
                    "Proof sources changed while preparing the audit snapshot")
            try:
                if prepare_only:
                    command = [sys.executable, str(scratch / "audit.py"),
                               "--generate-only", "--jobs", str(jobs)]
                    code = logged_command(command, scratch, os.environ.copy(), output / "prepare.log")
                    require(code == 0, "Audit driver generation failed")
                    result.update(status="prepared_only", lean_invoked=False, returncode=0)
                else:
                    (scratch / "build").symlink_to(project / ".lake/build/lib/lean", target_is_directory=True)
                    env = os.environ.copy()
                    # `lake env` puts the pinned compiler on PATH. The engine's Lean
                    # subprocess runs from scratch, so it must not use its old fallback path.
                    env["CLONING_LEAN"] = "lean"
                    env["CLONING_PACKAGES"] = str(project / ".lake/packages")
                    command = [lake, "env", sys.executable, str(scratch / "audit.py"),
                               "--jobs", str(jobs)]
                    result["audit_command"] = ["lake", "env", "python3", "<scratch>/audit.py",
                                               "--jobs", str(jobs)]
                    print(f"Auditing in {jobs} worker(s); full log: {output / 'audit.log'}", flush=True)
                    code = logged_command(command, project, env, output / "audit.log", progress_only=True)
                    result["returncode"] = code
                    require(code == 0, f"Lean axiom audit failed; see {output / 'audit.log'}")
                    summary = read_json(scratch / "verification.json")
                    require(summary["axiom_audit"] == "passed", "Auditor did not certify success")
                    require(summary["source_sha256"] == source_hashes(project),
                            "Audited source snapshot differs from the current project")
                    result["artifact_hashes_unchanged"] = compiled_hashes(project) == artifacts
                    require(result["artifact_hashes_unchanged"], "Compiled artifacts changed during audit")
                    result.update(status="passed", lean_invoked=True,
                                  modules=summary["modules"], theorems=summary["theorems"],
                                  audited_constants=summary["audited_constants"])
                result["input_hashes_unchanged"] = current_inputs(project) == inputs
                require(result["input_hashes_unchanged"], "Project sources or dependency pins changed during audit")
                require(sha256(engine) == result["historical_engine_sha256"], "Historical auditor changed during audit")
            finally:
                preserve_workspace(scratch, output)
        result["evidence_sha256"] = {
            p.relative_to(output).as_posix(): sha256(p)
            for p in sorted(output.rglob("*")) if p.is_file() and p.name != "run.json"}
    except (CheckpointError, OSError, ValueError, KeyError, TypeError) as error:
        result.update(status="failed", error=str(error))
        raise
    finally:
        result["completed_utc"] = datetime.now(timezone.utc).isoformat()
        write_json(output / "run.json", result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=1, help="parallel auditor workers (default: 1)")
    parser.add_argument("--output", type=Path, help="new evidence directory; must not already exist")
    parser.add_argument("--prepare-only", action="store_true", help="generate an isolated audit snapshot; run no Lake or Lean")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be a positive integer")
    project = Path(__file__).resolve().parents[1]
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    output = (args.output or project / "verification/runs" / stamp).resolve()
    try:
        result = run(project, output, args.jobs, args.prepare_only)
    except (CheckpointError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"Audit failed: {error}", file=sys.stderr)
        return 1
    print(f"{result['status']}: {output}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
