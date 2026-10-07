#!/usr/bin/env python3
"""Serial warm profiles of owned modules from a completed elaboration test."""
import argparse
from datetime import datetime, timezone
import json
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import time

REPO = Path(__file__).resolve().parents[1]
PROJECT = REPO / "formalization"
CONFIGS = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def config_hashes():
    return {"formalization/" + name: sha256(PROJECT / name) for name in CONFIGS}


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def git_source(commit, source):
    return subprocess.check_output(["git", "show", f"{commit}:formalization/{source}"], cwd=REPO)


def effective_environment(lake, env):
    # Capture relevant effective values, never the complete inherited environment.
    code = ("import json,os,shutil; "
            "print(json.dumps({'environment':{k:os.environ.get(k) for k in "
            "['LEAN_NUM_THREADS','LAKE_ARTIFACT_CACHE','LAKE_NO_CACHE','LEAN_PATH',"
            "'LEAN_SYSROOT','LEAN_GITHASH','PATH','LANG','LC_ALL']},"
            "'lean_binary':shutil.which('lean')}))")
    result = json.loads(subprocess.check_output([lake, "env", "python3", "-c", code],
                                               cwd=PROJECT, env=env, text=True))
    binary = Path(result["lean_binary"]).resolve()
    result.update({"lean_binary": str(binary), "lean_binary_sha256": sha256(binary),
                   "lean_version": subprocess.check_output([lake, "env", "lean", "--version"],
                                                            cwd=PROJECT, env=env, text=True).strip(),
                   "lean_libdir": subprocess.check_output([lake, "env", "lean", "--print-libdir"],
                                                           cwd=PROJECT, env=env, text=True).strip(),
                   "lake_version": subprocess.check_output([lake, "--version"],
                                                           cwd=PROJECT, env=env, text=True).strip()})
    return result


def artifact_family(olean):
    candidates = [olean, olean.with_suffix(".ir"), Path(str(olean) + ".server"),
                  Path(str(olean) + ".private")]
    return [str(path.resolve()) for path in candidates if path.is_file()]


def project_path(name):
    path = Path(name)
    return (path if path.is_absolute() else PROJECT / path).resolve()


def stat_artifacts(paths):
    rows, digest = [], hashlib.sha256()
    for name in sorted(set(paths)):
        path = Path(name)
        if not path.is_file():
            raise ValueError("Missing compiled import artifact: " + name)
        stat = path.stat()
        row = {"path": name, "bytes": stat.st_size, "mtime_ns": stat.st_mtime_ns}
        rows.append(row)
        digest.update((json.dumps(row, sort_keys=True) + "\n").encode())
    return {"artifact_count": len(rows), "path_size_mtime_sha256": digest.hexdigest()}, rows


def import_context(lake, source, setup, effective, env):
    # --deps-json parses the header and returns before elaboration. --deps alone
    # ignores --setup in this Lean version, so resolve its names against the saved
    # setup map first and use the effective search path only for unmapped names.
    parsed = json.loads(subprocess.check_output([lake, "env", "lean", "--deps-json", source],
                                               cwd=PROJECT, env=env, text=True))
    header = parsed["imports"][0]
    if header.get("errors") or header.get("result?") is None:
        raise ValueError("Cannot parse profile import header: " + str(header))
    imports = header["result?"]["imports"]
    mapped = setup.get("importArts", {})
    search = [project_path(p) for p in (effective["environment"].get("LEAN_PATH") or "").split(os.pathsep) if p]
    search.append(project_path(effective["lean_libdir"]))
    direct = []
    for declaration in imports:
        name = declaration["module"]
        if name in mapped:
            paths, origin = mapped[name], "saved-setup-map"
        else:
            relative = Path(*name.split(".")).with_suffix(".olean")
            olean = next((base / relative for base in search if (base / relative).is_file()), None)
            if olean is None:
                raise ValueError("Cannot resolve new/fallback direct import: " + name)
            paths, origin = artifact_family(olean), "effective-search-path-fallback"
        direct.append({"module": name, "modifiers": declaration, "origin": origin,
                       "artifacts": [{"path": str(project_path(path)), "sha256": sha256(project_path(path))}
                                     for path in paths]})
    mapped_stats, rows = stat_artifacts(str(project_path(path)) for paths in mapped.values() for path in paths)
    return {"direct_imports": direct, "mapped_artifact_metadata": mapped_stats}, rows


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--benchmark", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--modules", nargs="*")
    p.add_argument("--top", type=int, default=5)
    p.add_argument("--repeat", type=int, default=1)
    p.add_argument("--threads", type=int, default=2)
    p.add_argument("--time", default="/opt/homebrew/bin/gtime")
    args = p.parse_args()
    summary = json.loads((args.benchmark / "summary.json").read_text())
    if (summary["exit_code"] != 0 or not summary["dependency_artifacts_unchanged"]
            or summary.get("source_config_hashes_unchanged") is False
            or summary.get("upstream_compilations")):
        p.error("A successful project-only benchmark is required")
    supplemental = args.benchmark / "source-config-stability.json"
    if supplemental.is_file():
        stability = json.loads(supplemental.read_text())
        if (stability.get("schema") != "cloning-elaboration-source-stability-v1"
                or stability.get("commit") != summary["commit"]
                or stability.get("unchanged") is not True):
            p.error("Invalid supplemental benchmark input stability record")
    if args.top < 1 or args.repeat < 1 or args.threads < 1:
        p.error("--top, --repeat, and --threads must be positive")
    sizes = json.loads((args.benchmark / "size.json").read_text())
    source_map = {row["module"]: row["source"] for row in sizes}
    modules = args.modules or [row["module"] for row in summary["timings"][:args.top]]
    if any(module not in source_map for module in modules):
        p.error("Profile scope must be owned source modules")
    output = args.output.resolve()
    if output.exists():
        p.error("Refusing to overwrite profiles")
    output.mkdir(parents=True)
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = str(args.threads)
    env["LAKE_ARTIFACT_CACHE"] = "false"
    results = []
    for module in modules:
        for repetition in range(1, args.repeat + 1):
            label = module + f"-{repetition}"
            events = output / (label + ".json")
            log = output / (label + ".log")
            resources = output / (label + ".resources.txt")
            source = str(Path(source_map[module]).relative_to("formalization"))
            source_bytes = (PROJECT / source).read_bytes()
            source_hash = hashlib.sha256(source_bytes).hexdigest()
            current_commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip()
            matches_commit = hashlib.sha256(git_source(current_commit, source)).hexdigest() == source_hash
            matches_benchmark = hashlib.sha256(git_source(summary["commit"], source)).hexdigest() == source_hash
            source_snapshot = None
            if not matches_commit:
                source_snapshot = label + ".source.lean.txt"
                (output / source_snapshot).write_bytes(source_bytes)
            setup_original = PROJECT / ".lake/build/ir" / Path(*module.split(".")).with_suffix(".setup.json")
            trace_original = PROJECT / ".lake/build/lib/lean" / Path(*module.split(".")).with_suffix(".trace")
            setup_bytes, trace_bytes = setup_original.read_bytes(), trace_original.read_bytes()
            setup = json.loads(setup_bytes)
            if setup.get("name") != module or setup.get("imports") is not None:
                p.error("Expected a matching Lake setup that lets the current source header determine imports")
            setup_snapshot, trace_snapshot = label + ".setup.json", label + ".build-trace.json"
            (output / setup_snapshot).write_bytes(setup_bytes)
            (output / trace_snapshot).write_bytes(trace_bytes)
            config_before = config_hashes()
            benchmark_configs = {"formalization/" + name: hashlib.sha256(
                git_source(summary["commit"], name)).hexdigest() for name in CONFIGS}
            if config_before != benchmark_configs:
                p.error("Profile configuration must match its benchmark commit")
            effective = effective_environment(lake, env)
            context_before, mapped_rows = import_context(lake, source, setup, effective, env)
            command = [args.time, "-v", "-o", str(resources), lake, "env", "lean",
                       "-DautoImplicit=false", "--profile", "--stats",
                       "-Dtrace.profiler=true", "-Dtrace.profiler.output.pp=true",
                       "-Dtrace.profiler.output=" + str(events),
                       "--setup", str(output / setup_snapshot), source]
            print(f"Profiling {module} ({repetition}/{args.repeat})", flush=True)
            start = datetime.now(timezone.utc).isoformat()
            clock = time.monotonic()
            with log.open("w") as stream:
                completed = subprocess.run(command, cwd=PROJECT, env=env, stdout=stream,
                                           stderr=subprocess.STDOUT)
            wall = time.monotonic() - clock
            end = datetime.now(timezone.utc).isoformat()
            # Keep partial evidence even if an input disappeared or the header
            # cannot be parsed after the timed process returns.
            source_stable = configs_stable = imports_stable = setup_stable = trace_stable = False
            context_after, guard_error = None, None
            try:
                source_stable = sha256(PROJECT / source) == source_hash
                configs_stable = config_hashes() == config_before
                context_after, _ = import_context(lake, source, setup, effective, env)
                imports_stable = context_before == context_after
                setup_stable = sha256(setup_original) == hashlib.sha256(setup_bytes).hexdigest()
                trace_stable = sha256(trace_original) == hashlib.sha256(trace_bytes).hexdigest()
            except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
                guard_error = type(error).__name__ + ": " + str(error)
            context_file = label + ".import-context.json"
            write_json(output / context_file, {"before": context_before, "after": context_after,
                "mapped_artifact_metadata_rows_before": mapped_rows,
                "notes": ["Direct artifact families are SHA-256 bound, including implicit Init.",
                          "The saved Lake setup pins its mapped transitive paths; its map is a conservative prior-build superset.",
                          "Unmapped direct imports use captured effective search-path fallback; their nonmapped transitive closure is not inventoried.",
                          "Mapped transitive artifact stability compares paths, sizes and mtimes, not every content hash.",
                          "Core fallback is identified by the Lean executable hash/version and library directory, not a complete core artifact content inventory."]})
            result = {"module": module, "repetition": repetition, "source": source,
                      "commit": current_commit, "source_sha256": source_hash,
                      "benchmark_commit": summary["commit"], "source_matches_commit": matches_commit,
                      "source_matches_benchmark": matches_benchmark, "source_snapshot": source_snapshot,
                      "environment": effective["environment"], "toolchain": effective,
                      "environment_overrides": {"LEAN_NUM_THREADS": str(args.threads), "LAKE_ARTIFACT_CACHE": "false"},
                      "environment_capture": "Selected effective Lake environment values; the complete inherited environment is not recorded.",
                      "config_sha256": config_before, "config_hashes_unchanged": configs_stable,
                      "config_matches_benchmark": True, "post_guard_error": guard_error,
                      "setup_snapshot": setup_snapshot, "setup_sha256": hashlib.sha256(setup_bytes).hexdigest(),
                      "trace_snapshot": trace_snapshot, "trace_sha256": hashlib.sha256(trace_bytes).hexdigest(),
                      "import_context": context_file, "import_context_sha256": sha256(output / context_file),
                      "source_hash_unchanged": source_stable, "import_artifacts_unchanged": imports_stable,
                      "build_setup_unchanged": setup_stable, "build_trace_unchanged": trace_stable,
                      "inputs_stable": source_stable and configs_stable and imports_stable and setup_stable and trace_stable,
                      "measurement_valid": completed.returncode == 0 and source_stable and configs_stable and imports_stable and setup_stable and trace_stable,
                      "command": command, "start_utc": start, "exit_code": completed.returncode,
                      "end_utc": end, "wall_seconds": wall,
                      "log": log.name, "events": events.name, "resources": resources.name}
            results.append(result)
            write_json(output / "profiles.json", results)
            if not result["inputs_stable"]:
                raise RuntimeError("Profile inputs changed during measurement; invalid evidence recorded: " + source)
            print(f"Finished {module}: exit {completed.returncode}, {result['wall_seconds']:.2f}s", flush=True)
            if completed.returncode:
                return completed.returncode
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
