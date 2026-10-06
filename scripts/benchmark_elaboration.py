#!/usr/bin/env python3
"""Measure a clean project-only All build; never invalidate package artifacts."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import threading
import time

REPO = Path(__file__).resolve().parents[1]
PROJECT = REPO / "formalization"


def run(*args, cwd=REPO):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def owned_sources(commit):
    names = run("git", "ls-tree", "-r", "--name-only", commit).splitlines()
    return [n for n in names if n.startswith("formalization/") and n.endswith(".lean")
            and (n.count("/") == 1 or n.startswith("formalization/Cloning/"))]


def dependency_snapshot():
    # A stat digest catches changes without adding gigabytes of read I/O to a run.
    digest = hashlib.sha256()
    count = 0
    for p in sorted((PROJECT / ".lake/packages").rglob("*")):
        if p.is_file() and ".lake/build/" in p.as_posix():
            s = p.stat()
            digest.update(f"{p.relative_to(PROJECT)}\0{s.st_size}\0{s.st_mtime_ns}\n".encode())
            count += 1
    return {"artifact_files": count, "path_size_mtime_sha256": digest.hexdigest()}


def invalidate_owned(modules):
    build = (PROJECT / ".lake/build").resolve()
    if build != PROJECT.resolve() / ".lake/build":
        raise ValueError("Refusing non-local or symlinked project build tree")
    targets = set()
    for facet in ("lib/lean", "ir"):
        base = build / facet
        for module in modules:
            relative = Path(*module.split("."))
            parent = base / relative.parent
            targets.update(parent.glob(relative.name + ".*"))
    removed = []
    for p in sorted(targets):
        if p.is_symlink() or not p.is_file() or not p.resolve().is_relative_to(build):
            raise ValueError("Unsafe project artifact: " + str(p))
        p.unlink()
        removed.append(str(p.relative_to(PROJECT)))
    return removed


def elapsed_seconds(value):
    parts = [float(x) for x in value.split(":")]
    return sum(x * 60 ** i for i, x in enumerate(reversed(parts)))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--threads", type=int, default=2)
    ap.add_argument("--size-helper", type=Path, required=True,
                    help="Pinned lean-elaboration-test count_lean_lines.py")
    ap.add_argument("--time", default="/opt/homebrew/bin/gtime")
    args = ap.parse_args()
    if args.threads < 1:
        ap.error("--threads must be positive")
    output = args.output.resolve()
    if output.exists():
        ap.error("Refusing to overwrite a measurement directory")
    commit = run("git", "rev-parse", "HEAD")
    sources = owned_sources(commit)
    changed = run("git", "diff", "HEAD", "--name-only", "--", *sources,
                  "formalization/lean-toolchain", "formalization/lakefile.toml",
                  "formalization/lake-manifest.json")
    if changed:
        ap.error("Commit measured proof/config changes first: " + changed)
    modules = [str(Path(s).relative_to("formalization").with_suffix("")).replace("/", ".")
               for s in sources]
    if "All" not in modules or "Cloning" not in modules:
        ap.error("Unexpected module scope")
    output.mkdir(parents=True)
    spec = importlib.util.spec_from_file_location("skill_counter", args.size_helper.resolve())
    counter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(counter)
    size = []
    graph = {}
    for source, module in zip(sources, modules):
        text = subprocess.check_output(["git", "show", f"{commit}:{source}"], cwd=REPO, text=True)
        _, flags = counter.code_line_flags(text)
        size.append({"module": module, "source": source, "lines": len(text.splitlines()),
                     "code_lines": sum(flags), "module_header": counter.has_module_header(text)})
        graph[module] = [m for m in re.findall(r"^import\s+(\S+)", text, re.M) if m in modules]
    reachable = set()
    def visit(m):
        if m not in reachable:
            reachable.add(m)
            for dependency in graph[m]:
                visit(dependency)
    visit("All")
    if reachable != set(modules):
        ap.error("All does not cover owned source scope")
    write_json(output / "size.json", size)
    write_json(output / "imports.json", graph)
    (output / "skill-size.txt").write_text(run("python3", str(args.size_helper.resolve()), commit,
                                             *sources) + "\n")
    before = dependency_snapshot()
    write_json(output / "dependencies-before.json", before)
    removed = invalidate_owned(modules)
    write_json(output / "invalidated.json", removed)
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = str(args.threads)
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    command = [args.time, "-v", "-o", str(output / "resources.txt"), lake,
               "--no-ansi", "--no-cache", "build", "All"]
    start = datetime.now(timezone.utc).isoformat()
    samples = []
    stop = threading.Event()
    def sample():
        while not stop.is_set():
            listing = run("ps", "-axo", "pid,etime,time,%cpu,command")
            samples.append({"utc": datetime.now(timezone.utc).isoformat(),
                            "processes": [line for line in listing.splitlines()
                                          if re.search(r"(?:/|\s)(?:lean|lake)(?:\s|$)", line)]})
            stop.wait(10)
    monitor = threading.Thread(target=sample, daemon=True)
    monitor.start()
    timed_start = time.monotonic()
    proc = subprocess.Popen(command, cwd=PROJECT, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, start_new_session=True,
                            bufsize=1)
    forbidden = []
    with (output / "build.log").open("w") as log:
        for line in proc.stdout:
            log.write(line)
            log.flush()
            match = re.search(r"(?:Built|Replayed)\s+(\S+)", line)
            if match and match[1].split(":")[0] not in modules:
                # Replayed cached upstream jobs are harmless; Built is compilation.
                if "Built " in line:
                    forbidden.append(line.strip())
                    os.killpg(proc.pid, signal.SIGTERM)
            if "Built " in line and ("All " in line or re.search(r"\((?:[3-9]\d|\d{3,})", line)):
                print(line.rstrip(), flush=True)
    status = proc.wait()
    wall = time.monotonic() - timed_start
    stop.set()
    monitor.join()
    end = datetime.now(timezone.utc).isoformat()
    after = dependency_snapshot()
    write_json(output / "dependencies-after.json", after)
    write_json(output / "process-samples.json", samples)
    log = (output / "build.log").read_text()
    timings = [{"module": m, "seconds": float(s)} for m, s in
               re.findall(r"Built\s+(\S+)\s+\(([\d.]+)s\)", log) if m in modules]
    timings.sort(key=lambda row: row["seconds"], reverse=True)
    resources = {}
    for line in (output / "resources.txt").read_text().splitlines():
        if ": " in line:
            key, value = line.strip().rsplit(": ", 1)
            resources[key] = value
    duration = {r["module"]: r["seconds"] for r in timings}
    chains = {}
    def critical(m):
        if m not in chains:
            prior = max((critical(d) for d in graph[m]), key=lambda x: x[0], default=(0, []))
            chains[m] = (prior[0] + duration.get(m, 0), [*prior[1], m])
        return chains[m]
    summary = {"schema": "cloning-elaboration-test-v1", "commit": commit, "start_utc": start,
               "end_utc": end, "command": command, "environment": {"LEAN_NUM_THREADS": str(args.threads)},
               "host": run("uname", "-a"), "cpu_count": os.cpu_count(),
               "memory_bytes": run("sysctl", "-n", "hw.memsize"),
               "lean": run(lake, "env", "lean", "--version", cwd=PROJECT),
               "lake": run(lake, "--version", cwd=PROJECT),
               "time_tool": run(args.time, "--version"), "exit_code": status,
               "wall_seconds_observed": wall, "resources": resources,
               "dependency_artifacts_unchanged": before == after,
               "upstream_compilations": forbidden, "module_count": len(modules),
               "total_lines": sum(x["lines"] for x in size),
               "code_lines": sum(x["code_lines"] for x in size),
               "legacy_header_files": sum(not x["module_header"] for x in size),
               "timings": timings, "logged_job_seconds": sum(x["seconds"] for x in timings),
               "critical_path_logged_lower_bound": critical("All"),
               "heavy_tiers": {str(t): sum(x["seconds"] >= t for x in timings) for t in (10, 20, 30, 40)},
               "warnings": len(re.findall(r"^warning:", log, re.M)),
               "errors": len(re.findall(r"^error:", log, re.M)),
               "sorry_messages": len(re.findall(r"declaration uses.*sorry", log)),
               "lake_jobs": max((int(n) for n in re.findall(r"\[\d+/(\d+)\]", log)), default=0)}
    write_json(output / "summary.json", summary)
    print(json.dumps({k: summary[k] for k in ("commit", "exit_code", "wall_seconds_observed",
          "module_count", "logged_job_seconds", "heavy_tiers", "dependency_artifacts_unchanged")}))
    return 0 if status == 0 and before == after and not forbidden else 1


if __name__ == "__main__":
    raise SystemExit(main())
