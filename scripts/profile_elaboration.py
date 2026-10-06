#!/usr/bin/env python3
"""Serial warm profiles of owned modules from a completed elaboration test."""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

REPO = Path(__file__).resolve().parents[1]
PROJECT = REPO / "formalization"


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
    if summary["exit_code"] != 0 or not summary["dependency_artifacts_unchanged"]:
        p.error("A successful project-only benchmark is required")
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
    results = []
    for module in modules:
        for repetition in range(1, args.repeat + 1):
            label = module + f"-{repetition}"
            events = output / (label + ".json")
            log = output / (label + ".log")
            resources = output / (label + ".resources.txt")
            source = str(Path(source_map[module]).relative_to("formalization"))
            command = [args.time, "-v", "-o", str(resources), lake, "env", "lean",
                       "-DautoImplicit=false", "--profile",
                       "-Dtrace.profiler.output=" + str(events), source]
            print(f"Profiling {module} ({repetition}/{args.repeat})", flush=True)
            start = datetime.now(timezone.utc).isoformat()
            clock = time.monotonic()
            with log.open("w") as stream:
                completed = subprocess.run(command, cwd=PROJECT, env=env, stdout=stream,
                                           stderr=subprocess.STDOUT)
            result = {"module": module, "repetition": repetition, "source": source,
                      "command": command, "start_utc": start, "exit_code": completed.returncode,
                      "wall_seconds": time.monotonic() - clock,
                      "log": log.name, "events": events.name, "resources": resources.name}
            results.append(result)
            (output / "profiles.json").write_text(json.dumps(results, indent=2) + "\n")
            print(f"Finished {module}: exit {completed.returncode}, {result['wall_seconds']:.2f}s", flush=True)
            if completed.returncode:
                return completed.returncode
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
