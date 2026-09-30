#!/usr/bin/env python3
"""Check against a supplied, already compiled Mathlib dependency directory.
Usage: python3 check_local.py [--incremental] [--jobs N] [Cloning/Foo.lean ...]
Override CLONING_LEAN and CLONING_PACKAGES for a different installation.
CLONING_BUILD optionally selects an isolated local output directory.
The optional incremental mode assumes the external compiled dependencies are unchanged.
"""
from pathlib import Path
import argparse, os, re, subprocess, sys, threading
from concurrent.futures import ThreadPoolExecutor
root = Path(__file__).resolve().parent
lean = os.environ.get("CLONING_LEAN", "/Users/jw/.elan/toolchains/leanprover--lean4---v4.29.0-rc6/bin/lean")
packages = Path(os.environ.get("CLONING_PACKAGES", "/Users/jw/Downloads/continuity-of-regularized-channel-renyi-divergence/.lake/packages"))
build = Path(os.environ.get("CLONING_BUILD", str(root / "build")))
build.mkdir(exist_ok=True)
env = os.environ.copy()
env["LEAN_PATH"] = ":".join([str(build), str(root)] + [str(p) for p in packages.glob("*/.lake/build/lib/lean")])
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--incremental', action='store_true')
parser.add_argument('--jobs', type=int, default=1, help='maximum independent Lean jobs (default: 1)')
parser.add_argument('files', nargs='*')
args = parser.parse_args()
if args.jobs < 1:
    parser.error('--jobs must be at least 1')
incremental = args.incremental
requested = args.files or ['Cloning.lean']
files, seen, active, dependencies = [], set(), set(), {}
def visit(name):
    if name in seen:
        return
    if name in active:
        raise SystemExit("Import cycle at " + name)
    active.add(name)
    source = root / name
    if not source.is_file():
        raise SystemExit("Missing local source: " + str(source))
    dependencies[name] = [imported.replace('.', '/') + '.lean' for imported in
        re.findall(r"^import\s+(Cloning(?:\.\w+)?)\s*$", source.read_text(), re.M)]
    for imported in dependencies[name]:
        visit(imported)
    active.remove(name)
    seen.add(name)
    files.append(name)
for name in requested:
    visit(name)
output_lock = threading.Lock()
futures = {}
def compile_file(name):
    # Every prerequisite is earlier in the topological list and has an assigned
    # future before this task is submitted. Dependents never read partial oleans.
    for dependency in dependencies[name]:
        if futures[dependency].result() != 0:
            return 1
    target = (build / name).with_suffix(".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    if incremental and target.exists():
        prerequisites = [root / name] + [(build / dep).with_suffix('.olean')
                                        for dep in dependencies[name]]
        if all(p.exists() and p.stat().st_mtime_ns <= target.stat().st_mtime_ns
               for p in prerequisites):
            return 0
    with output_lock:
        print("CHECK", name, flush=True)
    result = subprocess.run([lean, "-DautoImplicit=false", "-o", str(target), name],
                            cwd=root, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.stdout:
        with output_lock:
            print(result.stdout, end='', flush=True)
    return result.returncode

with ThreadPoolExecutor(max_workers=args.jobs) as executor:
    for name in files:
        futures[name] = executor.submit(compile_file, name)
    exit_codes = [future.result() for future in futures.values()]
if any(exit_codes):
    sys.exit(1)
