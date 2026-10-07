#!/usr/bin/env python3
"""Pinned comparator reproduction; does not mutate the audited source tree.

The default Linux mode uses actual landrun. --trusted-local is a deliberately
labelled alternative for a self-built trusted tree (also usable on macOS).
Neither a configuration check nor a wrapper build is a comparator verdict.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LOCK_PATH = ROOT / "verification/tools-lock.json"


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def read_json(path):
    return json.loads(Path(path).read_text())


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def capture(args, cwd=None, env=None):
    return subprocess.check_output([str(x) for x in args], cwd=cwd, env=env,
                                   text=True, stderr=subprocess.STDOUT).strip()


def run(args, cwd=None, env=None, log=None):
    print("+ " + " ".join(str(x) for x in args), flush=True)
    if log is None:
        subprocess.run([str(x) for x in args], cwd=cwd, env=env, check=True)
    else:
        with Path(log).open("w") as f:
            subprocess.run([str(x) for x in args], cwd=cwd, env=env,
                           stdout=f, stderr=subprocess.STDOUT, check=True)


def validate_sources(lock):
    audit_path = ROOT / lock["audit"]["run_file"]
    require(digest(audit_path) == lock["audit"]["run_sha256"], "pinned audit record changed")
    audit = read_json(audit_path)
    require(audit["status"] == "passed", "source inventory is not from a passed audit")
    actual_paths = {*ROOT.glob("*.lean"), *(ROOT / "Cloning").rglob("*.lean"),
                    ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json"}
    actual = {p.relative_to(ROOT).as_posix(): digest(p) for p in sorted(actual_paths)}
    require(actual == audit["input_sha256"], "proof sources/config differ from the pinned audited snapshot")
    require((ROOT / "lean-toolchain").read_text().strip() == lock["lean_toolchain"], "Lean toolchain mismatch")
    return audit


def validate_config(lock):
    audit = validate_sources(lock)
    claims = read_json(HERE / "claims.json")["claims"]
    names = [c["name"] for c in claims]
    require(len(claims) == 27 and len(set(names)) == 27, "expected 27 distinct named manuscript claims")
    config = read_json(HERE / "config.json")
    require(config == {"challenge_module": "Challenge", "solution_module": "Solution",
                       "theorem_names": names, "permitted_axioms": lock["permitted_axioms"],
                       "enable_nanoda": False}, "comparator config differs from the pinned interface")
    require(lock["comparator_inputs"], "challenge snapshot has not been pinned")
    for relative, expected in lock["comparator_inputs"].items():
        require(digest(HERE / relative) == expected, "comparator input changed: " + relative)
    challenge = (HERE / "Challenge.lean").read_text()
    solution = (HERE / "Solution.lean").read_text()
    require("import Solution" not in challenge, "challenge must not import its solution")
    require(not re.search(r"\b(sorry|admit|axiom)\b", re.sub(r"/-.*?-/|--[^\n]*", "", solution, flags=re.S)),
            "solution contains a placeholder or custom axiom")
    for c in claims:
        short = c["name"].rsplit(".", 1)[-1]
        require(re.search(r"\btheorem\s+" + re.escape(short) + r"\b", challenge), "missing challenge: " + short)
        require(re.search(r"\btheorem\s+" + re.escape(short) + r"\b", solution), "missing solution: " + short)
    return audit


def lake_path(option):
    candidate = option or os.environ.get("LAKE") or shutil.which("lake")
    if not candidate:
        candidate = str(Path.home() / ".elan/bin/lake")
    require(Path(candidate).is_file(), "Lake missing; set LAKE to the installed elan lake executable")
    return str(Path(candidate).absolute())


def prerequisite_report(lock, args):
    failures = []
    if not shutil.which("git"):
        failures.append("git is required")
    try:
        lake = lake_path(args.lake)
    except RuntimeError as e:
        lake = None
        failures.append(str(e))
    if not args.trusted_local:
        if platform.system() != "Linux":
            failures.append("sandboxed comparator requires Linux with Landlock; use a Linux host/VM, or explicitly select --trusted-local")
        if hasattr(os, "geteuid") and os.geteuid() == 0:
            failures.append("sandboxed comparator must run as an unprivileged user")
        if not shutil.which("go"):
            failures.append("Go " + lock["tools"]["landrun"]["go_toolchain"] + " required to build pinned landrun")
    if not (ROOT / ".lake/build/lib/lean/Cloning.olean").is_file():
        failures.append("project not built: run pinned Lake build All first")
    return {"platform": platform.system(), "python": platform.python_version(), "lake": lake,
            "mode": "trusted-local-no-sandbox" if args.trusted_local else "linux-landrun",
            "network": "not probed; setup requires GitHub and Go module network access",
            "blockers": failures}


def validate_dependencies():
    """Check trusted statement-import sources against the frozen Lake manifest."""
    for package in read_json(ROOT / "lake-manifest.json")["packages"]:
        path = ROOT / ".lake/packages" / package["name"]
        require(capture(["git", "-C", path, "rev-parse", "HEAD"]) == package["rev"],
                "dependency checkout differs from manifest: " + package["name"])
        require(not capture(["git", "-C", path, "status", "--porcelain", "--untracked-files=no"]),
                "tracked dependency source modified: " + package["name"])


def checkout(work, name, pin):
    target = work / "sources" / name
    if not target.exists():
        target.mkdir(parents=True)
        run(["git", "init", target])
        run(["git", "-C", target, "remote", "add", "origin", pin["repository"]])
        run(["git", "-C", target, "fetch", "--depth", "1", "origin", pin["commit"]])
        run(["git", "-C", target, "checkout", "--detach", "FETCH_HEAD"])
    require(capture(["git", "-C", target, "rev-parse", "HEAD"]) == pin["commit"], "wrong source revision: " + name)
    require(not capture(["git", "-C", target, "status", "--porcelain", "--untracked-files=no"]),
            "tracked upstream source modified: " + name)
    return target


def setup(lock, args, work, lake):
    # The checked-out source trees stay untouched. Only the comparator build
    # copy gets a generated Lake config with immutable local dependencies.
    exporter = checkout(work, "lean4export", lock["tools"]["lean4export"])
    checker = checkout(work, "lean4checker", lock["tools"]["lean4checker"])
    comparator = checkout(work, "comparator", lock["tools"]["comparator"])
    for path in (exporter, comparator):
        require((path / "lean-toolchain").read_text().strip() == lock["lean_toolchain"], "upstream toolchain mismatch")
    build = work / "comparator-build"
    expected_lakefile = (
        'name = "Comparator"\nversion = "0.1.0"\ndefaultTargets = ["comparator"]\n\n'
        '[[lean_lib]]\nname = "Comparator"\n\n[[lean_exe]]\nname = "comparator"\nroot = "Main"\n\n'
        '[[require]]\nname = "Lean4Checker"\npath = ' + json.dumps(str(checker)) + '\n\n'
        '[[require]]\nname = "lean4export"\npath = ' + json.dumps(str(exporter)) + '\n')
    if not build.exists():
        shutil.copytree(comparator, build, ignore=shutil.ignore_patterns(".git", ".lake"))
        manifest = build / "lake-manifest.json"
        if manifest.exists():
            manifest.unlink()
        (build / "lakefile.toml").write_text(expected_lakefile)
    require((build / "lakefile.toml").read_text() == expected_lakefile, "comparator build configuration altered")
    require((build / "lean-toolchain").read_text().strip() == lock["lean_toolchain"], "comparator build toolchain altered")
    for source in comparator.rglob("*.lean"):
        if ".lake" not in source.parts:
            require(digest(source) == digest(build / source.relative_to(comparator)), "comparator Lean source altered")
    run([lake, "build", "lean4export"], cwd=exporter)
    run([lake, "build", "comparator"], cwd=build)
    bindir = work / "bin"
    bindir.mkdir(exist_ok=True)
    binaries = {"lean4export": exporter / ".lake/build/bin/lean4export",
                "comparator": build / ".lake/build/bin/comparator"}
    if args.trusted_local:
        binaries["landrun"] = HERE / "trusted-landrun.py"
    else:
        require(capture(["go", "version"]).split()[2] == lock["tools"]["landrun"]["go_toolchain"], "Go compiler does not match lock")
        landrun = checkout(work, "landrun", lock["tools"]["landrun"])
        env = dict(os.environ, GOTOOLCHAIN="local", GOFLAGS="-mod=readonly")
        run(["go", "build", "-trimpath", "-o", bindir / "landrun.real", "./cmd/landrun"], cwd=landrun, env=env)
        binaries["landrun"] = bindir / "landrun.real"
    for name, target in binaries.items():
        link = bindir / name
        if link.is_symlink():
            link.unlink()
        require(not link.exists(), "refusing to replace existing binary: " + str(link))
        link.symlink_to(target)
    return binaries


def prepare(work, lock):
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    wrapper = work / "runs" / stamp
    lib = wrapper / ".lake/build/lib/lean"
    lib.mkdir(parents=True)
    for name in ("Challenge.lean", "Solution.lean", "CheckTypes.lean", "lakefile.toml", "config.json"):
        shutil.copyfile(HERE / name, wrapper / name)
    (wrapper / "lean-toolchain").write_text(lock["lean_toolchain"] + "\n")
    roots = [ROOT / ".lake/build/lib/lean"]
    roots.extend(ROOT / ".lake/packages" / p["name"] / ".lake/build/lib/lean"
                 for p in read_json(ROOT / "lake-manifest.json")["packages"])
    for root in roots:
        # Some manifest dependencies serve tools that the proof never imports
        # (e.g. Cli), and thus need not have any compiled library directory.
        if not root.is_dir():
            continue
        for source in sorted(root.iterdir()):
            target = lib / source.name
            if target.exists() or target.is_symlink():
                require(target.resolve() == source.resolve(), "compiled-library root collision: " + str(source))
            else:
                target.symlink_to(source.resolve())
    return wrapper


def compiled_hashes(audit):
    # Platform-specific .olean hashes are recorded, not compared with a Mac
    # audit on Linux. They must remain unchanged throughout this run.
    return {name: digest(ROOT / ".lake/build/lib/lean" / name)
            for name in audit["compiled_artifact_sha256"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", nargs="?", choices=("validate", "preflight", "setup", "prepare", "run"), default="run")
    parser.add_argument("--work", type=Path, default=HERE / ".work")
    parser.add_argument("--lake", help="absolute elan lake path; also accepts LAKE")
    parser.add_argument("--trusted-local", action="store_true", help="explicitly disable the Linux sandbox for a trusted, already-built local tree")
    args = parser.parse_args()
    lock = read_json(LOCK_PATH)
    audit = validate_config(lock)
    if args.command == "validate":
        print(json.dumps({"status": "configuration-valid", "claims": 27,
                          "source_snapshot_matches": True, "comparator_executed": False}, indent=2))
        return
    report = prerequisite_report(lock, args)
    if args.command == "preflight":
        print(json.dumps(report, indent=2))
        require(not report["blockers"], "prerequisites missing; no checker was run")
        return
    require(not report["blockers"], "\n".join(report["blockers"]))
    validate_dependencies()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    lake = report["lake"]
    if args.command == "prepare":
        print(prepare(work, lock))
        return
    if args.command == "setup":
        setup(lock, args, work, lake)
        print("Pinned tools built. No comparator verdict has been produced.")
        return
    wrapper = prepare(work, lock)
    record = {"status": "running", "started_utc": datetime.now(timezone.utc).isoformat(),
              "mode": report["mode"], "phase": "setup", "comparator_executed": False,
              "lock_sha256": digest(LOCK_PATH), "source_audit_sha256": lock["audit"]["run_sha256"],
              "wrapper_sha256": {name: digest(wrapper / name) for name in
                                  ("Challenge.lean", "Solution.lean", "CheckTypes.lean", "lakefile.toml", "config.json", "lean-toolchain")},
              "runner_sha256": digest(Path(__file__)),
              "compiled_before": compiled_hashes(audit)}
    write_json(wrapper / "run.json", record)
    try:
        binaries = setup(lock, args, work, lake)
        record["binary_sha256"] = {name: digest(path) for name, path in binaries.items()}
        record["phase"] = "comparison"
        write_json(wrapper / "run.json", record)
        env = dict(os.environ)
        env.pop("LEAN_PATH", None)
        env["PATH"] = str(work / "bin") + os.pathsep + str(Path(lake).parent) + os.pathsep + env.get("PATH", "")
        env["LEAN_ABORT_ON_PANIC"] = "1"
        if not args.trusted_local:
            # Pinned comparator itself uses --best-effort. Require an actual
            # denied write to a read-only scratch file before accepting this
            # as a sandboxed run; a no-op/fake landrun cannot pass.
            probe = wrapper / "sandbox-probe"
            probe.write_text("read-only\n")
            cmd = [work / "bin/landrun", "--best-effort", "--ro", "/", "--rw", "/dev", "-ldd", "-add-exec",
                   shutil.which("python3"), "-c", "import pathlib,sys\ntry: pathlib.Path(sys.argv[1]).write_text('escaped')\nexcept PermissionError: sys.exit(73)", probe]
            result = subprocess.run([str(x) for x in cmd], env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            (wrapper / "sandbox-probe.log").write_text(result.stdout)
            require(result.returncode == 73 and probe.read_text() == "read-only\n", "landrun failed the denied-write probe")
        record["comparator_executed"] = True
        run([lake, "env", work / "bin/comparator", "config.json"], cwd=wrapper, env=env, log=wrapper / "comparator.log")
        require("Your solution is okay!" in (wrapper / "comparator.log").read_text(), "missing comparator success marker")
        validate_config(lock)
        validate_dependencies()
        require(digest(LOCK_PATH) == record["lock_sha256"], "tool lock changed during verification")
        require(digest(Path(__file__)) == record["runner_sha256"], "runner changed during verification")
        require({name: digest(path) for name, path in binaries.items()} == record["binary_sha256"],
                "tool binary changed during verification")
        require({name: digest(wrapper / name) for name in record["wrapper_sha256"]} == record["wrapper_sha256"],
                "wrapper input changed during verification")
        require(compiled_hashes(audit) == record["compiled_before"], "project artifacts changed during verification")
        record.update(status="passed", comparator_verdict="Your solution is okay!")
    except BaseException as error:
        record.update(status="failed", error=str(error))
        raise
    finally:
        record["completed_utc"] = datetime.now(timezone.utc).isoformat()
        write_json(wrapper / "run.json", record)
        print("Evidence: " + str(wrapper), flush=True)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print("ERROR: " + str(error), file=sys.stderr)
        sys.exit(2)
