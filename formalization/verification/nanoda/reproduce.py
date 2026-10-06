#!/usr/bin/env python3
"""Pinned, fail-closed Nanoda reproduction; default mode is a local preflight."""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent.parent
sys.path.insert(0, str(PROJECT / "scripts"))
from check_checkpoint import shared_inventory

LOCK_PATH = HERE.parent / "tools-lock.json"
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
# Lean comparator v4.29.0-rc6's primitive and Nanoda builtin targets.
BUILTINS = """Nat String String.mk Char Char.ofNat List Quot Quot.mk Quot.lift
Quot.ind Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble
Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList""".split()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def locate_tool(name: str) -> str | None:
    found = shutil.which(name)
    if found:
        return found
    directory = ".elan/bin" if name == "lake" else ".cargo/bin"
    candidate = Path.home() / directory / name
    return str(candidate) if candidate.is_file() and os.access(candidate, os.X_OK) else None


def bound_inventory(lock: dict) -> tuple[list[str], dict]:
    """Use the complete saved environment inventory, bound to current sources."""
    run_path = PROJECT / lock["audit"]["run_file"]
    require(sha256(run_path) == lock["audit"]["run_sha256"], "pinned audit run hash changed")
    run = read_json(run_path)
    require(run["status"] == "passed" and run["returncode"] == 0,
            "the bound audit did not pass")
    for relative, expected in run["input_sha256"].items():
        path = PROJECT / relative
        require(path.is_file() and sha256(path) == expected,
                f"audited input drift: {relative}; obtain and pin a fresh full audit")
    proof_files = {str(path.relative_to(PROJECT)) for path in PROJECT.glob("*.lean")} | {
        str(path.relative_to(PROJECT)) for path in (PROJECT / "Cloning").rglob("*.lean")
    } | {"lean-toolchain", "lakefile.toml", "lake-manifest.json"}
    require(proof_files == set(run["input_sha256"]), "project input set changed since bound audit")
    details = {}
    if run.get("audit_engine") == "shared":
        inventory = shared_inventory(run_path.parent, run)
        evidence = run_path.parent / "audit-inventory.json"
        inventories = {item["module"]: [constant["name"] for constant in item["constants"]]
                       for item in inventory["modules"]}
        roots = [item["name"] for item in inventory["declarations"]]
        details = {"inventory_format": inventory["audit_schema"],
                   "axiom_report_scope": "aggregate union; no per-root axiom attribution",
                   "aggregate_axioms": inventory["aggregate_axioms"]}
    else:
        require(run.get("audit_engine") in (None, "historical"), "unknown bound audit engine")
        evidence = run_path.parent / "AXIOMS.txt"
        require(sha256(evidence) == run["evidence_sha256"]["AXIOMS.txt"],
                "bound AXIOMS.txt hash changed")
        inventories, reports = {}, set()
        with evidence.open(encoding="utf-8") as stream:
            for line in stream:
                if line.startswith("SHARD_INVENTORY "):
                    item = json.loads(line.removeprefix("SHARD_INVENTORY "))
                    module, names = item["module"], item["constant_names"]
                    require(module == "Cloning" or module.startswith("Cloning."),
                            f"unexpected inventory module: {module}")
                    require(module not in inventories or inventories[module] == names,
                            f"conflicting module inventory: {module}")
                    inventories[module] = names
                elif line.startswith("AXIOM_REPORT "):
                    item = json.loads(line.removeprefix("AXIOM_REPORT "))
                    require(set(item["axioms"]) <= STANDARD_AXIOMS,
                            f"unpermitted axiom in archived report: {item['name']}")
                    reports.add(item["name"])
        roots = sorted({name for names in inventories.values() for name in names})
        require(set(roots) == reports, "audit roots differ from axiom report coverage")
    require(len(roots) == lock["audit"]["constants"] == run["audited_constants"],
            "audit declaration count mismatch")
    # The audit's module count excludes the umbrella Cloning module.
    require(len(set(inventories) - {"Cloning"}) == lock["audit"]["modules"],
            "audit module count mismatch")
    require(all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name) for name in roots),
            "new escaped/unusual Lean names need an explicit name-serialization review")
    return roots, {"run_sha256": sha256(run_path), "inventory_sha256": sha256(evidence),
                   "modules": len(set(inventories) - {"Cloning"}),
                   "project_declarations": len(roots), "source_binding": "matched",
                   "input_sha256": run["input_sha256"], **details}


def validate_config(config: dict, lock: dict) -> None:
    require(set(config["permitted_axioms"]) == STANDARD_AXIOMS == set(lock["permitted_axioms"]),
            "axiom allowlist must be exactly propext, Quot.sound, Classical.choice")
    require(config.get("unpermitted_axiom_hard_error") is True,
            "unpermitted axioms must cause a hard error")
    require(config.get("unsafe_permit_all_axioms") is False, "permissive axioms forbidden")
    require(config.get("use_stdin") is False, "this runner checks a hashed export file")
    require(config.get("print_success_message") is True, "checker success message required")
    require(config.get("pp_declars") == [], "pretty printing is outside this check")
    require(config.get("print_axioms") is not True or
            (config.get("pp_to_stdout") is True and not config.get("pp_output_path")),
            "axiom reporting requires stdout as its output destination")
    require(config.get("nat_extension") is True and config.get("string_extension") is True,
            "Lean Nat and String kernel extensions required")


def scan_export(path: Path, roots: set[str], lock: dict) -> dict:
    """Check root coverage and the explicit axiom policy; Nanoda checks all terms."""
    names = {0: ""}
    declarations, axioms = set(), set()
    counts = Counter()
    meta = None
    with path.open(encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, 1):
            item = json.loads(line)
            require(isinstance(item, dict), f"invalid export record at line {line_number}")
            if "meta" in item:
                require(line_number == 1 and meta is None, "export metadata must be first and unique")
                meta = item["meta"]
                require(meta["format"]["version"] == lock["export_format"], "export format mismatch")
                expected_lean = lock["lean_toolchain"].split(":v", 1)[1]
                require(meta["lean"]["version"] == expected_lean, "export Lean version mismatch")
            elif "in" in item:
                idx = item["in"]
                require(idx not in names, "duplicate name index")
                part = item.get("str", item.get("num"))
                require(part is not None and part["pre"] in names, "invalid name predecessor")
                prefix = names[part["pre"]]
                suffix = part["str"] if "str" in part else str(part["i"])
                names[idx] = prefix + ("." if prefix else "") + suffix
            else:
                entries = []
                for kind in ("axiom", "def", "thm", "opaque", "quot"):
                    if kind in item:
                        entries.append((kind, item[kind]))
                if "inductive" in item:
                    for kind in ("types", "ctors", "recs"):
                        entries.extend((kind, value) for value in item["inductive"][kind])
                for kind, declaration in entries:
                    name = names[declaration["name"]]
                    require(name not in declarations, f"duplicate exported declaration: {name}")
                    require(not declaration.get("isUnsafe", False), f"unsafe declaration: {name}")
                    require(declaration.get("safety", "safe") == "safe", f"unsafe/partial def: {name}")
                    declarations.add(name)
                    counts[kind] += 1
                    if kind == "axiom":
                        require(name in STANDARD_AXIOMS, f"unpermitted exported axiom: {name}")
                        axioms.add(name)
    require(meta is not None, "missing export metadata")
    missing = roots - declarations
    require(not missing, f"export omitted {len(missing)} requested roots: {sorted(missing)[:10]}")
    return {"metadata": meta, "sha256": sha256(path), "bytes": path.stat().st_size,
            "declarations": len(declarations), "declaration_kinds": dict(counts),
            "requested_roots": len(roots), "missing_roots": [], "axioms": sorted(axioms)}


def command(argv: list[str], cwd: Path, output: Path, *, env=None,
            error_output: Path | None = None) -> None:
    print(f"{utc()} running {argv[0]} {' '.join(argv[1:4])}; log: {output}", flush=True)
    with output.open("wb") as out:
        if error_output is None:
            result = subprocess.run(argv, cwd=cwd, env=env, stdout=out, stderr=subprocess.STDOUT)
        else:
            with error_output.open("wb") as err:
                result = subprocess.run(argv, cwd=cwd, env=env, stdout=out, stderr=err)
    require(result.returncode == 0, f"command exited {result.returncode}; see {output}")


def git_value(path: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(path), *args], text=True).strip()


def checkout(pin: dict, destination: Path, output: Path) -> Path:
    require(re.fullmatch(r"[0-9a-f]{40}", pin["commit"]) is not None, "invalid tool commit")
    if not destination.exists():
        destination.parent.mkdir(parents=True, exist_ok=True)
        command(["git", "clone", "--no-checkout", pin["repository"], str(destination)],
                destination.parent, output / f"{destination.name}-clone.log")
        command(["git", "checkout", "--detach", pin["commit"]], destination,
                output / f"{destination.name}-checkout.log")
    require(git_value(destination, "rev-parse", "HEAD") == pin["commit"],
            f"wrong checkout commit: {destination}")
    require(not git_value(destination, "status", "--porcelain", "--untracked-files=all"),
            f"modified/untracked tool source: {destination}")
    return destination


def dependency_sources() -> dict:
    manifest = read_json(PROJECT / "lake-manifest.json")
    records = {}
    for package in manifest["packages"]:
        require(package["type"] == "git", "unreviewed non-Git dependency in lake manifest")
        source = PROJECT / manifest["packagesDir"] / package["name"]
        require(source.is_dir(), f"missing dependency checkout: {source}; initialize Lake dependencies")
        actual = git_value(source, "rev-parse", "HEAD")
        require(actual == package["rev"], f"dependency commit drift: {package['name']}")
        require(not git_value(source, "status", "--porcelain", "--untracked-files=no"),
                f"modified tracked dependency source: {package['name']}")
        records[package["name"]] = {"commit": actual, "tracked_source_clean": True}
    return records


def compiled_hashes() -> dict:
    base = PROJECT / ".lake/build/lib/lean"
    paths = [base / "Cloning.olean"] + sorted((base / "Cloning").rglob("*.olean"))
    require(paths[0].is_file(), "missing built Cloning.olean")
    return {str(path.relative_to(base)): sha256(path) for path in paths}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", action="store_true", help="perform network setup, build, export and check")
    parser.add_argument("--preflight", action="store_true", help="local-only preflight (the default)")
    parser.add_argument("--work", type=Path, default=HERE / ".work")
    parser.add_argument("--threads", type=int, default=1, help="Nanoda checker threads; default 1")
    args = parser.parse_args()
    require(not (args.run and args.preflight), "choose --run or --preflight")
    require(args.threads > 0, "threads must be positive")
    work = args.work.resolve()
    output = work / ("run-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ"))
    output.mkdir(parents=True, exist_ok=False)
    state = {"status": "running", "started_utc": utc(), "mode": "run" if args.run else "preflight",
             "independent_kernel_check": "not_run", "output": str(output)}
    write_json(output / "run.json", state)
    try:
        lock = read_json(LOCK_PATH)
        config = read_json(HERE / "nanoda-config.json")
        validate_config(config, lock)
        require((PROJECT / "lean-toolchain").read_text().strip() == lock["lean_toolchain"],
                "project Lean pin differs from tools lock")
        require(lock["tools"]["nanoda"]["patches"] == [], "Nanoda kernel patches forbidden")
        project_roots, binding = bound_inventory(lock)
        roots = sorted(set(project_roots) | set(BUILTINS) | STANDARD_AXIOMS)
        (output / "roots.txt").write_text("\n".join(roots) + "\n", encoding="utf-8")
        write_json(output / "binding.json", binding)
        files = [LOCK_PATH, Path(__file__), HERE / "ExportCloning.lean", HERE / "nanoda-config.json",
                 PROJECT / "scripts/check_checkpoint.py", PROJECT / "scripts/shared_audit.py"]
        harness_hashes = {str(p): sha256(p) for p in files}
        state.update({"tools_lock_sha256": sha256(LOCK_PATH), "harness_sha256": harness_hashes,
                      "tools": lock["tools"], "project_declarations": len(project_roots),
                      "modules": binding["modules"], "roots_sha256": sha256(output / "roots.txt"),
                      "source_binding": "matched", "axiom_policy": "strict_standard_three"})
        executables = {tool: locate_tool(tool) for tool in ("git", "lake", "rustup", "cargo")}
        missing = [tool for tool, path in executables.items() if path is None]
        state["executables"] = executables
        state["missing_prerequisites"] = missing
        state["network_access"] = "not_tested"
        if not args.run:
            state["status"] = "blocked" if missing else "ready_not_run"
            state["note"] = "Local source/configuration preflight only; no exporter or Nanoda execution."
            return 2 if missing else 0
        require(not missing, "missing executables: " + ", ".join(missing))
        env = os.environ.copy()
        env["PATH"] = os.pathsep.join(dict.fromkeys(
            [str(Path(path).parent) for path in executables.values() if path] +
            env.get("PATH", "").split(os.pathsep)))
        # Prevent a caller's search path from shadowing the pinned proof dependencies.
        env.pop("LEAN_PATH", None)
        env["LEAN_ABORT_ON_PANIC"] = "1"
        rust = lock["tools"]["nanoda"]["rust_toolchain"]
        command(["rustup", "run", rust, "rustc", "--version", "--verbose"], PROJECT,
                output / "rust-version.log", env=env)
        command(["lake", "env", "lean", "--version"], PROJECT, output / "lean-version.log", env=env)
        require(lock["lean_toolchain"].split(":v")[1] in (output / "lean-version.log").read_text(),
                "effective Lean version differs from locked toolchain")
        state["dependency_sources"] = dependency_sources()
        exporter = checkout(lock["tools"]["lean4export"], work / "src/lean4export", output)
        nanoda = checkout(lock["tools"]["nanoda"], work / "src/nanoda", output)
        require((exporter / "lean-toolchain").read_text().strip() == lock["lean_toolchain"],
                "exporter toolchain differs from project")
        state["phase"] = "build"
        write_json(output / "run.json", state)
        command(["lake", "build"], exporter, output / "exporter-build.log", env=env)
        command(["rustup", "run", rust, "cargo", "build", "--release", "--locked"], nanoda,
                output / "nanoda-build.log", env=env)
        command(["lake", "build", "All"], PROJECT, output / "project-build.log", env=env)
        bound_inventory(lock)
        require(dependency_sources() == state["dependency_sources"], "dependency sources changed during build")
        artifacts = compiled_hashes()
        write_json(output / "compiled-before.json", artifacts)
        export_path = output / "cloning.ndjson"
        # Lake appends the incoming LEAN_PATH to its project/dependency paths.
        export_env = dict(env, LEAN_PATH=str(exporter / ".lake/build/lib/lean"))
        state["phase"] = "export"
        write_json(output / "run.json", state)
        command(["lake", "env", "lean", "--run", str(HERE / "ExportCloning.lean"),
                 str(output / "roots.txt")], PROJECT, export_path, env=export_env,
                error_output=output / "export.stderr")
        export_report = scan_export(export_path, set(roots), lock)
        write_json(output / "export.json", export_report)
        config.update(export_file_path=str(export_path), num_threads=args.threads)
        validate_config(config, lock)
        write_json(output / "nanoda-config.json", config)
        binary = nanoda / "target/release/nanoda_bin"
        state.update(phase="check", export_sha256=export_report["sha256"],
                     checker_binary_sha256=sha256(binary), independent_kernel_check="running",
                     checker_config_sha256=sha256(output / "nanoda-config.json"))
        write_json(output / "run.json", state)
        command([str(binary), str(output / "nanoda-config.json")], output,
                output / "nanoda.stdout", env=env, error_output=output / "nanoda.stderr")
        stdout = (output / "nanoda.stdout").read_text(encoding="utf-8")
        successes = re.findall(r"^Checked (\d+) declarations with no errors$", stdout, re.MULTILINE)
        require(len(successes) == 1, "Nanoda did not emit an unqualified success message")
        require(int(successes[0]) == export_report["declarations"],
                "Nanoda checked declaration count differs from exported declaration coverage")
        require(sha256(export_path) == export_report["sha256"], "export changed during checking")
        require(sha256(binary) == state["checker_binary_sha256"], "checker binary changed during checking")
        require(sha256(output / "nanoda-config.json") == state["checker_config_sha256"],
                "checker configuration changed during checking")
        require(sha256(output / "roots.txt") == state["roots_sha256"], "export roots changed during checking")
        require(compiled_hashes() == artifacts, "compiled project changed during checking")
        bound_inventory(lock)
        require(dependency_sources() == state["dependency_sources"], "dependency sources changed during checking")
        for path, expected in harness_hashes.items():
            require(sha256(Path(path)) == expected, "verification harness changed during checking")
        checkout(lock["tools"]["nanoda"], nanoda, output)
        checkout(lock["tools"]["lean4export"], exporter, output)
        state.update(status="passed", independent_kernel_check="passed", phase="complete",
                     checked_declarations=int(successes[0]), inputs_unchanged=True)
        return 0
    except KeyboardInterrupt:
        state.update(status="interrupted", independent_kernel_check="incomplete")
        return 130
    except (RuntimeError, OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        state.update(status="failed", error=str(error))
        if state["independent_kernel_check"] == "running":
            state["independent_kernel_check"] = "failed"
        return 1
    finally:
        state["completed_utc"] = utc()
        write_json(output / "run.json", state)
        print(json.dumps({"status": state["status"], "independent_kernel_check": state["independent_kernel_check"],
                          "report": str(output / "run.json"), "error": state.get("error"),
                          "missing_prerequisites": state.get("missing_prerequisites", [])}, indent=2))


if __name__ == "__main__":
    raise SystemExit(main())
