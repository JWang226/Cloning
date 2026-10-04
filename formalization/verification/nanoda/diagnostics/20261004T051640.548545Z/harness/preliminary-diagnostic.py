#!/usr/bin/env python3
"""Unbound preliminary diagnostic only; never substitutes for the official runner."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, importlib.util, json, os, re, shutil, subprocess, sys

PROJECT = Path.cwd().resolve()
HERE = PROJECT / "verification/nanoda"
WORK = HERE / ".work"
OUT = WORK / ("preliminary-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ"))
OUT.mkdir()
spec = importlib.util.spec_from_file_location("nanoda_reproduce", HERE / "reproduce.py")
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)
state = {"status": "running", "scope": "unbound_preliminary_diagnostic", "official_bound_runner": "not_run", "independent_kernel_check": "not_run", "started_utc": r.utc(), "output": str(OUT), "runner_pid": os.getpid()}

def save():
    r.write_json(OUT / "diagnostic.json", state)

def project_sources():
    paths = set(PROJECT.glob("*.lean")) | set((PROJECT / "Cloning").rglob("*.lean")) | {PROJECT / "lean-toolchain", PROJECT / "lakefile.toml", PROJECT / "lake-manifest.json"}
    return {str(p.relative_to(PROJECT)): r.sha256(p) for p in sorted(paths)}

def exporter_compiled(exporter):
    return {str(p.relative_to(exporter)): r.sha256(p) for p in sorted((exporter / ".lake/build/lib/lean").rglob("*.olean"))}

print("PRELIMINARY UNBOUND diagnostic directory: " + str(OUT), flush=True)
save()
try:
    inventory_path = PROJECT / "verification/kernel-compatibility/project-safety-inventory.json"
    inventory = r.read_json(inventory_path)
    project_roots = inventory["declaration_names"]
    r.require(len(project_roots) == len(set(project_roots)) == inventory["project_declarations"], "inventory root count or uniqueness mismatch")
    r.require(inventory["unsafe_declarations"] == [] and inventory["partial_declarations"] == [], "project safety inventory contains non-safe constants")
    r.require(all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name) for name in project_roots), "unsupported name encoding")
    lock = r.read_json(r.LOCK_PATH)
    config = r.read_json(HERE / "nanoda-config.json")
    r.validate_config(config, lock)
    r.require(lock["tools"]["nanoda"]["patches"] == [], "kernel patches forbidden")
    r.require((PROJECT / "lean-toolchain").read_text().strip() == lock["lean_toolchain"], "Lean pin drift")
    roots = sorted(set(project_roots) | set(r.BUILTINS) | r.STANDARD_AXIOMS)
    (OUT / "roots.txt").write_text("\n".join(roots) + "\n")
    shutil.copy2(inventory_path, OUT / "project-safety-inventory.json")
    shutil.copy2(r.LOCK_PATH, OUT / "tools-lock.json")
    source_hashes = project_sources()
    compiled = r.compiled_hashes()
    r.require(len(compiled) == inventory["modules"] + 1, "compiled artifact/module count mismatch")
    dependencies = r.dependency_sources()
    r.write_json(OUT / "source-before.json", source_hashes)
    r.write_json(OUT / "compiled-before.json", compiled)
    exporter = r.checkout(lock["tools"]["lean4export"], WORK / "src/lean4export", OUT)
    nanoda = r.checkout(lock["tools"]["nanoda"], WORK / "src/nanoda", OUT)
    tool_compiled = exporter_compiled(exporter)
    r.require(bool(tool_compiled), "missing compiled exporter API")
    r.write_json(OUT / "exporter-compiled-before.json", tool_compiled)
    binary = nanoda / "target/release/nanoda_bin"
    rust = WORK / "rust-local"
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env.update(CARGO_HOME=str(rust / "cargo"), RUSTUP_HOME=str(rust / "rustup"), CARGO_BUILD_JOBS="1", LEAN_ABORT_ON_PANIC="1", PATH=str(rust / "cargo/bin") + os.pathsep + str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", ""))
    tracked = [r.LOCK_PATH, HERE / "reproduce.py", HERE / "ExportCloning.lean", HERE / "nanoda-config.json", Path(__file__).resolve(), inventory_path, exporter / "Export.lean", exporter / "lean-toolchain", binary]
    tracked_hashes = {str(p): r.sha256(p) for p in tracked}
    state.update(project_declarations=len(project_roots), modules=inventory["modules"], requested_roots=len(roots), roots_sha256=r.sha256(OUT / "roots.txt"), provenance_sha256=tracked_hashes, dependency_sources=dependencies, tools=lock["tools"], environment_overrides={"CARGO_HOME":env["CARGO_HOME"], "RUSTUP_HOME":env["RUSTUP_HOME"], "CARGO_BUILD_JOBS":"1", "LEAN_ABORT_ON_PANIC":"1", "PATH_prefix":[str(rust / "cargo/bin"),str(Path.home() / ".elan/bin")], "LEAN_PATH":"unset_then_exporter_API_for_export"}, audit_binding="not_established_fresh_axiom_audit_still_running")
    save()
    commands = []
    def command(argv, output, error=None, environment=env):
        commands.append({"argv":argv, "cwd":str(PROJECT), "stdout":str(output), "stderr":str(error) if error else "merged"})
        r.write_json(OUT / "commands.json", commands)
        r.command(argv, PROJECT, output, env=environment, error_output=error)
    command(["rustup", "run", lock["tools"]["nanoda"]["rust_toolchain"], "rustc", "--version", "--verbose"], OUT / "rust-version.log")
    command(["lake", "env", "lean", "--version"], OUT / "lean-version.log")
    r.require(lock["lean_toolchain"].split(":v")[1] in (OUT / "lean-version.log").read_text(), "effective Lean version drift")
    export_path = OUT / "cloning.ndjson"
    export_env = dict(env, LEAN_PATH=str(exporter / ".lake/build/lib/lean"))
    state["phase"] = "export"
    save()
    command(["/usr/bin/time", "-l", "lake", "env", "lean", "--run", str(HERE / "ExportCloning.lean"), str(OUT / "roots.txt")], export_path, OUT / "export.stderr", export_env)
    export_report = r.scan_export(export_path, set(roots), lock)
    r.write_json(OUT / "export.json", export_report)
    config.update(export_file_path=str(export_path), num_threads=1)
    r.validate_config(config, lock)
    r.write_json(OUT / "nanoda-config.json", config)
    state.update(phase="check", independent_kernel_check="running", export_sha256=export_report["sha256"], checker_binary_sha256=r.sha256(binary), checker_config_sha256=r.sha256(OUT / "nanoda-config.json"))
    save()
    command(["/usr/bin/time", "-l", str(binary), str(OUT / "nanoda-config.json")], OUT / "nanoda.stdout", OUT / "nanoda.stderr")
    stdout = (OUT / "nanoda.stdout").read_text()
    success = re.findall(r"^Checked (\d+) declarations with no errors$", stdout, re.MULTILINE)
    r.require(len(success) == 1 and int(success[0]) == export_report["declarations"], "missing/mismatched unqualified success count")
    r.require(project_sources() == source_hashes, "project sources changed during diagnostic")
    r.require(r.compiled_hashes() == compiled, "project artifacts changed during diagnostic")
    r.require(r.dependency_sources() == dependencies, "dependency sources changed during diagnostic")
    r.require(exporter_compiled(exporter) == tool_compiled, "compiled exporter changed during diagnostic")
    for path, expected in tracked_hashes.items():
        r.require(r.sha256(Path(path)) == expected, "provenance changed during diagnostic: " + path)
    r.require(r.sha256(export_path) == export_report["sha256"], "export changed during checking")
    r.require(r.sha256(OUT / "nanoda-config.json") == state["checker_config_sha256"], "checker config changed during checking")
    r.require(r.sha256(OUT / "roots.txt") == state["roots_sha256"], "roots changed during checking")
    r.checkout(lock["tools"]["nanoda"], nanoda, OUT)
    r.checkout(lock["tools"]["lean4export"], exporter, OUT)
    state.update(status="passed_preliminary_unbound", phase="complete", independent_kernel_check="passed_preliminary_unbound", checked_declarations=int(success[0]), inputs_unchanged=True)
    code = 0
except KeyboardInterrupt:
    state.update(status="interrupted_preliminary_unbound", independent_kernel_check="incomplete_preliminary_unbound")
    code = 130
except Exception as error:
    state.update(status="failed_preliminary_unbound", error=str(error))
    if state["independent_kernel_check"] == "running":
        state["independent_kernel_check"] = "failed_or_incomplete_preliminary_unbound"
    code = 1
finally:
    state["completed_utc"] = r.utc()
    save()
    print(json.dumps({k:state.get(k) for k in ["status","scope","official_bound_runner","independent_kernel_check","phase","checked_declarations","output","error"]}, indent=2), flush=True)
raise SystemExit(code)
