#!/usr/bin/env python3
"""Audit every compiled Cloning root with one shared native axiom traversal.

Copy this standalone engine beside Cloning.lean and Cloning/, with a `build`
link to the compiled project. CLONING_LEAN and CLONING_PACKAGES supply the same
compiler/search-path overrides as the historical engine. No proof is checked
from source-token guesses: coverage comes from imported Lean module tables.

The result is an aggregate axiom union, with no per-root axiom attribution.
--generate-only writes inputs and the driver without invoking Lean.
--resummarize validates completed evidence without invoking Lean.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

SCHEMA = "cloning-shared-axiom-audit-v1"
STRATEGY = "shared-transitive-axiom-union"
ALLOWED_AXIOMS = frozenset({"Classical.choice", "Quot.sound", "propext"})
KINDS = frozenset({"axiom", "definition", "theorem", "opaque", "quotient",
                   "inductive", "constructor", "recursor"})
ROOT_DEDUPLICATION = "identical repeated module exports counted once"


class AuditError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise AuditError(message)


def sha256(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def digest_json(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"),
                                     ensure_ascii=False).encode()).hexdigest()


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True,
                                    ensure_ascii=False) + "\n", encoding="utf-8")


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key: " + key)
        result[key] = value
    return result


def read_json(path):
    return json.loads(Path(path).read_text(encoding="utf-8"), object_pairs_hook=unique_object,
                      parse_constant=lambda value: (_ for _ in ()).throw(AuditError("Invalid JSON constant: " + value)))


def source_tokens(text):
    """Mask nested comments and strings, preserving diagnostic line numbers."""
    out, depth, pos, string = [], 0, 0, False
    while pos < len(text):
        pair = text[pos:pos + 2]
        if string:
            if text[pos] == "\\" and pos + 1 < len(text):
                out.extend("  ")
                pos += 2
                continue
            if text[pos] == '"':
                string = False
            out.append("\n" if text[pos] == "\n" else " ")
            pos += 1
        elif pair == "/-":
            depth += 1
            out.extend("  ")
            pos += 2
        elif depth and pair == "-/":
            depth -= 1
            out.extend("  ")
            pos += 2
        elif not depth and pair == "--":
            end = text.find("\n", pos)
            out.extend(" " * ((len(text) if end < 0 else end) - pos))
            pos = len(text) if end < 0 else end
        elif not depth and text[pos] == '"':
            string = True
            out.append(" ")
            pos += 1
        else:
            out.append(text[pos] if not depth or text[pos] == "\n" else " ")
            pos += 1
    return "".join(out)


def source_info(root):
    umbrella = root / "Cloning.lean"
    require(umbrella.is_file(), "Missing source umbrella Cloning.lean")
    files = sorted((root / "Cloning").rglob("*.lean"))
    sources, counts, declarations = {}, {}, []
    pattern = re.compile(r"^\s*(?:@\[[^\n]*\]\s*)*"
                         r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
                         r"(theorem|lemma)\s+(\S+)", re.M)
    for path in [umbrella, *files]:
        relative = path.relative_to(root).as_posix()
        sources[relative] = sha256(path)
        tokens = source_tokens(path.read_text(encoding="utf-8"))
        require(not re.search(r"\b(?:sorry|admit|axiom|sorryAx)\b", tokens),
                "Unproved declaration or placeholder in " + relative)
        if path == umbrella:
            continue
        matches = list(pattern.finditer(tokens))
        counts[path.relative_to(root / "Cloning").as_posix()] = len(matches)
        declarations.extend({"file": relative, "kind": match.group(1),
                             "written_name": match.group(2),
                             "line": tokens.count("\n", 0, match.start(1)) + 1}
                            for match in matches)
    modules = sorted(".".join(path.relative_to(root).with_suffix("").parts) for path in files)
    require(len(modules) == len(set(modules)), "Source paths map to duplicate Lean module names")
    return {"source_sha256": sources, "source_manifest_sha256": digest_json(sources),
            "source_modules": modules, "expected_modules": sorted(["Cloning", *modules]),
            "theorems": sum(counts.values()), "by_module": counts,
            "source_declarations": declarations}


DRIVER = r'''import Cloning
import Lean.Util.CollectAxioms

open Lean Elab Command

private def sharedAuditWrite (handle : IO.FS.Handle) (value : Json) : IO Unit := do
  handle.putStrLn value.compress
  handle.flush

private def sharedAuditKind (info : ConstantInfo) : String :=
  match info with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let handle ← liftIO <| IO.FS.Handle.mk "audit-native.jsonl" .write
  let importedModules := env.header.moduleNames.filter fun name =>
    name == `Cloning || (`Cloning).isPrefixOf name
  liftIO <| sharedAuditWrite handle <| Json.mkObj [
    ("event", toJson "begin"), ("audit_schema", toJson "@@SCHEMA@@"),
    ("source_manifest_sha256", toJson "@@SOURCE@@"),
    ("imported_modules", toJson importedModules.size)]
  let mut seen : NameSet := {}
  let mut roots : Array Name := #[]
  let mut exportOccurrences := 0
  let mut moduleCount := 0
  for index in [:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[index]!
    if moduleName == `Cloning || (`Cloning).isPrefixOf moduleName then
      let data := env.header.moduleData[index]!
      let mut constants : Array Json := #[]
      let mut moduleSeen : NameSet := {}
      for name in data.constNames do
        if moduleSeen.contains name then
          throwError "Duplicate compiled export {name} within {moduleName}"
        moduleSeen := moduleSeen.insert name
        let some info := env.checked.get.find? name
          | throwError "Missing checked declaration {name} from {moduleName}"
        constants := constants.push <| Json.mkObj [
          ("name", toJson name.toString), ("kind", toJson (sharedAuditKind info)),
          ("private", toJson (name.toString.startsWith "_private."))]
        exportOccurrences := exportOccurrences + 1
        if !seen.contains name then
          seen := seen.insert name
          roots := roots.push name
      moduleCount := moduleCount + 1
      liftIO <| sharedAuditWrite handle <| Json.mkObj [
        ("event", toJson "module"), ("module", toJson moduleName.toString),
        ("constant_count", toJson constants.size), ("constants", Json.arr constants)]
  liftIO <| sharedAuditWrite handle <| Json.mkObj [
    ("event", toJson "inventory_complete"), ("imported_modules", toJson moduleCount),
    ("export_occurrences", toJson exportOccurrences), ("unique_roots", toJson roots.size)]
  -- One State, including its visited set, is shared across every unique root.
  -- The pinned native collector retains its exact type/value and cycle semantics.
  let (_, state) := ((roots.forM CollectAxioms.collect).run env).run {}
  let axioms := state.axioms.map Name.toString
  liftIO <| sharedAuditWrite handle <| Json.mkObj [
    ("event", toJson "aggregate"), ("root_count", toJson roots.size),
    ("visited_constants", toJson state.visited.toList.length), ("axioms", toJson axioms)]
  let unexpected := axioms.filter fun name =>
    name != "Classical.choice" && name != "Quot.sound" && name != "propext"
  liftIO <| sharedAuditWrite handle <| Json.mkObj [
    ("event", toJson "complete"), ("passed", toJson unexpected.isEmpty)]
  if !unexpected.isEmpty then
    throwError "Unexpected aggregate axioms: {unexpected}"
'''


def generate_driver(source_digest):
    return DRIVER.replace("@@SCHEMA@@", SCHEMA).replace("@@SOURCE@@", source_digest)


def fields(value, wanted, label):
    require(type(value) is dict and set(value) == set(wanted), "Malformed " + label + " fields")


def natural(value, label):
    require(type(value) is int and value >= 0, "Invalid " + label)
    return value


def names(value, label):
    require(type(value) is list and all(type(name) is str and name for name in value),
            "Invalid " + label)
    require(len(value) == len(set(value)), "Duplicate " + label)
    return value


def parse_native_output(text, expected_modules, source_digest):
    require(bool(text) and text.endswith("\n"), "Incomplete native output")
    events = []
    for line in text.splitlines():
        require(bool(line), "Blank native output record")
        try:
            event = json.loads(line, object_pairs_hook=unique_object,
                               parse_constant=lambda value: (_ for _ in ()).throw(AuditError("Invalid JSON constant: " + value)))
        except json.JSONDecodeError as error:
            raise AuditError("Malformed native JSON: " + str(error)) from error
        require(type(event) is dict and type(event.get("event")) is str, "Malformed native event")
        events.append(event)
    require(len(events) >= 4, "Incomplete native event sequence")
    begin = events[0]
    fields(begin, ["event", "audit_schema", "source_manifest_sha256", "imported_modules"], "begin")
    require(begin["event"] == "begin" and begin["audit_schema"] == SCHEMA
            and begin["source_manifest_sha256"] == source_digest, "Native schema/source binding differs")
    names(expected_modules, "expected source modules")
    expected = set(expected_modules)
    require(natural(begin["imported_modules"], "module count") == len(expected), "Native module count differs")
    modules, unique, occurrence_count = {}, {}, 0
    cursor = 1
    while cursor < len(events) and events[cursor]["event"] == "module":
        record = events[cursor]
        fields(record, ["event", "module", "constant_count", "constants"], "module")
        module = record["module"]
        require(type(module) is str and module in expected, "Unexpected imported project module")
        require(module not in modules, "Duplicate module record: " + module)
        require(type(record["constants"]) is list
                and natural(record["constant_count"], "constant count") == len(record["constants"]),
                "Malformed module constant inventory")
        module_names = set()
        for info in record["constants"]:
            fields(info, ["name", "kind", "private"], "constant")
            name = info["name"]
            require(type(name) is str and bool(name) and type(info["kind"]) is str and info["kind"] in KINDS
                    and type(info["private"]) is bool, "Malformed constant metadata")
            require(info["private"] == name.startswith("_private."), "Incorrect private declaration flag")
            require(name not in module_names, "Duplicate constant within module: " + name)
            module_names.add(name)
            normalized = {"name": name, "kind": info["kind"], "private": info["private"]}
            if name in unique:
                require({k: unique[name][k] for k in normalized} == normalized,
                        "Conflicting repeated declaration: " + name)
                unique[name]["exported_by"].append(module)
            else:
                unique[name] = {**normalized, "exported_by": [module]}
        occurrence_count += len(record["constants"])
        modules[module] = record
        cursor += 1
    require(set(modules) == expected, "Missing imported project module inventory")
    require(len(events) == cursor + 3, "Incomplete or extra native events")
    inventory, aggregate, complete = events[cursor:]
    fields(inventory, ["event", "imported_modules", "export_occurrences", "unique_roots"], "inventory completion")
    require(inventory["event"] == "inventory_complete"
            and natural(inventory["imported_modules"], "inventory module count") == len(modules)
            and natural(inventory["export_occurrences"], "export count") == occurrence_count
            and natural(inventory["unique_roots"], "unique root count") == len(unique),
            "Incorrect or incomplete native inventory coverage")
    fields(aggregate, ["event", "root_count", "visited_constants", "axioms"], "aggregate")
    require(aggregate["event"] == "aggregate"
            and natural(aggregate["root_count"], "traversed root count") == len(unique),
            "Aggregate traversal does not cover every unique root")
    visited = natural(aggregate["visited_constants"], "visited declaration count")
    require(visited >= len(unique), "Visited declaration count omits project roots")
    axioms = sorted(names(aggregate["axioms"], "aggregate axiom names"))
    fields(complete, ["event", "passed"], "completion")
    require(complete["event"] == "complete" and type(complete["passed"]) is bool,
            "Missing native completion marker")
    allowed = set(axioms) <= ALLOWED_AXIOMS
    require(complete["passed"] == allowed, "Native policy verdict conflicts with observed axioms")
    declarations = []
    for name in sorted(unique):
        info = unique[name]
        info["exported_by"].sort()
        declarations.append(info)
    return {"audit_schema": SCHEMA, "modules": [modules[name] for name in sorted(modules)],
            "declarations": declarations, "aggregate_axioms": axioms,
            "native_passed": allowed, "coverage": {"inventory_complete": True,
                "traversal_complete": True, "imported_modules": len(modules),
                "export_occurrences": occurrence_count, "unique_roots": len(unique),
                "visited_constants": visited, "includes_private_generated": True,
                "root_deduplication": ROOT_DEDUPLICATION}}


def generate(root):
    info = source_info(root)
    driver = generate_driver(info["source_manifest_sha256"])
    (root / "Audit.lean").write_text(driver, encoding="utf-8")
    manifest = {"audit_schema": SCHEMA, "engine_sha256": sha256(Path(__file__)), **info,
                "audit_driver_sha256": sha256(root / "Audit.lean")}
    write_json(root / "audit-inputs.json", manifest)
    return manifest


def validate_inputs(root):
    manifest = read_json(root / "audit-inputs.json")
    info = source_info(root)
    require(manifest == {"audit_schema": SCHEMA, "engine_sha256": sha256(Path(__file__)), **info,
                         "audit_driver_sha256": sha256(root / "Audit.lean")}, "Audit inputs or engine changed")
    require((root / "Audit.lean").read_text(encoding="utf-8") == generate_driver(info["source_manifest_sha256"]),
            "Generated driver differs from the audited strategy")
    return manifest


def make_summary(manifest, receipt, inventory, root):
    coverage = {**inventory["coverage"], "source_modules": len(manifest["source_modules"])}
    passed = receipt["lean_exit_code"] == 0 and inventory["native_passed"]
    return {"audit_schema": SCHEMA, "audit_strategy": STRATEGY,
            "axiom_report_scope": "aggregate union; no per-root axiom attribution",
            "modules": len(manifest["source_modules"]), "theorems": manifest["theorems"],
            "by_module": manifest["by_module"], "source_declarations": manifest["source_declarations"],
            "theorem_count_basis": "source-declared theorem/lemma commands, including attributes and modifiers",
            "audited_constants": coverage["unique_roots"], "raw_constant_reports": coverage["export_occurrences"],
            "constant_count_basis": "unique kernel declaration names; identical repeated module exports counted once",
            "constant_classification": dict(sorted(Counter(info["kind"] for info in inventory["declarations"]).items())),
            "private_constants": sum(info["private"] for info in inventory["declarations"]),
            "compiled_constants_by_module": {item["module"]: item["constant_count"] for item in inventory["modules"]},
            "audit_coverage": "all constant names in every imported Cloning module, via Lean environment tables",
            "aggregate_coverage": coverage, "aggregate_axioms": inventory["aggregate_axioms"],
            "allowed_axioms": sorted(ALLOWED_AXIOMS),
            "unexpected_axioms": sorted(set(inventory["aggregate_axioms"]) - ALLOWED_AXIOMS),
            "missing_reports": [], "missing_modules": [], "duplicate_reports": [], "conflicting_reports": {},
            "lean_exit_code": receipt["lean_exit_code"], "lean_invoked": receipt["lean_invoked"],
            "lean_completion_basis": "completed native Lean subprocess recorded in audit-run.json",
            "audit_driver_sha256": manifest["audit_driver_sha256"],
            "audit_native_output_sha256": sha256(root / "audit-native.jsonl"),
            "audit_output_sha256": sha256(root / "AXIOMS.txt"),
            "audit_inventory_sha256": sha256(root / "audit-inventory.json"),
            "audit_engine_sha256": manifest["engine_sha256"],
            "source_sha256": manifest["source_sha256"], "source_placeholder_scan": "passed",
            "axiom_audit": "passed" if passed else "failed"}


def finish(root, receipt, resummarize=False):
    manifest = validate_inputs(root)
    require(type(receipt) is dict and receipt.get("audit_schema") == SCHEMA and receipt.get("status") == "completed"
            and receipt.get("lean_invoked") is True and type(receipt.get("lean_exit_code")) is int,
            "No completed native Lean execution receipt")
    for name in ("audit-inputs.json", "Audit.lean", "audit-native.jsonl", "AXIOMS.txt"):
        require(receipt.get("evidence_sha256", {}).get(name) == sha256(root / name),
                "Completed audit evidence changed: " + name)
    inventory = parse_native_output((root / "audit-native.jsonl").read_text(encoding="utf-8"),
                                    manifest["expected_modules"], manifest["source_manifest_sha256"])
    inventory_path = root / "audit-inventory.json"
    if resummarize and inventory_path.exists():
        require(read_json(inventory_path) == inventory, "Saved inventory differs from native output")
    else:
        write_json(inventory_path, inventory)
    summary = make_summary(manifest, receipt, inventory, root)
    path = root / "verification.json"
    if resummarize and path.exists():
        require(read_json(path) == summary, "Saved completion summary differs from native evidence")
    else:
        write_json(path, summary)
    require(summary["axiom_audit"] == "passed", "Native aggregate axiom audit failed")
    return summary


def run_native(root, manifest):
    lean = os.environ.get("CLONING_LEAN", "lean")
    env = os.environ.copy()
    paths = [str(root / "build"), str(root)]
    packages = os.environ.get("CLONING_PACKAGES")
    if packages:
        paths.extend(str(path) for path in sorted(Path(packages).glob("*/.lake/build/lib/lean")))
    env["LEAN_PATH"] = os.pathsep.join(paths)
    command = [lean, "-DautoImplicit=false", "Audit.lean"]
    receipt = {"audit_schema": SCHEMA, "status": "running", "lean_invoked": True,
               "command": command, "started_utc": datetime.now(timezone.utc).isoformat()}
    write_json(root / "audit-run.json", receipt)
    print("AUDIT STAGE native Lean started; inventory: audit-native.jsonl", flush=True)
    started, heartbeat = time.monotonic(), time.monotonic()
    with (root / "AXIOMS.txt").open("w", encoding="utf-8") as log:
        process = subprocess.Popen(command, cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT)
        try:
            while process.poll() is None:
                time.sleep(0.1)
                if time.monotonic() - heartbeat >= 5:
                    native = root / "audit-native.jsonl"
                    size = native.stat().st_size if native.exists() else 0
                    print(f"AUDIT HEARTBEAT {time.monotonic() - started:.1f}s; native output {size} bytes", flush=True)
                    heartbeat = time.monotonic()
            receipt["lean_exit_code"] = process.wait()
        except BaseException:
            if process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
            raise
    receipt.update(status="completed", completed_utc=datetime.now(timezone.utc).isoformat(),
                   evidence_sha256={name: sha256(root / name) for name in
                                    ("audit-inputs.json", "Audit.lean", "audit-native.jsonl", "AXIOMS.txt")
                                    if (root / name).is_file()})
    write_json(root / "audit-run.json", receipt)
    print("AUDIT STAGE native Lean completed with exit " + str(receipt["lean_exit_code"]), flush=True)
    return receipt


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--generate-only", action="store_true")
    mode.add_argument("--resummarize", action="store_true")
    args = parser.parse_args(argv)
    root = Path(__file__).resolve().parent
    try:
        if args.resummarize:
            summary = finish(root, read_json(root / "audit-run.json"), resummarize=True)
            print("AUDIT STAGE validated completed shared audit without invoking Lean", flush=True)
        else:
            require(not any((root / name).exists() for name in
                            ("audit-native.jsonl", "audit-run.json", "AXIOMS.txt", "verification.json")),
                    "Native audit evidence already exists; use a new scratch directory or --resummarize")
            manifest = generate(root)
            print("AUDIT STAGE generated shared driver; source modules " + str(len(manifest["source_modules"])), flush=True)
            if args.generate_only:
                return 0
            summary = finish(root, run_native(root, manifest))
        print(f"AUDIT STAGE passed: {summary['audited_constants']} unique compiled roots; "
              f"{summary['aggregate_coverage']['visited_constants']} visited declarations; "
              f"aggregate axioms {summary['aggregate_axioms']}", flush=True)
        return 0
    except (AuditError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print("AUDIT STAGE failed: " + str(error), file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
