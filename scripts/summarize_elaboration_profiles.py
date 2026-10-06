#!/usr/bin/env python3
"""Summarize completed Lean profiles without changing their logs or trace JSON.

C++ --profile timers are exclusive elapsed times, summed across threads. Firefox
trace weights are elapsed intervals, not measured CPU time; inclusive rankings
overlap. Source pointers are declaration locations, not inferred tactic locations.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

REPO = Path(__file__).resolve().parents[1]
PROJECT = REPO / "formalization"
LEAN_COMMIT = "00659f8e6071d7e46131ed643bf8003b99b044e9"
SOURCE_URL = f"https://github.com/leanprover/lean4/blob/{LEAN_COMMIT}/src/"
NUMBER = r"[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?"
DURATION = rf"({NUMBER})\s*(ms|s)"
EVENT = re.compile(rf"^(.*?) took {DURATION}\s*$")
TOTAL = re.compile(rf"^\s+(.+?)\s+{DURATION}\s*$")
IDENTIFIER = r"(?:«[^»]+»|[^\W\d]\w*[!?']*)(?:\.(?:«[^»]+»|[^\W\d]\w*[!?']*))*"
DECLARATION = re.compile(
    rf"(?m)^[ \t]*(?:@\[[^\]]*\]\s*)*"
    rf"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    rf"(theorem|lemma|def|abbrev|opaque|instance|structure|class|inductive)\s+({IDENTIFIER})"
)
SCOPE = re.compile(rf"(?m)^[ \t]*(namespace|section|end)\b[ \t]*({IDENTIFIER})?")


def milliseconds(number, unit):
    return float(number) * (1000 if unit == "s" else 1)


def parse_text_profile(text, threshold_ms=100):
    """Parse the pinned C++ time_task.cpp and timeit.cpp output formats."""
    totals, events = defaultdict(float), []
    in_totals, blocks = False, 0
    for line_number, line in enumerate(text.splitlines(), 1):
        if line.strip() == "cumulative profiling times:":
            in_totals, blocks = True, blocks + 1
            continue
        match = TOTAL.match(line) if in_totals else None
        if match:
            totals[match[1]] += milliseconds(match[2], match[3])
            continue
        if line.strip():
            in_totals = False
        match = EVENT.match(line.strip())
        if match:
            ms = milliseconds(match[2], match[3])
            if ms > threshold_ms:
                category, separator, declaration = match[1].partition(" of ")
                events.append({"category": category, "declaration": declaration if separator else None,
                               "exclusive_ms": ms, "log_line": line_number, "text": line.strip()})
    events.sort(key=lambda row: row["exclusive_ms"], reverse=True)
    head_classes = defaultdict(lambda: {"logged_exclusive_ms": 0.0, "event_count": 0})
    for event in events:
        if event["category"] == "typeclass inference" and event["declaration"]:
            head = head_classes[event["declaration"]]
            head["logged_exclusive_ms"] += event["exclusive_ms"]
            head["event_count"] += 1
    return {"cumulative_blocks": blocks, "exclusive_phase_ms": dict(totals),
            "exclusive_phase_sum_ms": sum(totals.values()), "events_over_threshold": events,
            "head_class_events_over_threshold": [
                {"head_class": name, **values} for name, values in
                sorted(head_classes.items(), key=lambda item: item[1]["logged_exclusive_ms"], reverse=True)],
            "unattributed_elaboration_events": [
                event for event in events if event["category"] == "elaboration" and not event["declaration"]]}


def masked_source(text):
    """Keep character positions while masking nested comments and strings."""
    result = list(text)
    i, depth, line_comment, string = 0, 0, False, False
    while i < len(text):
        c, pair = text[i], text[i:i + 2]
        if c == "\n":
            line_comment = False
            i += 1
            continue
        if line_comment:
            result[i] = " "
            i += 1
        elif depth:
            if pair in ("/-", "-/"):
                depth += 1 if pair == "/-" else -1
                result[i:i + 2] = "  "
                i += 2
            else:
                result[i] = " "
                i += 1
        elif string:
            result[i] = " "
            if c == "\\" and i + 1 < len(text):
                if text[i + 1] != "\n":
                    result[i + 1] = " "
                i += 2
            else:
                string = c != '"'
                i += 1
        elif pair in ("--", "/-"):
            line_comment, depth = pair == "--", int(pair == "/-")
            result[i:i + 2] = "  "
            i += 2
        elif c == '"':
            result[i], string = " ", True
            i += 1
        else:
            i += 1
    return "".join(result)


def declaration_locations(text, source):
    masked, scopes, declarations = masked_source(text), [], []
    tokens = [(m.start(), "scope", m) for m in SCOPE.finditer(masked)]
    tokens.extend((m.start(), "declaration", m) for m in DECLARATION.finditer(masked))
    for _, kind, match in sorted(tokens, key=lambda item: item[0]):
        if kind == "scope":
            command, name = match[1], match[2]
            if command == "end":
                if name:
                    for i in range(len(scopes) - 1, -1, -1):
                        if scopes[i][1] == name:
                            scopes = scopes[:i]
                            break
                elif scopes:
                    scopes.pop()
            else:
                scopes.append((command, name))
            continue
        name = match[2]
        namespace = ".".join(n for k, n in scopes if k == "namespace" and n)
        full_name = name.removeprefix("_root_.") if name.startswith("_root_.") else ".".join(
            part for part in (namespace, name) if part)
        position = match.start(2)
        declarations.append({"declaration": full_name, "short_name": name,
                             "kind": match[1], "file": source,
                             "line": text.count("\n", 0, position) + 1,
                             "column": position - text.rfind("\n", 0, position),
                             "position_origin": "lexical_declaration_in_hash_bound_source"})
    return declarations


def bound_source(record, directory=None):
    """Use only source bytes bound by a recorded SHA-256; never guess a revision."""
    source = record.get("source", "")
    expected = record.get("source_sha256")
    if not expected:
        return [], "No recorded source_sha256; declaration positions are unavailable."
    relative = source if source.startswith("formalization/") else "formalization/" + source
    path = (REPO / relative).resolve()
    if not path.is_relative_to(PROJECT.resolve()) or path.suffix != ".lean":
        return [], "Source path is outside the owned Lean project."
    if record.get("source_snapshot") and directory is not None:
        snapshot = input_path(directory, record["source_snapshot"])
        data = snapshot.read_bytes()
        if hashlib.sha256(data).hexdigest() != expected:
            raise ValueError("Preserved profile source differs from its recorded SHA-256")
        return declaration_locations(data.decode("utf-8"), relative), None
    data = path.read_bytes() if path.is_file() else b""
    if hashlib.sha256(data).hexdigest() != expected:
        commit = record.get("commit")
        if not commit:
            return [], "Working source differs from recorded hash and no commit is recorded."
        result = subprocess.run(["git", "show", f"{commit}:{relative}"], cwd=REPO,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        data = result.stdout if result.returncode == 0 else b""
        if hashlib.sha256(data).hexdigest() != expected:
            return [], "Recorded source hash matches neither the working source nor its commit."
    return declaration_locations(data.decode("utf-8"), relative), None


def source_pointers(descriptor, declarations, exact_name=None):
    """Locate explicit declaration names, not every constant mentioned in a goal."""
    names = [exact_name] if exact_name else re.findall(
        rf"\b(?:theorem|lemma|def|abbrev|opaque|structure|class|inductive)\s+({IDENTIFIER})",
        descriptor)
    if not names and ": " in descriptor:
        tag = descriptor.split(": ", 1)[1]
        if re.fullmatch(IDENTIFIER, tag):
            names = [tag]
    matches = []
    for name in names:
        for declaration in declarations:
            if name in (declaration["declaration"], declaration["short_name"]) or (
                    name.startswith("_private.") and name.endswith("." + declaration["declaration"])):
                pointer = {k: v for k, v in declaration.items() if k != "short_name"}
                if pointer not in matches:
                    matches.append(pointer)
    return matches


def parse_firefox_profile(profile, declarations=(), limit=50):
    """Account for each weighted leaf slice once; de-duplicate recursive frames."""
    functions = defaultdict(lambda: {"self_ms": 0.0, "inclusive_ms": 0.0})
    paths, categories, threads = defaultdict(float), defaultdict(float), []
    negative_weights, exported_positions = 0, 0
    for thread in profile.get("threads", []):
        samples, stacks = thread["samples"], thread["stackTable"]
        frames, funcs, strings = thread["frameTable"], thread["funcTable"], thread["stringArray"]
        if samples.get("weightType") != "tracing-ms":
            raise ValueError("Expected Lean tracing-ms sample weights")
        if len(samples["stack"]) != len(samples["weight"]):
            raise ValueError("Sample stack and weight arrays differ in length")
        frame_keys = []
        for i, func in enumerate(frames["func"]):
            file_index = funcs["fileName"][func]
            file_name = strings[file_index] if file_index is not None else None
            line = frames["line"][i] if frames["line"][i] is not None else funcs["lineNumber"][func]
            column = frames["column"][i] if frames["column"][i] is not None else funcs["columnNumber"][func]
            exported_positions += int(file_name is not None and line is not None)
            frame_keys.append((strings[funcs["name"][func]], file_name, line, column))
        stack_paths = {}
        def stack_path(index):
            if index not in stack_paths:
                chain, seen = [], set()
                while index is not None:
                    if index in seen:
                        raise ValueError("Cycle in Firefox stack prefixes")
                    seen.add(index)
                    chain.append(frame_keys[stacks["frame"][index]])
                    index = stacks["prefix"][index]
                return tuple(reversed(chain))
            return stack_paths[index]
        total = 0.0
        for stack, weight in zip(samples["stack"], samples["weight"]):
            weight = float(weight)
            total += weight
            negative_weights += int(weight < -1e-6)
            if not weight:
                continue
            path = stack_path(stack)
            stack_paths[stack] = path
            functions[path[-1]]["self_ms"] += weight
            for key in set(path):
                functions[key]["inclusive_ms"] += weight
            paths[tuple(key[0] for key in path)] += weight
            category = path[-1][0].split(":", 1)[0]
            categories[category] += weight
        times = samples.get("time", [])
        threads.append({"name": thread["name"], "is_main_thread": thread.get("isMainThread", False),
                        "sample_count": len(samples["weight"]), "weighted_elapsed_ms": total,
                        "timeline_span_ms": max(times) - min(times) if times else 0})
    def row(key, value):
        name, file_name, line, column = key
        return {"name": name, **value,
                "exported_source_position": {"file": file_name, "line": line, "column": column}
                if file_name is not None and line is not None else None,
                "declaration_pointers": source_pointers(name, declarations)}
    ranked = [row(key, value) for key, value in functions.items()]
    return {"threads": threads, "sum_thread_weights_ms": sum(t["weighted_elapsed_ms"] for t in threads),
            "main_thread_weights_ms": sum(t["weighted_elapsed_ms"] for t in threads if t["is_main_thread"]),
            "negative_weight_count": negative_weights, "exported_position_count": exported_positions,
            "top_self_functions": sorted(ranked, key=lambda r: r["self_ms"], reverse=True)[:limit],
            "top_inclusive_functions": sorted(ranked, key=lambda r: r["inclusive_ms"], reverse=True)[:limit],
            "self_by_trace_class_ms": dict(sorted(categories.items(), key=lambda r: r[1], reverse=True)),
            "top_self_stacks": [{"stack": list(path), "self_ms": ms} for path, ms in
                                sorted(paths.items(), key=lambda r: r[1], reverse=True)[:limit]]}


def input_path(directory, name):
    directory = directory.resolve()
    path = (directory / name).resolve()
    if not path.is_relative_to(directory) or not path.is_file():
        raise ValueError("Missing or escaping profile input: " + str(path))
    return path


def summarize(directory, limit=50, threshold_ms=100):
    directory = directory.resolve()
    records = json.loads((directory / "profiles.json").read_text())
    results, raw_paths = [], {directory / "profiles.json"}
    for record in records:
        log_path = input_path(directory, record["log"])
        events_path = input_path(directory, record["events"])
        raw_paths.update((log_path, events_path))
        input_hashes = {}
        for key in ("log", "events", "resources", "source_snapshot", "setup_snapshot", "trace_snapshot", "import_context"):
            if record.get(key):
                raw_path = input_path(directory, record[key])
                raw_paths.add(raw_path)
                digest = hashlib.sha256(raw_path.read_bytes()).hexdigest()
                input_hashes[key] = digest
                expected_key = {"source_snapshot": "source_sha256", "setup_snapshot": "setup_sha256",
                                "trace_snapshot": "trace_sha256", "import_context": "import_context_sha256"}.get(key)
                if expected_key and record.get(expected_key) != digest:
                    raise ValueError("Profile input differs from its recorded SHA-256: " + key)
        declarations, source_warning = bound_source(record, directory)
        text = parse_text_profile(log_path.read_text(), threshold_ms)
        for event in text["events_over_threshold"]:
            event["declaration_pointers"] = source_pointers(event["text"], declarations, event["declaration"])
        trace = parse_firefox_profile(json.loads(events_path.read_text()), declarations, limit)
        warnings = [source_warning] if source_warning else []
        if record.get("exit_code") != 0:
            warnings.append("This profile did not complete successfully; timings are partial evidence.")
        if record.get("measurement_valid") is False:
            warnings.append("Profile measurement is invalid or incomplete; inspect its input stability guards.")
        if not text["cumulative_blocks"]:
            warnings.append("No cumulative --profile totals found.")
        if not trace["exported_position_count"]:
            warnings.append("This Lean exporter provides no source positions; pointers identify declarations only.")
        if trace["negative_weight_count"]:
            warnings.append("Negative trace intervals retained; trace rankings require timeline inspection.")
        if all(row["name"] in ("Import", "runFrontend") for row in trace["top_self_functions"]):
            warnings.append("No detailed timed trace nodes; enable trace.profiler=true for attribution.")
        results.append({"profile": record, "input_sha256": input_hashes,
            "text_profile": text, "firefox_profile": trace, "warnings": warnings})
    return {"schema": "cloning-elaboration-profile-summary-v1",
            "generated_utc": datetime.now(timezone.utc).isoformat(),
            "threshold_ms": threshold_ms, "ranking_limit": limit,
            "measurement_notes": [
                "C++ cumulative totals and individual events are exclusive elapsed times, not OS CPU time.",
                "Cumulative timers are summed across threads and need not equal process wall time.",
                "Firefox self weights count each leaf interval once; inclusive functions overlap.",
                "Firefox function labels are trace classes/tags/messages, not native sampled functions.",
                "Recursive occurrences of a function count once per inclusive weighted slice.",
                "Firefox threadCPUDelta is synthesized from elapsed intervals by Lean; it is not sampled CPU.",
                "Thread trace intervals can overlap; their sum is not process wall time.",
                "Declaration pointers locate hash-bound source declarations, not the precise expensive tactic.",
                "Text durations use Lean's three-significant-digit display precision."],
            "format_sources": {"cpp_timers": SOURCE_URL + "library/time_task.cpp",
                               "duration_display": SOURCE_URL + "util/timeit.cpp",
                               "firefox_exporter": SOURCE_URL + "Lean/Util/Profiler.lean"},
            "profile_count": len(results), "profiles": results}, raw_paths


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profiles", type=Path, required=True, help="Directory containing profiles.json")
    parser.add_argument("--output", type=Path, help="Default: PROFILE_DIRECTORY/summary.json")
    parser.add_argument("--limit", type=int, default=50)
    parser.add_argument("--threshold-ms", type=float, default=100)
    args = parser.parse_args()
    if args.limit < 1 or args.threshold_ms < 0:
        parser.error("--limit must be positive and --threshold-ms nonnegative")
    directory = args.profiles.resolve()
    summary, raw_paths = summarize(directory, args.limit, args.threshold_ms)
    output = (args.output or directory / "summary.json").resolve()
    if output in raw_paths:
        parser.error("Refusing to overwrite a raw profile input")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(f"Summarized {summary['profile_count']} profiles: {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
