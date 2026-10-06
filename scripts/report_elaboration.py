#!/usr/bin/env python3
"""Render a completed, hash-bound elaboration measurement as Markdown.

This is a read-only report generator: it never builds Lean, invalidates artifacts,
or infers CPU time from Lake's rounded elapsed job durations.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
import hashlib
import io
import json
import math
from pathlib import Path
import re
import shlex
import subprocess
import tarfile

REPO = Path(__file__).resolve().parents[1]
SKILL_PIN = "70bb859295edc2abb9ad81f8f6e31ab2adf8ca07"
SKILL_BASE = "https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/" + SKILL_PIN
NUMBER = r"[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?"
BUILT = re.compile(rf"Built\s+(\S+)(?:\s+\(({NUMBER})(ms|s)\))?")


def load_json(path):
    return json.loads(Path(path).read_text())


def markdown(value):
    return str(value).replace("|", "\\|").replace("\n", " ")


def table(headers, rows):
    lines = ["| " + " | ".join(map(markdown, headers)) + " |",
             "| " + " | ".join("---" for _ in headers) + " |"]
    lines.extend("| " + " | ".join(map(markdown, row)) + " |" for row in rows)
    return "\n".join(lines)


def number(value, digits=2):
    return "unavailable" if value is None else f"{value:,.{digits}f}"


def delta(value, prior, digits=2):
    return "—" if value is None or prior is None else f"{value - prior:+,.{digits}f}"


def elapsed_seconds(value):
    parts = [float(x) for x in value.split(":")]
    if not 1 <= len(parts) <= 3 or any(x < 0 for x in parts):
        raise ValueError("Invalid elapsed time: " + value)
    return sum(x * 60 ** i for i, x in enumerate(reversed(parts)))


def resource_metrics(resources):
    def numeric(key):
        value = resources.get(key)
        return float(value) if value is not None else None
    user, system = numeric("User time (seconds)"), numeric("System time (seconds)")
    wall_text = resources.get("Elapsed (wall clock) time (h:mm:ss or m:ss)")
    cpu = user + system if user is not None and system is not None else None
    return {"wall": elapsed_seconds(wall_text) if wall_text else None,
            "user": user, "system": system, "cpu": cpu,
            "cpu_percent": resources.get("Percent of CPU this job got", "unavailable"),
            "rss_kib": numeric("Maximum resident set size (kbytes)")}


def masked_source(text):
    """Mask comments and strings while preserving newlines and positions."""
    result, i, depth, line_comment, string = list(text), 0, 0, False, False
    while i < len(text):
        c, pair = text[i], text[i:i + 2]
        if c == "\n":
            line_comment = False
            i += 1
        elif line_comment:
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


def first_namespace(text):
    match = re.search(r"(?m)^\s*namespace\s+([^\s]+)", masked_source(text))
    return match[1] if match else "(root / facade)"


def archive_sources(commit, sources, repo=REPO):
    """Read measured source bytes from Git, never the current working tree."""
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("Expected a complete measured Git commit")
    for source in sources:
        p = Path(source)
        if p.is_absolute() or ".." in p.parts or not source.startswith("formalization/"):
            raise ValueError("Invalid measured source path: " + source)
    data = subprocess.check_output(["git", "archive", commit, "--", *sources], cwd=repo)
    with tarfile.open(fileobj=io.BytesIO(data)) as archive:
        return {source: archive.extractfile(source).read().decode("utf-8") for source in sources}


def timing_rows(summary, log, modules):
    """Keep displayed durations as estimates and reject duplicate module times."""
    timings = {}
    for row in summary["timings"]:
        module = row["module"]
        if (module not in modules or module in timings or row["seconds"] < 0
                or not math.isfinite(row["seconds"])):
            raise ValueError("Invalid or duplicate owned timing: " + module)
        timings[module] = float(row["seconds"])
    compiled = {m[1] for m in BUILT.finditer(log) if m[1] in modules}
    logged = {m[1]: float(m[2]) / (1000 if m[3] == "ms" else 1)
              for m in BUILT.finditer(log) if m[1] in modules and m[2] is not None}
    if timings != logged:
        raise ValueError("Summary timings differ from the raw build log")
    return timings, compiled


def weighted_chain(graph, timings, target="All"):
    memo, active = {}, set()
    def visit(module):
        if module in active:
            raise ValueError("Cycle in owned import graph")
        if module not in memo:
            active.add(module)
            prior = max((visit(d) for d in graph.get(module, [])),
                        key=lambda row: row[0], default=(0, []))
            memo[module] = (prior[0] + timings.get(module, 0), [*prior[1], module])
            active.remove(module)
        return memo[module]
    return visit(target)


@dataclass
class Snapshot:
    directory: Path
    summary: dict
    sizes: list
    graph: dict
    log: str
    samples: list
    sources: dict
    timings: dict
    compiled: set
    resources: dict

    @classmethod
    def read(cls, directory):
        directory = Path(directory).resolve()
        summary = load_json(directory / "summary.json")
        if summary.get("schema") != "cloning-elaboration-test-v1":
            raise ValueError("Unexpected benchmark schema")
        sizes, graph = load_json(directory / "size.json"), load_json(directory / "imports.json")
        modules = {row["module"] for row in sizes}
        if len(modules) != len(sizes) or set(graph) != modules:
            raise ValueError("Size and import scopes differ")
        if (summary["module_count"] != len(sizes)
                or summary["total_lines"] != sum(row["lines"] for row in sizes)
                or summary["code_lines"] != sum(row["code_lines"] for row in sizes)):
            raise ValueError("Summary source counts differ from recorded sizes")
        reachable = set()
        def visit(module):
            if module not in modules:
                raise ValueError("Import graph contains a non-owned module")
            if module not in reachable:
                reachable.add(module)
                for dependency in graph[module]:
                    visit(dependency)
        visit("All")
        if reachable != modules:
            raise ValueError("All does not reach every recorded owned source")
        log = (directory / "build.log").read_text()
        timings, compiled = timing_rows(summary, log, modules)
        samples = load_json(directory / "process-samples.json")
        sources = archive_sources(summary["commit"], [row["source"] for row in sizes])
        if any(len(sources[row["source"]].splitlines()) != row["lines"] for row in sizes):
            raise ValueError("Measured source line counts differ from recorded sizes")
        return cls(directory, summary, sizes, graph, log, samples, sources,
                   timings, compiled, resource_metrics(summary["resources"]))

    def groups(self):
        result = defaultdict(lambda: {"modules": 0, "code_lines": 0, "seconds": 0})
        for row in self.sizes:
            group = result[first_namespace(self.sources[row["source"]])]
            group["modules"] += 1
            group["code_lines"] += row["code_lines"]
            group["seconds"] += self.timings.get(row["module"], 0)
        return result


def load_profiles(path):
    if path is None:
        return None
    path = Path(path)
    result = load_json(path / "summary.json" if path.is_dir() else path)
    if result.get("schema") != "cloning-elaboration-profile-summary-v1":
        raise ValueError("Supply the completed profile-summary utility output")
    result["report_input_path"] = str((path / "summary.json" if path.is_dir() else path).resolve())
    return result


def ratio(numerator, denominator):
    return numerator / denominator if numerator is not None and denominator else None


def process_census(samples, repo=REPO):
    """Attribute only absolute Lean source paths; Lake command cwd is unknown."""
    maxima = Counter()
    foreign_sources = set()
    foreign_samples = 0
    for sample in samples:
        counts = Counter()
        for line in sample["processes"]:
            fields = line.split(None, 4)
            command = fields[4] if len(fields) == 5 else line
            try:
                arguments = shlex.split(command)
            except ValueError:
                arguments = []
            sources = [Path(arg) for arg in arguments if arg.startswith("/") and arg.endswith(".lean")]
            if sources:
                source = sources[0]
                if source.is_relative_to(repo):
                    counts["owned_source"] += 1
                else:
                    counts["other_source"] += 1
                    foreign_sources.add(str(source))
            else:
                counts["unresolved"] += 1
        foreign_samples += counts["other_source"] > 0
        for group in ("owned_source", "other_source", "unresolved"):
            maxima[group] = max(maxima[group], counts[group])
    return {"maxima": dict(maxima), "foreign_source_paths": sorted(foreign_sources),
            "samples_with_other_source": foreign_samples}


def comparison(current, prior):
    if prior is None:
        return "No prior benchmark supplied; this report is a standalone measurement."
    a, b = current.summary, prior.summary
    matched = (a.get("environment") == b.get("environment") and
               a.get("time_tool") == b.get("time_tool") and a.get("host") == b.get("host"))
    current_sum, prior_sum = sum(current.timings.values()), sum(prior.timings.values())
    pa = ratio(current_sum, current.resources["wall"])
    pb = ratio(prior_sum, prior.resources["wall"])
    up = sum(current.timings[m] > prior.timings[m] * 1.1
             for m in current.timings.keys() & prior.timings.keys())
    down = sum(current.timings[m] < prior.timings[m] * .9
               for m in current.timings.keys() & prior.timings.keys())
    flags = [current.resources["user"] is not None and prior.resources["user"] is not None and
             current.resources["user"] < prior.resources["user"] and current_sum > prior_sum,
             pa is not None and pb is not None and pa > pb * 1.2,
             up > 0 and down > 0]
    relation = "matched" if matched else "unmatched: avoid a wall-time speedup claim"
    text = (f"Host, environment, and timing tool are **{relation}**. "
            f"Contention screens: user CPU down while logged duration sum rises: {flags[0]}; "
            f"logged-duration/wall ratio rises >20%: {flags[1]}; same-module durations move "
            f"in opposite directions by >10%: {flags[2]} ({up} up, {down} down). ")
    if sum(flags) >= 2:
        text += "At least two screens fire; treat the aggregate trend as contention-limited and withhold structural conclusions. "
    else:
        text += "Fewer than two screens fire; this does not establish absence of contention. "
    cpu_per_line = ratio(prior.resources["cpu"], prior.summary["code_lines"])
    predicted = ((a["code_lines"] - b["code_lines"]) * cpu_per_line
                 if cpu_per_line is not None else None)
    actual = (current.resources["cpu"] - prior.resources["cpu"]
              if current.resources["cpu"] is not None and prior.resources["cpu"] is not None else None)
    return text + (f"Growth-only CPU prediction Δcode lines × prior CPU/code line: {number(predicted)} s; "
                   f"actual GNU-time CPU change: {number(actual)} s. Process inventory and these "
                   "heuristics do not identify the cause of a timing change. Two snapshots cannot establish a three-report monotonic trend.")


def profile_section(profiles):
    if profiles is None:
        return "No warm own-file profiles supplied. Local phase costs and cleanup causes remain unestablished."
    rows, details = [], []
    for result in profiles["profiles"]:
        record, parsed = result["profile"], result["text_profile"]
        phases = parsed["exclusive_phase_ms"]
        total = sum(phases.values())
        dominant = [k for k, v in phases.items() if v > 5000 and total and v / total > .25]
        rows.append([record["module"], record.get("repetition", 1), record.get("exit_code"),
                     number(record.get("wall_seconds")), number(total / 1000),
                     ", ".join(dominant) or "no phase above both thresholds",
                     len(parsed["events_over_threshold"])])
        details.append("### " + record["module"] + " — repetition " + str(record.get("repetition", 1)))
        details.append(f"Recorded profile commit: `{record.get('commit', 'unavailable')}`; "
                       f"source SHA-256: `{record.get('source_sha256', 'unavailable')}`.")
        details.append(table(["Exclusive elapsed phase", "Seconds"],
                             [[k, number(v / 1000, 3)] for k, v in sorted(phases.items(), key=lambda x: -x[1])]))
        events = parsed["events_over_threshold"][:10]
        if events:
            details.append(table(["Largest event (>100 ms)", "Exclusive seconds", "Log line"],
                                 [[e["text"], number(e["exclusive_ms"] / 1000, 3), e["log_line"]] for e in events]))
        details.append("Recorded command:\n\n```sh\n" + shlex.join(record["command"]) + "\n```")
        if result.get("warnings"):
            details.append("\n".join("- " + w for w in result["warnings"]))
    note = ("Cumulative C++ timers are exclusive **elapsed** times summed across threads, not OS CPU. "
            "Trace self weights are elapsed intervals; inclusive trace rankings overlap. "
            "The dominant-phase screen requires >5 s and >25% of the displayed phase sum. "
            "Declaration pointers identify declarations, not automatically an exact costly tactic.")
    return note + "\n\n" + table(["Module", "Run", "Exit", "Process wall s", "Phase sum s", "Dominant screen", ">100 ms events"], rows) + "\n\n" + "\n\n".join(details)


def render(current, profiles=None, prior=None, notes=None):
    s, r = current.summary, current.resources
    old = prior.summary if prior else {}
    oldr = prior.resources if prior else {}
    wall = r["wall"]
    logged = sum(current.timings.values())
    old_logged = sum(prior.timings.values()) if prior else None
    own_count = len(current.sizes)
    chain_seconds, chain = weighted_chain(current.graph, current.timings)
    census = process_census(current.samples)
    load_note = table(["Global process inventory", "Observed"], [
        ["Samples", len(current.samples)],
        ["Maximum total Lean/Lake lines", max((len(x["processes"]) for x in current.samples), default=0)],
        ["Maximum compiler lines with owned absolute .lean source", census["maxima"].get("owned_source", 0)],
        ["Maximum compiler lines with another absolute .lean source", census["maxima"].get("other_source", 0)],
        ["Maximum lines with unresolved source/cwd", census["maxima"].get("unresolved", 0)],
        ["Samples containing another absolute .lean source", census["samples_with_other_source"]]])
    if census["foreign_source_paths"]:
        load_note += "\n\nObserved source paths from concurrent compiler processes (up to ten):\n\n" + "\n".join(
            "- `" + path + "`" for path in census["foreign_source_paths"][:10])
    sections = []
    sections.append(("1. Setup/provenance", f"UTC window: `{s['start_utc']}` → `{s['end_utc']}`. "
        f"Measured Git commit: `{s['commit']}`. Target: `All`.\n\n"
        f"Host: `{s['host']}`; logical CPUs: {s.get('cpu_count', 'unavailable')}; "
        f"memory bytes: {s.get('memory_bytes', 'unavailable')}.\n\n"
        f"Lean: `{s['lean']}`. Lake: `{s['lake']}`. GNU time: `{s['time_tool'].splitlines()[0]}`. "
        f"Environment: `{s['environment']}`.\n\n"
        f"Workflow: [lean-elaboration-test]({SKILL_BASE}/skills/lean-elaboration-test/SKILL.md) and "
        f"[lean-elaboration]({SKILL_BASE}/skills/lean-elaboration/SKILL.md), pinned at `{SKILL_PIN}`.\n\n"
        + load_note + "\n\nThe raw inventory can include this run and concurrent projects. "
        "Absolute source paths support the limited attribution above; a Lake command alone does not disclose its cwd. "
        "Presence alone is informational; "
        "it neither invalidates the run nor establishes artifact mutation or causality.\n\n" + comparison(current, prior)))
    excluded = re.search(r"comment-only files \(excluded\):\s*(\d+)",
                         (current.directory / "skill-size.txt").read_text())
    sections.append(("2. Size snapshot", table(["Metric", "Measured", "Prior", "Δ"], [
        ["Owned .lean files", own_count, old.get("module_count", "—"), delta(own_count, old.get("module_count"), 0)],
        ["Total source lines", s["total_lines"], old.get("total_lines", "—"), delta(s["total_lines"], old.get("total_lines"), 0)],
        ["Non-comment code lines", s["code_lines"], old.get("code_lines", "—"), delta(s["code_lines"], old.get("code_lines"), 0)],
        ["Comment-only files excluded", int(excluded[1]) if excluded else "unavailable", "—", "—"],
        ["Legacy files without module header", s["legacy_header_files"], old.get("legacy_header_files", "—"), "—"]]) +
        "\n\nSizes and first declared namespaces come from `git archive` at the measured commit. "
        f"The `All` import closure covers all {own_count} owned modules; actual compilation count is recorded below. "
        "The pinned skill prescribes zero files without a `module` header. This project deliberately adapts "
        "that strict requirement to its existing Lean file format; the nonzero legacy count is disclosed, "
        "and no module-format migration was performed."))
    metric_rows = [
        ("GNU-time elapsed wall seconds", r["wall"], oldr.get("wall")),
        ("Wrapper observed wall seconds", s["wall_seconds_observed"], old.get("wall_seconds_observed")),
        ("GNU-time user CPU seconds", r["user"], oldr.get("user")),
        ("GNU-time system CPU seconds", r["system"], oldr.get("system")),
        ("GNU-time total CPU seconds", r["cpu"], oldr.get("cpu")),
        ("Actual CPU / GNU wall", ratio(r["cpu"], wall), ratio(oldr.get("cpu"), oldr.get("wall"))),
        ("Maximum process peak RSS (KiB)", r["rss_kib"], oldr.get("rss_kib")),
        ("Logged elapsed job-duration sum seconds", logged, old_logged),
        ("Logged duration sum / GNU wall", ratio(logged, wall), ratio(old_logged, oldr.get("wall"))),
        ("Actual CPU ms / code line", ratio(r["cpu"] * 1000 if r["cpu"] is not None else None, s["code_lines"]),
         ratio(oldr.get("cpu") * 1000 if oldr.get("cpu") is not None else None, old.get("code_lines"))),
        ("Logged elapsed ms / code line", ratio(logged * 1000, s["code_lines"]),
         ratio(old_logged * 1000 if old_logged is not None else None, old.get("code_lines")))]
    headline = table(["Metric", "Measured", "Prior", "Δ"],
                     [[name, number(a), number(b), delta(a, b)] for name, a, b in metric_rows])
    headline += "\n\n" + table(["Metric", "Measured", "Prior"], [
        ["GNU-time %CPU", r["cpu_percent"], oldr.get("cpu_percent", "—")],
        ["Configured LEAN_NUM_THREADS", s["environment"].get("LEAN_NUM_THREADS", "—"), old.get("environment", {}).get("LEAN_NUM_THREADS", "—")],
        ["Lake total jobs (includes cached upstream jobs)", s["lake_jobs"], old.get("lake_jobs", "—")],
        ["Unique owned modules actually compiled", len(current.compiled), len(prior.compiled) if prior else "—"],
        ["Owned timings visible", f"{len(current.timings)}/{own_count} ({len(current.timings) / own_count:.1%})", "—"]])
    headline += ("\n\nLake's displayed Built durations are rounded wall-time estimates of individual jobs, "
                 "not measured CPU. Their sum and duration/wall ratio describe overlapping logged work; "
                 "they must not be called cumulative CPU or actual CPU parallelism. GNU time supplies "
                 "the separate CPU totals. Peak RSS is the maximum process peak reported by GNU time, "
                 "not simultaneous memory summed across compiler workers. `LEAN_NUM_THREADS` records "
                 "runtime configuration, not a measured cap on concurrent compiler processes.\n\n"
                 f"Weighted owned import-chain estimate: {number(chain_seconds)} s across {len(chain)} modules. "
                 f"CPU/8 reference work floor: {number(ratio(r['cpu'], 8))} s; CPU/2 nominal pool reference: "
                 f"{number(ratio(r['cpu'], 2))} s. These references do not establish the actual scheduling bound. "
                 "The chain uses rounded observed durations and misses untimed work; it is an estimate, "
                 "not a verified wall-time lower bound.\n\n`" + " → ".join(chain) + "`")
    sections.append(("3. Headline table", headline))
    warnings = Counter(re.sub(r"^\S+\.lean:\d+:\d+:\s*", "", line)
                       for line in re.findall(r"(?m)^warning:\s*(.*)$", current.log))
    overrides, oversized = [], []
    for row in current.sizes:
        source = masked_source(current.sources[row["source"]])
        settings = re.findall(r"(?m)^\s*set_option\s+((?:synthInstance\.)?maxHeartbeats)\s+(\d+)", source)
        if settings:
            overrides.append((row["module"], settings))
        if row["lines"] > 1500:
            oversized.append(row["module"])
    health = table(["Check", "Recorded result"], [
        ["Build exit code", s["exit_code"]], ["Errors", s["errors"]],
        ["Sorry messages / authorized", f"{s['sorry_messages']} / 0"], ["Warnings", s["warnings"]],
        ["Upstream compilation records", len(s["upstream_compilations"])],
        ["Dependency path/size/mtime digest unchanged", s["dependency_artifacts_unchanged"]],
        ["Compiled all owned modules", current.compiled == {x["module"] for x in current.sizes}],
        ["Files above 1,500 lines", len(oversized)],
        ["Files containing heartbeat overrides", len(overrides)],
        ["Heartbeat override commands", sum(len(x[1]) for x in overrides)]])
    if warnings:
        health += "\n\n" + table(["Warning message kind", "Count"], warnings.most_common(10))
    health += ("\n\nOnly exact project-owned artifacts were invalidated. No `lake clean`, `lake update`, "
               "or upstream compilation is part of this procedure. Existing heartbeat overrides are "
               "a disclosed census, not a performance improvement. The dependency guard compares "
               "path, size, and mtime metadata rather than every artifact's content hash.")
    sections.append(("4. Build health", health))
    tiers = table(["Rounded logged duration tier", "Measured files", "Prior", "Δ"], [
        [f"≥{tier} s", sum(t >= tier for t in current.timings.values()),
         sum(t >= tier for t in prior.timings.values()) if prior else "—",
         delta(sum(t >= tier for t in current.timings.values()),
               sum(t >= tier for t in prior.timings.values()) if prior else None, 0)]
        for tier in (10, 20, 30, 40)])
    size_map = {x["module"]: x for x in current.sizes}
    worst = sorted(current.timings.items(), key=lambda x: -x[1])[:30]
    tiers += "\n\n" + table(["Rank", "Module", "Logged elapsed s", "Code lines", "Elapsed ms/line", "Prior s", "Δ s"], [
        [i, module, number(seconds), size_map[module]["code_lines"],
         number(ratio(seconds * 1000, size_map[module]["code_lines"])),
         number(prior.timings.get(module) if prior else None),
         delta(seconds, prior.timings.get(module) if prior else None)]
        for i, (module, seconds) in enumerate(worst, 1)])
    tiers += "\n\nThreshold classification uses rounded displayed durations; a boundary file may lie on either side before rounding."
    sections.append(("5. Heavy tail", tiers))
    groups, previous = current.groups(), prior.groups() if prior else {}
    group_rows = []
    for name in sorted(groups.keys() | previous.keys(), key=lambda n: -groups.get(n, {}).get("seconds", 0)):
        a, b = groups.get(name, {}), previous.get(name, {})
        group_rows.append([name, a.get("modules", 0), a.get("code_lines", 0), number(a.get("seconds", 0)),
                           number(b.get("seconds") if prior else None),
                           delta(a.get("seconds", 0), b.get("seconds", 0) if prior else None)])
    sections.append(("6. Per-namespace work", "Each module is assigned once, to its first declared namespace in the measured Git source; "
        "facades without one are grouped at root. A module may later open other namespaces. "
        "This grouping aggregates rounded elapsed job durations, not CPU.\n\n" +
        table(["First declared namespace", "Modules", "Code lines", "Logged elapsed s", "Prior s", "Δ s"], group_rows)))
    sections.append(("7. Own-file profiles", profile_section(profiles)))
    findings = (notes.strip() if notes else
                "Measurement only: no cleanup intervention or mathematical change is claimed by this generator. "
                "Screen the heavy tail with serial warm profiles. Apply a named lever only after phase attribution "
                "and retain it only with the skill's per-intervention A/B evidence.")
    sections.append(("8. Findings ranked by actionability", findings))
    sections.append(("9. What is not established", "Logged job durations do not establish per-file CPU, exclusive elaboration cost, "
        "or a cleanup speedup. The global process inventory does not establish contention causality. "
        "Peak process RSS does not establish aggregate memory demand. The weighted import chain and "
        "CPU/core references are scheduling models, not measured critical-path bounds. Missing profiles "
        "leave tail causes unclassified; large unattributed elaboration requires detailed trace attribution. "
        "The legacy module-header exception is an explicit adaptation, not satisfaction of the skill's "
        "zero-header-deficit rule. Successful elaboration does not by itself refresh the independent "
        "comparator/nanoda certificates or their historical pins."))
    env = " ".join(shlex.quote(k + "=" + v) for k, v in sorted(s["environment"].items()))
    command = env + " " + shlex.join(s["command"])
    repeat_command = shlex.join(["python3", "scripts/benchmark_elaboration.py", "--output",
        ".verify-work/elaboration-campaign/NEW_MEASUREMENT", "--threads",
        s["environment"].get("LEAN_NUM_THREADS", "2"), "--size-helper",
        ".verify-work/elaboration-campaign/skills/count_lean_lines.py", "--time", s["command"][0]])
    methodology = ("Recorded timed command (working directory: `formalization`):\n\n```sh\n" + command + "\n```\n\n"
        "The project-only wrapper records the commit, rejects uncommitted owned proof/config changes, "
        "archives source sizes, guards dependency artifacts, invalidates only exact owned module artifacts, "
        "and records process samples. For a repeat, choose a fresh output directory:\n\n```sh\n"
        + repeat_command + "\n```\n\n"
        "Both snapshots use `LAKE_ARTIFACT_CACHE=false`; upstream oleans remain inputs. "
        "Record the same host, GNU-time version, and thread setting. Profile serially after the build, "
        "then summarize the raw text/trace files before rendering this report.\n\n"
        "```sh\npython3 scripts/report_elaboration.py --benchmark BENCHMARK_DIRECTORY "
        "--profiles PROFILE_SUMMARY_DIRECTORY --prior PRIOR_BENCHMARK_DIRECTORY --output REPORT.md\n```")
    sections.append(("10. Methodology", methodology))
    artifacts = []
    for filename in ("summary.json", "size.json", "imports.json", "skill-size.txt", "build.log",
                     "resources.txt", "process-samples.json", "dependencies-before.json", "dependencies-after.json", "invalidated.json"):
        path = current.directory / filename
        if path.is_file():
            artifacts.append([filename, hashlib.sha256(path.read_bytes()).hexdigest()])
    pointers = f"Measurement directory: `{current.directory}`. "
    pointers += (f"Prior benchmark: `{prior.directory}` at `{prior.summary['commit']}`; role: prior measurement for trend comparison."
                 if prior else "No prior benchmark supplied.")
    pointers += "\n\n" + table(["Evidence file", "SHA-256"], artifacts)
    if profiles and profiles.get("report_input_path"):
        profile_path = Path(profiles["report_input_path"])
        pointers += (f"\n\nProfile summary: `{profile_path}`; SHA-256: "
                     f"`{hashlib.sha256(profile_path.read_bytes()).hexdigest()}`. "
                     "Its per-profile input hashes bind the raw text and trace evidence.")
    sections.append(("11. Pointers", pointers))
    date = s["start_utc"][:10]
    return f"# Cloning elaboration report — {date}\n\n" + "\n\n".join(
        f"## {heading}\n\n{body}" for heading, body in sections) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--benchmark", type=Path, required=True)
    parser.add_argument("--profiles", type=Path, help="Completed profile-summary JSON or its directory")
    parser.add_argument("--prior", type=Path, help="Prior benchmark directory")
    parser.add_argument("--notes", type=Path, help="Reviewed findings/cleanup notes in Markdown")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    current = Snapshot.read(args.benchmark)
    prior = Snapshot.read(args.prior) if args.prior else None
    profiles = load_profiles(args.profiles)
    raw_inputs = {p.resolve() for p in current.directory.iterdir() if p.is_file()}
    if prior:
        raw_inputs.update(p.resolve() for p in prior.directory.iterdir() if p.is_file())
    if args.profiles:
        p = args.profiles.resolve()
        if p.is_dir():
            raw_inputs.update(x.resolve() for x in p.iterdir() if x.is_file())
        else:
            raw_inputs.add(p)
    if args.notes:
        raw_inputs.add(args.notes.resolve())
    if args.output.resolve() in raw_inputs:
        parser.error("Refusing to overwrite measurement inputs or reviewed notes")
    report = render(current, profiles, prior, args.notes.read_text() if args.notes else None)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(report)
    print(f"Rendered elaboration report: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
