#!/usr/bin/env python3
"""Lightweight before/after arithmetic and controlled-intervention summaries.

Reads completed small summary/verdict JSON only. It never parses profile traces,
invokes Lean, or compresses evidence. Do not render a public comparison until the
after build and serial profiles pass the report generator's completion gate.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import statistics


def require(value, message):
    if not value:
        raise ValueError(message)


def finite(value):
    if value is None:
        return None
    result = float(value)
    require(math.isfinite(result), "Nonfinite measurement")
    return result


def elapsed(value):
    if value is None:
        return None
    parts = [finite(part) for part in value.split(":")]
    require(1 <= len(parts) <= 3 and all(part >= 0 for part in parts), "Invalid GNU elapsed value")
    return sum(part * 60 ** power for power, part in enumerate(reversed(parts)))


def change(before, after):
    before, after = finite(before), finite(after)
    return {"before": before, "after": after,
            "delta_after_minus_before": None if before is None or after is None else after - before,
            "reduction_percent": None if before is None or after is None or before == 0
                                 else 100 * (before - after) / before}


def resources(summary):
    r = summary["resources"]
    user, system = finite(r.get("User time (seconds)")), finite(r.get("System time (seconds)"))
    wall = elapsed(r.get("Elapsed (wall clock) time (h:mm:ss or m:ss)"))
    cpu = None if user is None or system is None else user + system
    return {"gnu_wall_seconds": wall,
            "observed_wall_seconds": finite(summary.get("wall_seconds_observed")),
            "gnu_user_cpu_seconds": user, "gnu_system_cpu_seconds": system,
            "gnu_total_cpu_seconds": cpu,
            "cpu_wall_ratio": None if cpu is None or wall is None or wall == 0 else cpu / wall,
            "max_process_rss_kib": finite(r.get("Maximum resident set size (kbytes)"))}


def validate_summary(summary):
    require(summary.get("schema") == "cloning-elaboration-test-v1", "Unexpected benchmark schema")
    require(summary.get("exit_code") == 0 and summary.get("errors") == 0 and summary.get("sorry_messages") == 0,
            "Full benchmark did not pass")
    require(summary.get("dependency_artifacts_unchanged") is True and summary.get("upstream_compilations") == [],
            "Upstream cache guard did not pass")
    durations = {row["module"]: finite(row["seconds"]) for row in summary["timings"]}
    require(len(durations) == len(summary["timings"]) == summary["module_count"], "Missing/duplicate owned timings")
    require(all(value >= 0 for value in durations.values()), "Negative duration")
    return durations


def snapshot_comparison(before, after):
    a, b = validate_summary(before), validate_summary(after)
    old, new = resources(before), resources(after)
    metrics = {key: change(old[key], new[key]) for key in old}
    for key in ("module_count", "total_lines", "code_lines", "legacy_header_files", "warnings"):
        metrics[key] = change(before.get(key), after.get(key))
    metrics["rounded_logged_job_seconds"] = change(sum(a.values()), sum(b.values()))
    common = set(a) & set(b)
    shifts = [{"module": name, **change(a[name], b[name])} for name in sorted(common)]
    tiers = {str(t): change(sum(value >= t for value in a.values()), sum(value >= t for value in b.values()))
             for t in (10, 20, 30, 40)}
    checks = {key: before.get(key) is not None and after.get(key) is not None and before.get(key) == after.get(key)
              for key in ("environment", "time_tool", "host", "lean", "lake", "cpu_count", "memory_bytes")}
    return {"schema": "cloning-elaboration-comparison-support-v1", "before_commit": before["commit"],
            "after_commit": after["commit"], "matching_recorded_conditions": checks,
            "metrics": metrics, "heavy_tiers": tiers,
            "module_cohorts": {"common": len(common), "added": sorted(set(b) - set(a)), "removed": sorted(set(a) - set(b))},
            "largest_logged_decreases": sorted(shifts, key=lambda row: row["delta_after_minus_before"])[:15],
            "largest_logged_increases": sorted(shifts, key=lambda row: row["delta_after_minus_before"], reverse=True)[:15],
            "interpretation": "Full-build changes are observed trends; two snapshots on a shared host do not establish causal cleanup savings.",
            "validation_scope": "Summary arithmetic only; the 11-section report generator separately validates source/config archives and completed profiles."}


def intervention(verdict):
    require(verdict.get("decision") in ("accept", "revert", "reject"), "Missing intervention decision")
    rows = verdict["rows"]
    counts = Counter((row["kind"], row["arm"]) for row in rows)
    require(all(counts.get((kind, arm), 0) >= 3 for kind in ("bare", "profile") for arm in ("A", "B")),
            "Three repeated bare and profile runs required in both arms")
    for row in rows:
        require(abs(finite(row["cpu"]) - finite(row["user"]) - finite(row["system"])) < 1e-6,
                "A row total CPU differs from its native user+system CPU")
    result = {"decision": verdict["decision"], "run_count": len(rows),
              "group_counts": {kind + ":" + arm: counts[(kind, arm)] for kind, arm in sorted(counts)},
              "modes": {}, "inherited_notes": verdict.get("notes", []),
              "validation_scope": "Arithmetic from recorded verdict rows; exit/input/API claims require the original raw execution records and patch."}
    for kind in ("bare", "profile"):
        groups = {arm: [row for row in rows if row["kind"] == kind and row["arm"] == arm] for arm in ("A", "B")}
        metrics = {}
        for key in ("wall_seconds", "user", "system", "cpu", "rss_kib"):
            # A median of per-run total CPU need not equal median user+median system.
            metrics[key] = change(statistics.median(finite(row[key]) for row in groups["A"]),
                                  statistics.median(finite(row[key]) for row in groups["B"]))
        phases = sorted(set().union(*(row.get("exclusive_phase_ms", {}) for row in rows if row["kind"] == kind)))
        phase_changes = {}
        for phase in phases:
            values = {arm: [finite(row["exclusive_phase_ms"][phase]) for row in groups[arm]
                            if phase in row.get("exclusive_phase_ms", {})] for arm in ("A", "B")}
            if all(len(values[arm]) == len(groups[arm]) for arm in ("A", "B")):
                phase_changes[phase] = change(statistics.median(values["A"]), statistics.median(values["B"]))
        result["modes"][kind] = {"median_metrics": metrics, "median_exclusive_elapsed_phases_ms": phase_changes}
    result["interpretation"] = ("Use repeated bare native CPU as compiler evidence. Matched profile phases explain the intervention; "
                                "they are elapsed timers. A/B pp=false and campaign pp=true profiles are separate comparisons. "
                                "Single-file savings do not predict a full-build reduction; max-process RSS is not aggregate memory.")
    return result


def read(path):
    return json.loads(path.read_text())


def file_hash(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--before", type=Path, required=True, help="completed benchmark directory")
    p.add_argument("--after", type=Path, required=True, help="completed benchmark directory")
    p.add_argument("--intervention", type=Path, action="append", default=[], help="completed small verdict JSON")
    p.add_argument("--output", type=Path, required=True, help="fresh derived JSON; never replaces evidence")
    args = p.parse_args()
    require(not args.output.exists(), "Refusing to overwrite comparison evidence")
    paths = [args.before / "summary.json", args.after / "summary.json", *args.intervention]
    configs = [args.before / "source-config-hashes.json", args.after / "source-config-hashes.json"]
    require(all(path.is_file() for path in paths), "Wait for completed after inputs")
    result = snapshot_comparison(read(paths[0]), read(paths[1]))
    config_names = {"formalization/lean-toolchain", "formalization/lakefile.toml", "formalization/lake-manifest.json"}
    config_records = [{k: v for k, v in read(path).items() if k in config_names}
                      if path.is_file() else {} for path in configs]
    result["configuration_equivalence"] = {"all_three_config_hashes_recorded": all(set(x) == config_names for x in config_records),
                                             "config_hashes_match": all(set(x) == config_names for x in config_records) and config_records[0] == config_records[1]}
    result["input_sha256"] = {str(path): file_hash(path) for path in [*paths, *configs] if path.is_file()}
    result["comparison_helper_sha256"] = file_hash(Path(__file__))
    result["interventions"] = [{"record": str(path), **intervention(read(path))} for path in args.intervention]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x") as output:
        output.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print("Derived comparison arithmetic written; causal statements remain limited to their paired evidence.")

if __name__ == "__main__":
    main()
