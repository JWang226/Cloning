# Elaboration evidence

These records contain completed cold own-module builds and serial warm profiles.
Benchmark records are unchanged. Process inventories contain UTC/counts only;
the original omitted records' hashes are in manifest.json. Public profile indexes
remove inherited path-valued environment fields. Summaries are regenerated from
raw logs, native GNU resources and available Firefox traces, with source copies
verified against each source_sha256. Before has ten successful Firefox profiles;
after has thirteen Firefox profiles and two guarded native profile/statistics runs.
The two native runs have no Firefox trace or before warm counterpart.

[Preserved attempts](profiles-after/profile-attempts.json) and their
[original-index receipt](profiles-after/profile-attempts-receipt.json) retain two
failed trace attempts and the excluded exploratory native control. They do not
enter successful-profile timing comparisons. The [heartbeat analysis](tools/profiler-heartbeat-exception.md)
is a preserved historical note written before the guarded controls; its old
`profiles-after/profiles.json` reference describes that earlier stage. Current
failures are selected by the separate attempt records, while `profiles-after/profiles.json`
selects the completed mixed cohort.

Detailed traces, logs, resources, source copies, matching Lake setups, build traces
and import contexts are compressed in each profiles-*.tar.gz. Supplemental sets:
interventions/weyl-bridge, interventions/werner-trace-bridge. Every member has a SHA-256, size and role in manifest.json; each
archive was safely extracted and checked against the exact member set before
publication. Task-specific source/setup/import paths remain as measurement
provenance. Saved setups should be replaced by locally generated ones for a new run.

Intervention receipts retain module, arm, mode and measured repetition. Traced runs
and bare GNU controls have separate summaries; bare controls have no Firefox data.
Diagnostic sorry snapshots are explicitly labeled outside production. Plans,
verdicts (including rejected candidates), driver bytes, patches and source/artifact
hashes are preserved, with original hashes for redacted metadata.

The source-api-guard/ directory preserves the original source/API guard and driver.
Its receipt labels the driver digest as captured at publication, retains the
historical Git context, and binds candidate bytes to accepted intervention
snapshots. This supplemental source guard does not replace proof verification.


The copied measurement helper and elaboration guides are by
[Scott Armstrong (`scottnarmstrong`)](https://github.com/scottnarmstrong), from
[LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/tree/70bb859295edc2abb9ad81f8f6e31ab2adf8ca07), under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). Their contents are
unmodified. [Attribution](skills/ATTRIBUTION.md) and [provenance](skills/provenance.json)
map each pinned original source path to its local filename and digest; the exact
upstream [license and warranty disclaimer](skills/LICENSE) are preserved.

From a Git checkout containing the recorded measured commits, extract the profile
archives into this evidence directory (their members include the relative prefix).
For example, run `tar -xzf EVIDENCE_DIRECTORY/profiles-before.tar.gz -C EVIDENCE_DIRECTORY`.
Keep its small profiles-*/summary.json and profiles.json files in place. Then:

```sh
python3 scripts/report_elaboration.py --benchmark EVIDENCE_DIRECTORY/before --profiles EVIDENCE_DIRECTORY/profiles-before --portable --require-complete --output ELABORATION_REPORT_BEFORE.md
python3 scripts/report_elaboration.py --benchmark EVIDENCE_DIRECTORY/after --prior EVIDENCE_DIRECTORY/before --profiles EVIDENCE_DIRECTORY/profiles-after --portable --require-complete --output ELABORATION_REPORT_AFTER.md
python3 scripts/summarize_elaboration_profiles.py --profiles EVIDENCE_DIRECTORY/profiles-before --output .verify-work/cloning-profile-summary-review.json
```

For a fresh measurement with populated pinned dependency caches and GNU time
available as gtime, use fresh output directories from the repository root. The
commands below re-run the five recorded after cold leaders in separate modes.
Default `--top 5` Firefox collection can hit unchanged heartbeat limits and stops
at its first failure. Preserve that failed directory; run remaining selected
Firefox modules and guarded native fallbacks in new directories. These outputs
retain separate indexes and summaries; the published canonical index records the
historical combined cohort.

```sh
python3 scripts/benchmark_elaboration.py --output .verify-work/elaboration-reproduce --threads 2 --size-helper EVIDENCE_DIRECTORY/skills/count_lean_lines.py --time gtime
python3 scripts/profile_elaboration.py --benchmark .verify-work/elaboration-reproduce --output .verify-work/elaboration-reproduce-firefox --modules Cloning.TensorFlatProjectorStateFidelity Cloning.TensorCartanChannelCovariance Cloning.TensorCartanStateOperator --threads 2 --time gtime
python3 scripts/summarize_elaboration_profiles.py --profiles .verify-work/elaboration-reproduce-firefox
python3 scripts/profile_elaboration.py --benchmark .verify-work/elaboration-reproduce --output .verify-work/elaboration-reproduce-native --modules Cloning.PhysicalFlatConverseReduction Cloning.PhysicalFlatPinchingInflation --trace-mode native --threads 2 --time gtime
python3 scripts/summarize_elaboration_profiles.py --profiles .verify-work/elaboration-reproduce-native
```

The recorded commands, commits, environment overrides and configuration hashes
identify historical inputs; publication helper copies in tools/ identify the
bundling/reconstruction version, and are not proof that those versions were used
during the original timed processes. Historical reproduction requires the recorded
proof/config state and compatible helpers; rebuild local setups instead of running
host-specific saved paths. Cold Lake job durations are rounded elapsed estimates.
Profiler intervals can overlap and are not native CPU time. GNU peak RSS is a
maximum process peak rather than aggregate concurrent memory.
