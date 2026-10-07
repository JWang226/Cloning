# Cloning elaboration cleanup comparison — 6 October 2026 campaign

The dead-code sweep preceded the first test. Two measured proof conversions were then replaced, followed by the complete second test and serial warm profiles. The before/after filename date identifies the campaign that started on 6 October in Pacific time; precise UTC windows below remain the timing record.

## Complete cold snapshots

Before: `cbb2fd2007ae367e201d4a6ac7c069899db90dbd`; `2026-10-06T22:44:14.173734+00:00` → `2026-10-07T02:09:30.814062+00:00`.

After: `3eb587e0f00748c3a9b63f9eeedc1646e4cb77be`; `2026-10-07T02:51:09.215352+00:00` → `2026-10-07T03:58:20.185742+00:00`.

| Recorded metric | Before | After | After − before | Observed reduction |
| --- | --- | --- | --- | --- |
| GNU elapsed wall seconds | 12,316.00 | 4,030.00 | -8,286.00 | 67.28% |
| GNU user CPU seconds | 9,052.61 | 6,489.59 | -2,563.02 | 28.31% |
| GNU system CPU seconds | 4,517.38 | 2,301.81 | -2,215.57 | 49.05% |
| GNU total CPU seconds | 13,569.99 | 8,791.40 | -4,778.59 | 35.21% |
| Maximum-process RSS KiB | 3,396,256.00 | 3,416,144.00 | 19,888.00 | — |
| Owned modules | 994.00 | 994.00 | 0.00 | — |
| Native CPU / wall ratio | 1.10 | 2.18 | 1.08 | — |
| Physical lines | 111,939.00 | 111,941.00 | 2.00 | — |
| Code lines | 92,405.00 | 92,407.00 | 2.00 | — |
| Legacy header files | 994.00 | 994.00 | 0.00 | — |
| Whole-log warnings | 499.00 | 499.00 | 0.00 | — |
| Rounded elapsed job sum seconds | 24,284.90 | 7,917.50 | -16,367.40 | — |

These are two complete project-only snapshots on a shared host. Their aggregate wall/CPU differences are observed trends; they do not assign the entire change to the cleanup. Native CPU divided by GNU wall is 1.10 before and 2.18 after. This utilization difference is part of the scheduling/load limitation. The separate repeated controls below establish local compiler savings.

## Controlled proof-body results

| Intervention | Bare wall A s | Bare wall B s | Wall lower | Bare CPU A s | Bare CPU B s | CPU lower |
| --- | --- | --- | --- | --- | --- | --- |
| [werner-trace-bridge](formalization/verification/elaboration/2026-10-06/interventions/werner-trace-bridge/verdict.json) | 39.54 | 6.74 | 82.95% | 43.14 | 8.88 | 79.42% |
| [weyl-bridge](formalization/verification/elaboration/2026-10-06/interventions/weyl-bridge/verdict.json) | 106.89 | 6.62 | 93.81% | 110.05 | 9.62 | 91.26% |

| Intervention | Traced tactic A s | Traced tactic B s | Phase lower | Repeated A/B runs |
| --- | --- | --- | --- | --- |
| werner-trace-bridge | 38.80 | 2.46 | 93.66% | 12 |
| weyl-bridge | 106.00 | 1.48 | 98.60% | 12 |

Each experiment used three alternating pairs with profiling and three bare pairs, 12 successful A/B runs each. Bare runs omit trace/profile/statistics flags and provide native GNU CPU evidence. Traced controls use `pp=false` in both arms; campaign warm profiles use `pp=true`. Their exclusive phase times are elapsed measurements. The ignored body-only sorry diagnostics confirmed proof cost and were excluded from accepted sources and these 24 A/B runs. Neither bare experiment demonstrated an RSS decrease; no memory gain is claimed.

## Exact changes and source/API guard

- Weyl: explicitly rewrite `vectorProjector x = rankOneOperator x x` before the conversion in `integral_weighted_characteristic`.

- Werner: compose `traceCLM_apply`, the channel’s trace-preservation equality, and `traceCLM_apply(...).symm` in `wernerOutput_trace_one`.

The source/API guard covers 994 own files: 992 remain byte-identical; the two changed files remain byte-identical outside those theorem bodies. Public statements, hypotheses, namespace, imports, options, attributes and variables are preserved. All 316 result-index checks are unchanged. [Original guard](formalization/verification/elaboration/2026-10-06/source-api-guard/cleanup-api-source-guard.json) and [publication receipt](formalization/verification/elaboration/2026-10-06/source-api-guard/receipt.json) retain the guard’s historical working-tree context; the measured before/after manifests independently bind the accepted file bytes. This is a source/API guard, not independent proof verification.

## Matched warm profiles

| Matched Firefox module | Before GNU wall s | After GNU wall s | Before native CPU s | After native CPU s |
| --- | --- | --- | --- | --- |
| Cloning.WeylIdlerUniqueness | 193.17 | 8.91 | 194.37 | 11.77 |
| Cloning.PCTHybridMixtureFactor | 33.88 | 29.01 | 32.55 | 30.25 |
| Cloning.WernerPhysicalPullback | 332.29 | 29.66 | 330.47 | 32.10 |
| Cloning.PCTGlobalPhysical | 84.15 | 57.59 | 78.06 | 58.75 |
| Cloning.PCTUnitaryTransportChannels | 10.02 | 6.37 | 6.83 | 5.70 |
| Cloning.InfiniteTraceClass | 24.27 | 16.78 | 47.76 | 34.10 |
| Cloning.Thermal | 6.98 | 5.02 | 12.60 | 9.82 |
| Cloning.AmplifierWeylThermal | 8.97 | 7.19 | 7.09 | 5.99 |
| Cloning.PCTClosedForm | 6.21 | 4.98 | 5.36 | 4.53 |
| Cloning.CloningValueComparisonMonotone | 8.77 | 6.71 | 7.47 | 6.29 |

These single campaign warm runs use Firefox tracing with `pp=true` in both snapshots. They provide matched coverage and diagnostic context; formatting/export and contemporaneous host load can change their process CPU/wall. Only the repeated bare A/B controls above support causal compiler gains. Native CPU is GNU user plus system CPU; GNU wall differs slightly from the runner’s monotonic wrapper wall.

## Additional after-only diagnostics

| Unmatched module | Trace mode | GNU wall s | Native CPU s | Maximum-process RSS KiB |
| --- | --- | --- | --- | --- |
| Cloning.TensorFlatProjectorStateFidelity | firefox | 98.87 | 97.02 | 3,815,216 |
| Cloning.PhysicalFlatConverseReduction | native | 59.14 | 58.99 | 3,250,112 |
| Cloning.TensorCartanChannelCovariance | firefox | 111.86 | 106.08 | 3,371,472 |
| Cloning.TensorCartanStateOperator | firefox | 59.48 | 61.63 | 3,278,368 |
| Cloning.PhysicalFlatPinchingInflation | native | 30.14 | 42.00 | 3,275,648 |

These newly selected cold-top-five modules have no before warm counterpart. Their times do not enter the matched table or the 24 accepted A/B runs. A native entry runs `--profile --stats` with unchanged source/options and guarded setup/imports; it has no Firefox trace, trace-class ranking or Firefox source pointers. Its C++ profile/statistics and successful native compiler execution are useful diagnostic evidence without establishing an intervention gain.

## Preserved failed and exploratory attempts

| Module | Evidence role | Exit | Attempt wrapper wall s | Exclusion reason |
| --- | --- | --- | --- | --- |
| Cloning.PhysicalFlatConverseReduction | failed-profile-attempt | 1 | 62.36 | Untouched module passed the full cold build, but Firefox trace collection hit its existing typeclass and elaboration heartbeat limits. No Firefox export occurred after errors. Excluded from successful cohort. |
| Cloning.PhysicalFlatPinchingInflation | failed-profile-attempt | 1 | 30.74 | Untouched module passed the full cold build, but Firefox trace collection hit its existing typeclass heartbeat limit. No Firefox export occurred after errors. Excluded from successful cohort. |
| Cloning.PhysicalFlatConverseReduction | diagnostic-native-control | 0 | 60.61 | Exploratory native-only control passed, but setup/trace unchanged flags were inherited from the failed record, not remeasured by this driver. Excluded from canonical cohort; the fresh guarded native run is canonical. |

Failed trace wall values describe unsuccessful attempts and are excluded from passing-profile timing comparisons. The preliminary native control is exploratory because its first driver inherited setup/trace guard fields. The canonical native entries above come from freshly guarded runs and remain unmatched after-only diagnostics. No heartbeat budget or proof source changed, and none of these attempts enter the 24 accepted A/B runs.

[Preserved attempt records](formalization/verification/elaboration/2026-10-06/profiles-after/profile-attempts.json) · [Original index/hash/position receipt](formalization/verification/elaboration/2026-10-06/profiles-after/profile-attempts-receipt.json)

The elaboration failures precede Firefox export. Pinned Lean tracing code supplies a plausible instrumentation-allocation mechanism, while the precise trigger remains unmeasured. [Pinned-source analysis and qualifications](formalization/verification/elaboration/2026-10-06/tools/profiler-heartbeat-exception.md)

## Scope, health and measured follow-ups

All 994 own modules compiled in each snapshot; errors/sorry messages are 0/0 before and 0/0 after. Both preserve dependency artifact metadata and have no upstream compilation. Warnings cover the full logs and may include replayed cached upstream messages. The matched warm cohort contains 10 Firefox files; after adds 5 unmatched cold-top-five diagnostics (3 Firefox and 2 native). Own-file diagnostics cover the cold top five plus targeted files, rather than every cold top-30 module or every proof. No broad cache, simp, arithmetic, import split or module-header migration was validated. The legacy-header census is disclosed as a compatibility adaptation of the skill, rather than forcing an unmeasured export/API migration.

Remaining measured leads include mixed elaboration/metavariable costs in PCTHybridMixtureFactor, import costs in PCTGlobalPhysical and PCTUnitaryTransportChannels, and diffuse typeclass work in InfiniteTraceClass. Their precise remedies remain unresolved. Thermal, AmplifierWeylThermal, PCTClosedForm and ComparisonMonotone did not clear the full phase routing floor; the bounded arithmetic calls and static import proposals earned no cleanup credit.

## Interpretation limits

The matched toolchain, configurations, environment overrides and host do not establish identical contemporaneous load. Other projects were active. Profiler formatting/export can inflate whole-process CPU/wall, and cumulative phase/Firefox intervals are elapsed timers with overlapping threads/functions. Rounded Lake job durations are elapsed estimates, not per-file CPU. Peak RSS is the maximum process peak, rather than simultaneous memory summed across workers. The owned weighted import-chain and CPU/core values are scheduling references, not intrinsic observed wall-time lower bounds. The baseline source/configuration stability check is explicitly supplemental; the after runner performed its built-in end check.

## Detailed reports, evidence and reproduction

[Detailed 11-section before report](ELABORATION_REPORT_2026-10-06_BEFORE.md) · [Detailed 11-section after report](ELABORATION_REPORT_2026-10-06_AFTER.md) · [Evidence and fresh reproducer commands](formalization/verification/elaboration/2026-10-06/README.md) · [Evidence manifest](formalization/verification/elaboration/2026-10-06/manifest.json)

This comparison was rendered by small-record publication helpers: [render_final_comparison.py](formalization/verification/elaboration/2026-10-06/tools/render_final_comparison.py) SHA-256 `88dfa8bb54860deadee792d90d204cd9cd934b4ec542108b79f31757b2170a9c`; [comparison_support.py](formalization/verification/elaboration/2026-10-06/tools/comparison_support.py) SHA-256 `159b9b124c3ed13fb31b8c439537e27e306d43da3b7b60caecf8db859b58f1f9`. The detailed reports, measured data and arithmetic remain independently readable; these helpers perform no Lean/checker execution or trace/archive parsing.

Use fresh output directories with pinned dependency caches. The evidence guide gives the project-only benchmark and serial profiler commands. Its accepted-intervention archives retain the variants, commands, tool/setup/import guards, native resource logs, diagnostic labeling and exact patches. Original inherited process paths are omitted from public process census data, with their source digests retained. Rebuilding a matching local setup is required on another host; saved absolute setup paths should not be executed blindly. Historical proof/kernel certificates remain separate from elaboration measurements.
