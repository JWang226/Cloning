# Cloning elaboration report — 2026-10-07

## 1. Setup/provenance

UTC window: `2026-10-07T02:51:09.215352+00:00` → `2026-10-07T03:58:20.185742+00:00`. Measured Git commit: `3eb587e0f00748c3a9b63f9eeedc1646e4cb77be`. Target: `All`.

Host: `Darwin Mac.attlocal.net 27.2.0 Darwin Kernel Version 27.2.0: Tue Sep 29 21:45:37 PDT 2026; root:xnu-13432.40.177.0.3~56/RELEASE_ARM64_T8112 arm64`; logical CPUs: 8; memory bytes: 17179869184.

Lean: `Lean (version 4.29.0-rc6, arm64-apple-darwin24.6.0, commit 00659f8e6071d7e46131ed643bf8003b99b044e9, Release)`. Lake: `Lake version 5.0.0-src+00659f8 (Lean version 4.29.0-rc6)`. GNU time: `time (GNU Time) 1.10`. Environment: `{'LAKE_ARTIFACT_CACHE': 'false', 'LEAN_NUM_THREADS': '2'}`.

Workflow: [lean-elaboration-test](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/70bb859295edc2abb9ad81f8f6e31ab2adf8ca07/skills/lean-elaboration-test/SKILL.md) and [lean-elaboration](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/70bb859295edc2abb9ad81f8f6e31ab2adf8ca07/skills/lean-elaboration/SKILL.md), pinned at `70bb859295edc2abb9ad81f8f6e31ab2adf8ca07`.

| Global process inventory | Observed |
| --- | --- |
| Samples | 399 |
| Maximum total Lean/Lake lines | 5 |
| Maximum compiler lines with owned absolute .lean source | 2 |
| Maximum compiler lines with another absolute .lean source | 0 |
| Maximum lines with unresolved source/cwd | 3 |
| Samples containing another absolute .lean source | 0 |

The public inventory reports counts and omits unrelated paths and command lines. The raw inventory can include this run and concurrent projects. Absolute source paths support the limited attribution above; a Lake command alone does not disclose its cwd. Presence alone is informational; it neither invalidates the run nor establishes artifact mutation or causality. This report uses redacted count evidence; the original process samples are omitted from the public bundle.

Host, environment, and timing tool are **matched**. Measured configuration hashes match: True (missing manifests do not establish configuration equivalence). Contention screens: user CPU down while logged duration sum rises: False; logged-duration/wall ratio rises >20%: False; same-module durations move in opposite directions by >10%: True (41 up, 804 down). Fewer than two screens fire; this does not establish absence of contention. Growth-only CPU prediction Δcode lines × prior CPU/code line: 0.29 s; actual GNU-time CPU change: -4,778.59 s. Process inventory and these heuristics do not identify the cause of a timing change. Two snapshots cannot establish a three-report monotonic trend.

## 2. Size snapshot

| Metric | Measured | Prior | Δ |
| --- | --- | --- | --- |
| Owned .lean files | 994 | 994 | +0 |
| Total source lines | 111941 | 111939 | +2 |
| Non-comment code lines | 92407 | 92405 | +2 |
| Comment-only files excluded | 0 | — | — |
| Legacy files without module header | 994 | 994 | — |

Sizes and first declared namespaces come from `git archive` at the measured commit. The `All` import closure covers all 994 owned modules; actual compilation count is recorded below. The pinned skill prescribes zero files without a `module` header. This project deliberately adapts that strict requirement to its existing Lean file format; the nonzero legacy count is disclosed, and no module-format migration was performed.

## 3. Headline table

| Metric | Measured | Prior | Δ |
| --- | --- | --- | --- |
| GNU-time elapsed wall seconds | 4,030.00 | 12,316.00 | -8,286.00 |
| Wrapper observed wall seconds | 4,030.93 | 12,316.51 | -8,285.58 |
| GNU-time user CPU seconds | 6,489.59 | 9,052.61 | -2,563.02 |
| GNU-time system CPU seconds | 2,301.81 | 4,517.38 | -2,215.57 |
| GNU-time total CPU seconds | 8,791.40 | 13,569.99 | -4,778.59 |
| Actual CPU / GNU wall | 2.18 | 1.10 | +1.08 |
| Maximum process peak RSS (KiB) | 3,416,144.00 | 3,396,256.00 | +19,888.00 |
| Logged elapsed job-duration sum seconds | 7,917.50 | 24,284.90 | -16,367.40 |
| Logged duration sum / GNU wall | 1.96 | 1.97 | -0.01 |
| Actual CPU ms / code line | 95.14 | 146.85 | -51.72 |
| Logged elapsed ms / code line | 85.68 | 262.81 | -177.13 |

| Metric | Measured | Prior |
| --- | --- | --- |
| GNU-time %CPU | 218% | 110% |
| Configured LEAN_NUM_THREADS | 2 | 2 |
| Lake total jobs (includes cached upstream jobs) | 4563 | 4563 |
| Unique owned modules actually compiled | 994 | 994 |
| Owned timings visible | 994/994 (100.0%) | — |

Lake's displayed Built durations are rounded wall-time estimates of individual jobs, not measured CPU. Their sum and duration/wall ratio describe overlapping logged work; they must not be called cumulative CPU or actual CPU parallelism. GNU time supplies the separate CPU totals. Peak RSS is the maximum process peak reported by GNU time, not simultaneous memory summed across compiler workers. `LEAN_NUM_THREADS` records runtime configuration, not a measured cap on concurrent compiler processes.

Weighted owned import-chain estimate: 911.10 s across 81 modules. CPU/8 reference work floor: 1,098.92 s; CPU/2 nominal pool reference: 4,395.70 s. These references do not establish the actual scheduling bound. The chain uses rounded observed durations and misses untimed work; it is an estimate, not a verified wall-time lower bound.

`Cloning.InfiniteTraceClass → Cloning.InfiniteHilbertSchmidt → Cloning.InfiniteTraceClassBasis → Cloning.InfiniteTraceClassIdeal → Cloning.InfiniteTraceClassNormBounds → Cloning.InfiniteTraceClassSpace → Cloning.InfiniteTraceClassBanach → Cloning.InfiniteTraceClassAlgebra → Cloning.InfiniteTraceClassPositive → Cloning.InfiniteTraceClassChannels → Cloning.InfiniteTraceClassCutoff → Cloning.InfiniteCompletelyPositive → Cloning.InfiniteChannelTraceRepair → Cloning.InfiniteIsometricChannel → Cloning.InfiniteRectangularKraus → Cloning.OccupationChannel → Cloning.ComplexCoherent → Cloning.CoherentKernel → Cloning.CoherentContinuity → Cloning.UniformCoherent → Cloning.GeneralCoherentConvergence → Cloning.GeneralCoherentLimits → Cloning.GeneralCoherentChannels → Cloning.GeneralCoherentMixture → Cloning.PCTWernerMixture → Cloning.PCTPartialTrace → Cloning.PCTTensorFrame → Cloning.TensorLieGenerators → Cloning.TensorLieRelations → Cloning.TensorLieHighestWeight → Cloning.TensorLieFiltration → Cloning.TensorLieLeibniz → Cloning.TensorWedge → Cloning.TensorWedgeHighest → Cloning.TensorPartitionHighest → Cloning.TensorCyclicSector → Cloning.TensorCyclicSectorIrreducible → Cloning.TensorCyclicSectorOperators → Cloning.TensorCyclicSectorTensorPower → Cloning.TensorCyclicSectorTransvection → Cloning.TensorCyclicSectorCovariance → Cloning.TensorHighestExtractionBasic → Cloning.TensorHighestExtraction → Cloning.TensorSchurDecompositionData → Cloning.TensorSchurDecomposition → Cloning.TensorSchurDecompositionIsometry → Cloning.TensorSchurDecompositionTrace → Cloning.TensorSchurDecompositionPMF → Cloning.TensorSchurDecompositionMultiplicity → Cloning.TensorSchurDecompositionBounds → Cloning.TensorSchurDecompositionCasimir → Cloning.TensorSchurDecompositionCharacter → Cloning.TensorSchurDecompositionRadialTrace → Cloning.TensorSchurDecompositionRootSum → Cloning.TensorSchurDecompositionRadialEquation → Cloning.TensorSchurDecompositionCharacterSpectrum → Cloning.TensorSchurDecompositionWeylCharacter → Cloning.WeylCharacterDimensionPhysical → Cloning.TensorFlatProjectorLaw → Cloning.TensorFlatProjectorEmbedding → Cloning.TensorFlatProjectorNaturality → Cloning.TensorFlatProjectorSupport → Cloning.TensorFlatProjectorSector → Cloning.TensorFlatProjectorRestriction → Cloning.TensorFlatProjectorSectorSupport → Cloning.TensorFlatProjectorState → Cloning.TensorFlatProjectorMatrix → Cloning.TensorFlatProjectorCompression → Cloning.TensorFlatProjectorFidelity → Cloning.TensorFlatProjectorTraceClass → Cloning.TensorFlatProjectorGibbs → Cloning.TensorFlatProjectorGibbsState → Cloning.TensorFlatProjectorStateFidelity → Cloning.TensorFlatProjectorTransitionCovariance → Cloning.TensorFlatProjectorChannel → Cloning.TensorFlatProjectorAchievability → Cloning.TensorRankOneCoupling → Cloning.TensorRankOneTransition → Cloning.TensorRankOneGlobal → Cloning → All`

## 4. Build health

| Check | Recorded result |
| --- | --- |
| Build exit code | 0 |
| Errors | 0 |
| Sorry messages / authorized | 0 / 0 |
| Total logged warnings | 499 |
| Upstream compilation records | 0 |
| Dependency path/size/mtime digest unchanged | True |
| Source/config manifest bound to measured commit | True |
| Source/config byte stability | True (runner start/end check) |
| Compiled all owned modules | True |
| Files above 1,500 lines | 0 |
| Files containing heartbeat overrides | 742 |
| Heartbeat override commands | 811 |

| Warning message kind (all logged) | Count |
| --- | --- |
| This simp argument is unused: | 185 |
| Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice | 91 |
| 'ring' tactic does nothing | 22 |
| this tactic is never executed | 22 |
| unused variable `y` | 8 |
| unused variable `x` | 4 |
| unused variable `i` | 4 |
| try 'simp' instead of 'simpa' | 3 |
| Try `simp at hh` instead of `simpa using hh` | 3 |
| unused variable `z` | 2 |

Only exact project-owned artifacts were invalidated. No `lake clean`, `lake update`, or upstream compilation is part of this procedure. Existing heartbeat overrides are a disclosed census, not a performance improvement. The dependency guard compares path, size, and mtime metadata rather than every artifact's content hash. Warning counts cover the entire log and can include cached upstream warnings replayed by Lake; they are not an own-source-only warning census.

## 5. Heavy tail

| Rounded logged duration tier | Measured files | Prior | Δ |
| --- | --- | --- | --- |
| ≥10 s | 150 | 557 | -407 |
| ≥20 s | 51 | 357 | -306 |
| ≥30 s | 28 | 261 | -233 |
| ≥40 s | 14 | 193 | -179 |

| Rank | Module | Logged elapsed s | Code lines | Elapsed ms/line | Prior s | Δ s |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | Cloning.TensorFlatProjectorStateFidelity | 77.00 | 92 | 836.96 | 127.00 | -50.00 |
| 2 | Cloning.PhysicalFlatConverseReduction | 75.00 | 85 | 882.35 | 94.00 | -19.00 |
| 3 | Cloning.TensorCartanChannelCovariance | 69.00 | 80 | 862.50 | 86.00 | -17.00 |
| 4 | Cloning.TensorCartanStateOperator | 61.00 | 131 | 465.65 | 83.00 | -22.00 |
| 5 | Cloning.PhysicalFlatPinchingInflation | 61.00 | 89 | 685.39 | 45.00 | +16.00 |
| 6 | Cloning.TensorGibbsCutoffState | 58.00 | 86 | 674.42 | 101.00 | -43.00 |
| 7 | Cloning.TensorFlatProjectorMixture | 57.00 | 140 | 407.14 | 73.00 | -16.00 |
| 8 | Cloning.TensorPositiveSpectrumCompression | 53.00 | 167 | 317.37 | 61.00 | -8.00 |
| 9 | Cloning.TensorRankOneCartan | 48.00 | 110 | 436.36 | 50.00 | -2.00 |
| 10 | Cloning.TensorLANEmbeddingCellError | 47.00 | 133 | 353.38 | 85.00 | -38.00 |
| 11 | Cloning.TensorCloningBlockFidelity | 46.00 | 92 | 500.00 | 34.00 | +12.00 |
| 12 | Cloning.TensorFlatProjectorState | 45.00 | 125 | 360.00 | 59.00 | -14.00 |
| 13 | Cloning.TensorFlatProjectorLaw | 41.00 | 82 | 500.00 | 27.00 | +14.00 |
| 14 | Cloning.TensorCloningGlobalCovarianceSector | 41.00 | 73 | 561.64 | 48.00 | -7.00 |
| 15 | Cloning.TensorSchurDecompositionIsometry | 39.00 | 118 | 330.51 | 111.00 | -72.00 |
| 16 | Cloning.TensorSchurHaarIntertwiner | 38.00 | 175 | 217.14 | 45.00 | -7.00 |
| 17 | Cloning.WeylGaussianTwirl | 38.00 | 88 | 431.82 | 47.00 | -9.00 |
| 18 | Cloning.PhysicalFlatPinching | 36.00 | 62 | 580.65 | 30.00 | +6.00 |
| 19 | Cloning.PCTRankPurificationBlockMatrices | 35.00 | 86 | 406.98 | 41.00 | -6.00 |
| 20 | Cloning.TensorGibbsState | 33.00 | 123 | 268.29 | 68.00 | -35.00 |
| 21 | Cloning.TensorCloningGlobalCovarianceAlgebra | 32.00 | 64 | 500.00 | 21.00 | +11.00 |
| 22 | Cloning.PhysicalFlatPinchingCovariance | 32.00 | 60 | 533.33 | 47.00 | -15.00 |
| 23 | Cloning.YoungCompatibility | 31.00 | 177 | 175.14 | 36.00 | -5.00 |
| 24 | Cloning.HybridClassicalAverageTrace | 30.00 | 172 | 174.42 | 93.00 | -63.00 |
| 25 | Cloning.TensorLANEmbeddingSchurState | 30.00 | 73 | 410.96 | 43.00 | -13.00 |
| 26 | Cloning.TensorLANEmbeddingFockProtocol | 30.00 | 109 | 275.23 | 44.00 | -14.00 |
| 27 | Cloning.PhysicalFlatConverseCommutant | 30.00 | 122 | 245.90 | 33.00 | -3.00 |
| 28 | Cloning.TensorFlatProjectorGibbsState | 30.00 | 55 | 545.45 | 57.00 | -27.00 |
| 29 | Cloning.TensorFlatProjectorTraceClass | 29.00 | 78 | 371.79 | 45.00 | -16.00 |
| 30 | Cloning.TensorCloningBlockTrimming | 29.00 | 118 | 245.76 | 34.00 | -5.00 |

Threshold classification uses rounded displayed durations; a boundary file may lie on either side before rounding.

## 6. Per-namespace work

Each module is assigned once, to its first declared namespace in the measured Git source; facades without one are grouped at root. A module may later open other namespaces. This grouping aggregates rounded elapsed job durations, not CPU.

| First declared namespace | Modules | Code lines | Logged elapsed s | Prior s | Δ s |
| --- | --- | --- | --- | --- | --- |
| Cloning.TensorLie | 187 | 16624 | 2,096.60 | 4,615.10 | -2,518.50 |
| Cloning.TensorCloning | 56 | 4472 | 604.30 | 830.20 | -225.90 |
| Cloning.Hybrid | 52 | 5590 | 449.90 | 1,898.40 | -1,448.50 |
| Cloning.InfiniteTraceClass | 54 | 5719 | 409.00 | 2,356.20 | -1,947.20 |
| Cloning.PhysicalFlatConverse | 20 | 1498 | 340.60 | 383.00 | -42.40 |
| Cloning.TensorLAN | 31 | 2294 | 338.70 | 563.30 | -224.60 |
| Cloning.MultimodeCoherent | 49 | 4492 | 281.20 | 1,458.60 | -1,177.40 |
| Cloning.YoungHyperplane | 24 | 2294 | 264.90 | 176.90 | +88.00 |
| Cloning.TensorLocalUnitary | 17 | 1750 | 160.40 | 385.20 | -224.80 |
| Cloning.YoungGeneral | 26 | 3115 | 148.40 | 149.00 | -0.60 |
| Cloning.PCTRankPurification | 25 | 1717 | 138.60 | 160.50 | -21.90 |
| Cloning.MatrixFidelity | 26 | 2152 | 120.10 | 829.20 | -709.10 |
| Cloning.ComplexCoherent | 18 | 1515 | 114.60 | 320.70 | -206.10 |
| Cloning.WeylGNS | 15 | 1079 | 110.70 | 134.30 | -23.60 |
| Cloning.PCTRankAdapted | 15 | 878 | 100.90 | 110.40 | -9.50 |
| Cloning.PhysicalCloningConverse | 9 | 734 | 78.80 | 158.00 | -79.20 |
| Cloning.PCTProjectorPurity | 15 | 1039 | 74.20 | 78.10 | -3.90 |
| Cloning.YoungFlat | 13 | 1037 | 73.40 | 119.70 | -46.30 |
| Cloning.GeneralSymmetricOccupation | 11 | 1284 | 61.80 | 734.00 | -672.20 |
| Cloning.InfiniteFidelity | 8 | 655 | 60.10 | 295.30 | -235.20 |
| Cloning.PCT | 7 | 891 | 58.20 | 460.00 | -401.80 |
| Cloning.PCTGlobal | 6 | 591 | 57.20 | 485.00 | -427.80 |
| Cloning.PCTRankGlobal | 7 | 518 | 55.60 | 66.50 | -10.90 |
| Cloning.WeylSqueezer | 10 | 424 | 51.40 | 66.30 | -14.90 |
| (root / facade) | 12 | 1481 | 51.00 | 57.30 | -6.30 |
| Cloning.WeylCharacter | 8 | 692 | 47.20 | 105.60 | -58.40 |
| Cloning.PCTCountMeasurement | 7 | 532 | 46.50 | 66.10 | -19.60 |
| Cloning.YoungCompatibility | 3 | 457 | 44.40 | 51.10 | -6.70 |
| Cloning.YoungMultinomial | 8 | 546 | 41.90 | 46.60 | -4.70 |
| Cloning.ValueExpansion | 9 | 732 | 41.40 | 44.30 | -2.90 |
| Cloning.GeneralCoherent | 7 | 632 | 41.40 | 336.00 | -294.60 |
| Cloning.SymmetricOccupation | 4 | 465 | 40.00 | 109.00 | -69.00 |
| Cloning.PCTHybridMixture | 4 | 322 | 39.60 | 393.00 | -353.40 |
| Cloning.PCTLocalChart | 7 | 632 | 39.50 | 240.40 | -200.90 |
| Cloning.CovariantAmplifier | 7 | 364 | 39.00 | 48.50 | -9.50 |
| Cloning.PCTPhysicalFidelity | 5 | 427 | 38.10 | 282.90 | -244.80 |
| Cloning.PBWSymmetricFrame | 4 | 383 | 36.40 | 37.90 | -1.50 |
| Cloning.YoungDimensionRatio | 3 | 560 | 36.10 | 22.60 | +13.50 |
| Cloning.YoungFlatCoupling | 8 | 653 | 35.20 | 47.30 | -12.10 |
| Cloning.BosonicAmplifier | 6 | 691 | 34.20 | 148.00 | -113.80 |
| Cloning.CountMultinomial | 6 | 420 | 34.10 | 45.30 | -11.20 |
| Cloning.MultimodeIdler | 6 | 615 | 33.30 | 47.70 | -14.40 |
| Cloning.WeylSqueezerProduct | 3 | 308 | 32.80 | 48.50 | -15.70 |
| Cloning.PCTCount | 5 | 468 | 30.10 | 40.20 | -10.10 |
| Cloning.PCTFlatGaussianCross | 6 | 488 | 29.70 | 36.50 | -6.80 |
| Cloning.PCTJointGaussianWhitening | 6 | 579 | 29.40 | 261.70 | -232.30 |
| Cloning.ValueComparison | 6 | 411 | 27.20 | 30.20 | -3.00 |
| Cloning.PCTPrescribed | 5 | 297 | 27.00 | 30.10 | -3.10 |
| Cloning.PCTPurificationChannel | 4 | 678 | 26.10 | 79.80 | -53.70 |
| Cloning.PBW | 5 | 646 | 25.70 | 127.00 | -101.30 |
| Cloning.PhysicalFlatGrassmann | 5 | 361 | 24.50 | 29.90 | -5.40 |
| Cloning.MultimodeAmplifier | 3 | 364 | 24.30 | 153.00 | -128.70 |
| Cloning.Hybrid.PositiveTraceClass | 5 | 289 | 23.80 | 32.90 | -9.10 |
| Cloning.PCTPurity | 5 | 432 | 23.60 | 28.10 | -4.50 |
| Cloning.PCTGaussianCovariance | 4 | 348 | 21.70 | 92.00 | -70.30 |
| Cloning.MatrixLiftedCPTP | 4 | 343 | 20.50 | 466.00 | -445.50 |
| Cloning.PhysicalFlatPCT | 4 | 163 | 20.20 | 27.40 | -7.20 |
| Cloning.SampleRatio | 4 | 139 | 20.10 | 20.70 | -0.60 |
| Cloning.MixedLANTransfer | 4 | 412 | 19.90 | 285.00 | -265.10 |
| Cloning | 3 | 320 | 19.50 | 55.00 | -35.50 |
| Cloning.PCTRankOne | 3 | 171 | 19.40 | 23.00 | -3.60 |
| Cloning.Thermal | 4 | 687 | 16.90 | 97.20 | -80.30 |
| Cloning.YoungTwoRow | 3 | 819 | 16.00 | 16.20 | -0.20 |
| Cloning.QubitDegeneracy | 1 | 225 | 16.00 | 18.00 | -2.00 |
| Cloning.PCTPhysicalState | 3 | 192 | 15.40 | 58.40 | -43.00 |
| Cloning.YoungRounding | 2 | 755 | 15.40 | 15.00 | +0.40 |
| Cloning.PhysicalAllStateMinimax | 3 | 142 | 15.00 | 16.10 | -1.10 |
| Cloning.ScalarTaylor | 3 | 131 | 13.30 | 14.30 | -1.00 |
| Cloning.PCTGaussianOutput | 2 | 202 | 12.90 | 133.00 | -120.10 |
| Cloning.Hybrid.PositiveField | 3 | 242 | 12.40 | 111.00 | -98.60 |
| Cloning.InfiniteTraceClass.HilbertSchmidt | 1 | 432 | 12.00 | 127.00 | -115.00 |
| Cloning.ThermalWitness | 2 | 458 | 11.70 | 30.00 | -18.30 |
| Cloning.InfiniteFidelityHilbertSum | 2 | 186 | 11.70 | 11.70 | +0.00 |
| Cloning.SpectralGap | 2 | 321 | 10.50 | 12.10 | -1.60 |
| Cloning.PCTUnitaryTransport | 2 | 197 | 10.30 | 265.00 | -254.70 |
| Cloning.Occupation | 3 | 223 | 10.10 | 76.00 | -65.90 |
| Cloning.InfinitePowersStormer | 1 | 135 | 9.30 | 41.00 | -31.70 |
| Cloning.InfiniteFidelityCorner | 2 | 211 | 9.20 | 13.50 | -4.30 |
| Cloning.PCTReducedGaussian | 2 | 177 | 9.10 | 69.00 | -59.90 |
| Cloning.GaussianAffinity | 2 | 338 | 9.00 | 63.00 | -54.00 |
| Cloning.FiniteKrausLift | 1 | 110 | 8.60 | 37.00 | -28.40 |
| Cloning.Channels | 2 | 119 | 8.50 | 25.20 | -16.70 |
| Cloning.InfiniteTraceClass.TraceClass | 1 | 197 | 8.40 | 99.00 | -90.60 |
| Cloning.BosonicStochasticOrder | 2 | 195 | 8.10 | 14.20 | -6.10 |
| Cloning.PurificationSupport | 1 | 141 | 7.80 | 30.00 | -22.20 |
| Cloning.InfiniteFiniteCorner | 1 | 122 | 7.30 | 33.00 | -25.70 |
| Cloning.Compression | 2 | 208 | 7.20 | 14.80 | -7.60 |
| Cloning.InfiniteTraceClass.Polar | 1 | 172 | 6.50 | 107.00 | -100.50 |
| Cloning.MatrixRegularization | 1 | 86 | 6.40 | 22.00 | -15.60 |
| Cloning.InfiniteTraceClassWeakLimit | 1 | 87 | 6.10 | 30.00 | -23.90 |
| Cloning.CoherentGaussianMixture | 1 | 163 | 6.10 | 9.00 | -2.90 |
| Cloning.MatrixCovariantBalance | 1 | 141 | 5.80 | 65.00 | -59.20 |
| Cloning.MultimodeLeastNoise | 1 | 128 | 5.70 | 64.00 | -58.30 |
| Cloning.InfiniteTraceClassAsymptoticBound | 1 | 49 | 5.60 | 13.00 | -7.40 |
| Cloning.Rounding | 1 | 231 | 5.60 | 49.00 | -43.40 |
| Cloning.TensorCartanLieBalance | 1 | 116 | 5.50 | 6.00 | -0.50 |
| Cloning.MultimodeCoherentGaussianMixture | 1 | 109 | 5.40 | 8.50 | -3.10 |
| Cloning.BlockFidelity | 1 | 121 | 5.20 | 48.00 | -42.80 |
| Cloning.PCTJointGaussianLaw | 1 | 180 | 5.20 | 40.00 | -34.80 |
| Cloning.Channels.MatrixChannel | 1 | 46 | 5.10 | 169.00 | -163.90 |
| Cloning.BoundedOperator | 1 | 85 | 5.00 | 10.00 | -5.00 |
| Cloning.ThermalIdlerFidelity | 1 | 110 | 5.00 | 30.00 | -25.00 |
| Cloning.MultimodeThermalIdlerFidelity | 1 | 114 | 4.90 | 25.00 | -20.10 |
| Cloning.MatrixLANTransfer | 1 | 90 | 4.80 | 150.00 | -145.20 |
| Cloning.PCTJointGaussianConvolution | 1 | 59 | 4.70 | 86.00 | -81.30 |
| Cloning.PositiveKernel | 1 | 133 | 4.70 | 7.40 | -2.70 |
| Cloning.MatrixTransitionAchievability | 1 | 95 | 4.70 | 151.00 | -146.30 |
| Cloning.MatrixLiftedTrimming | 1 | 112 | 4.60 | 126.00 | -121.40 |
| Cloning.MatrixLiftedChannel | 1 | 100 | 4.60 | 7.20 | -2.60 |
| Cloning.OrbitalSeededOptimum | 1 | 43 | 4.50 | 20.00 | -15.50 |
| Cloning.InfiniteOccupationStates | 1 | 119 | 4.40 | 39.00 | -34.60 |
| Cloning.InfiniteLANTransfer | 1 | 92 | 4.40 | 5.00 | -0.60 |
| Cloning.ComplexGaussianMoments | 1 | 81 | 4.30 | 6.20 | -1.90 |
| Cloning.LAN | 1 | 197 | 4.20 | 35.00 | -30.80 |
| Cloning.Hybrid.PhaseBody | 1 | 140 | 4.00 | 5.60 | -1.60 |
| Cloning.InfiniteBilinearWeakClosure | 1 | 67 | 4.00 | 34.00 | -30.00 |
| Cloning.Moments | 1 | 85 | 4.00 | 76.00 | -72.00 |
| Cloning.PCTJointGaussianReal | 1 | 102 | 4.00 | 144.00 | -140.00 |
| Cloning.Projector | 1 | 224 | 3.70 | 4.00 | -0.30 |
| Cloning.CountableScheffe | 1 | 186 | 3.70 | 77.00 | -73.30 |
| Cloning.InfiniteDiagonalFidelity | 1 | 104 | 3.70 | 5.60 | -1.90 |
| Cloning.CoherentCoefficients | 1 | 80 | 3.70 | 54.00 | -50.30 |
| Cloning.WernerAsymptotics | 1 | 207 | 3.60 | 38.00 | -34.40 |
| Cloning.BosonicNumberLaw | 1 | 264 | 3.50 | 46.00 | -42.50 |
| Cloning.PoissonApproximation | 1 | 73 | 3.40 | 87.00 | -83.60 |
| Cloning.CartanChannel | 1 | 74 | 3.00 | 7.40 | -4.40 |
| Cloning.ClassicalFidelity | 1 | 153 | 2.90 | 59.00 | -56.10 |
| Cloning.WernerNormalization | 1 | 91 | 2.80 | 42.00 | -39.20 |
| Cloning.UniversalLeastNoise | 1 | 150 | 2.00 | 5.80 | -3.80 |

## 7. Own-file profiles

Cumulative C++ timers are exclusive **elapsed** times summed across threads, not OS CPU. Trace self weights are elapsed intervals; inclusive trace rankings overlap. Detailed profiling adds instrumentation overhead; these are warm own-file attribution runs. Saved Lake setups bind mapped artifact paths; direct import families are content hashed and mapped transitive artifacts are guarded by path/size/mtime. Newly unmapped direct imports fall back to the recorded search path; their nonmapped transitive closure is not inventoried. The dominant-phase screen requires >5 s and >25% of the displayed phase sum. Declaration pointers identify declarations, not automatically an exact costly tactic.

| Module | Run | Exit | Process wall s | Phase sum s | Dominant screen | >100 ms events |
| --- | --- | --- | --- | --- | --- | --- |
| Cloning.WeylIdlerUniqueness | 1 | 0 | 8.94 | 11.63 | no phase above both thresholds | 4 |
| Cloning.PCTHybridMixtureFactor | 1 | 0 | 29.06 | 25.38 | elaboration, typeclass inference | 22 |
| Cloning.WernerPhysicalPullback | 1 | 0 | 29.71 | 12.50 | no phase above both thresholds | 4 |
| Cloning.PCTGlobalPhysical | 1 | 0 | 57.64 | 18.47 | interpretation | 11 |
| Cloning.PCTUnitaryTransportChannels | 1 | 0 | 6.42 | 5.14 | no phase above both thresholds | 3 |
| Cloning.InfiniteTraceClass | 1 | 0 | 16.82 | 29.95 | typeclass inference | 32 |
| Cloning.Thermal | 1 | 0 | 5.07 | 9.11 | no phase above both thresholds | 6 |
| Cloning.AmplifierWeylThermal | 1 | 0 | 7.23 | 6.20 | no phase above both thresholds | 7 |
| Cloning.PCTClosedForm | 1 | 0 | 5.03 | 4.07 | no phase above both thresholds | 2 |
| Cloning.CloningValueComparisonMonotone | 1 | 0 | 6.76 | 5.54 | no phase above both thresholds | 3 |
| Cloning.TensorFlatProjectorStateFidelity | 1 | 0 | 98.91 | 68.67 | tactic execution | 25 |
| Cloning.PhysicalFlatConverseReduction | 1 | 0 | 59.19 | 60.20 | tactic execution | 11 |
| Cloning.TensorCartanChannelCovariance | 1 | 0 | 111.90 | 63.70 | interpretation, typeclass inference | 113 |
| Cloning.TensorCartanStateOperator | 1 | 0 | 59.52 | 39.45 | tactic execution, typeclass inference | 68 |
| Cloning.PhysicalFlatPinchingInflation | 1 | 0 | 30.18 | 43.96 | tactic execution, typeclass inference | 20 |

### Cloning.WeylIdlerUniqueness — repetition 1

Recorded profile commit: `3eb587e0f00748c3a9b63f9eeedc1646e4cb77be`; source SHA-256: `e1413287599caab0c36d5cf8625f327b319f75c097fe6cc33d4351f22cff5dc7`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | 3eb587e0f00748c3a9b63f9eeedc1646e4cb77be |
| Source matches recorded profile commit | True |
| Source matches benchmark commit | True |
| Preserved profile source | Cloning.WeylIdlerUniqueness-1.source.lean.txt |
| Configuration matches benchmark | True |
| Source/config/artifact/setup inputs stable | True |
| Measurement valid | True |
| Profile mode | firefox |
| Import context | Cloning.WeylIdlerUniqueness-1.import-context.json |

Controlled profile environment: `{'LAKE_ARTIFACT_CACHE': 'false', 'LEAN_NUM_THREADS': '2'}`. The raw metadata records selected effective environment and import paths.

| Configuration input | SHA-256 |
| --- | --- |
| formalization/lake-manifest.json | e4630915680b82b58c6a005e1ba1e515e865e5541c7e665d4a2d57f783eeadb4 |
| formalization/lakefile.toml | ddeb0d2c8217676fc393afd24c13629993c580f35f9d8ad15240c6a167b020c1 |
| formalization/lean-toolchain | dc6d65016fad3123d44bf17b5bf0598286284ab16ba75d5c17eb22ed11f47361 |

| Lean environment statistic | Value |
| --- | --- |
| Environment extensions | 302 |
| Imported constant-map buckets | 2097152 |
| Imported constants | 436230 |
| Imported compacted-region bytes (not RSS) | 4014560624 |
| Imported compacted regions (Lean labels these modules) | 20192 |
| Memory-mapped compacted regions | 20106 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| typeclass inference | 4.840 |
| import | 3.530 |
| tactic execution | 1.380 |
| interpretation | 0.989 |
| type checking | 0.386 |
| simp | 0.304 |
| elaboration | 0.123 |
| initialization | 0.019 |
| process pre-definitions | 0.013 |
| linting | 0.011 |
| share common exprs | 0.011 |
| instantiate metavars | 0.006 |
| parsing | 0.005 |
| congr simp thm | 0.003 |
| dsimp | 0.002 |
| fix level params | 0.001 |
| let-to-have transformation | 0.001 |
| compilation (LCNF base) | 0.000 |
| compilation (LCNF mono) | 0.000 |
| compilation (LCNF impure) | 0.000 |
| attribute application | 0.000 |
| compilation (IR) | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| import took 3.53s | 3.530 | 1 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 216ms | 0.216 | 3 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 163ms | 0.163 | 4 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 116ms | 0.116 | 5 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 5.016 | 6.236 | unattributed |
| Meta.check: ✅️ DFunLike.hasCoeToFun | 0.465 | 0.517 | unattributed |
| Elab.lint: running linters | 0.173 | 0.173 | unattributed |
| Meta.isDefEq: ✅️ { toNorm := ContinuousLinearMap.hasOpNorm, toAddCommGroup := ContinuousLinearMap.addCommGroup,   toPseudoMetricSpace := ContinuousLinearMap.toPseudoMetricSpace,   dist_eq :=     ⋯ } =?= { toNorm := NonUnitalNormedRing.toNonUnitalSeminormedRing.toNorm,   toAddCommGroup := NonUnitalNo | 0.127 | 0.349 | unattributed |
| Elab.step: Lean.Parser.Term.app: expected type: Type, term TraceClass (Fock d) | 0.116 | 0.128 | unattributed |
| Meta.synthInstance: ✅️ SeminormedAddCommGroup ↥(Cloning.MultimodeCoherent.Fock d) | 0.109 | 0.476 | unattributed |
| Meta.isDefEq.delta: ✅️ UniformConvergenceCLM.instTopologicalSpace (RingHom.id ℂ) ℂ   {S \|     Bornology.IsVonNBounded ℂ       S} =?= UniformConvergenceCLM.instTopologicalSpace (RingHom.id ℂ) ℂ {S \| Bornology.IsVonNBounded ℂ S} | 0.102 | 0.102 | unattributed |
| Meta.isDefEq: ✅️ (↥(Cloning.MultimodeCoherent.Fock d) →L[ℂ] ↥(Cloning.MultimodeCoherent.Fock d)) →L[ℂ]   ℂ =?= (↥(Cloning.MultimodeCoherent.Fock d) →L[ℂ] ↥(Cloning.MultimodeCoherent.Fock d)) →L[ℂ] ℂ | 0.091 | 0.105 | unattributed |
| Meta.synthInstance: ✅️ CoeFun ((↥(Cloning.MultimodeCoherent.Fock d) →L[ℂ] ↥(Cloning.MultimodeCoherent.Fock d)) →L[ℂ] ℂ) fun x =>   (↥(Cloning.MultimodeCoherent.Fock d) →L[ℂ] ↥(Cloning.MultimodeCoherent.Fock d)) → ℂ | 0.090 | 0.162 | unattributed |
| Elab.step: Lean.Parser.Term.app: expected type: <not-available>, term tracePairing T (displacement a) | 0.088 | 0.174 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 5.016 | 6.236 | unattributed |
| Elab.async: elaborating proof of Cloning.MultimodeCoherent.norm_tracePairing_displacement_le | 0.002 | 1.477 | unattributed |
| Elab.definition.value: Cloning.MultimodeCoherent.norm_tracePairing_displacement_le | 0.001 | 1.475 | Cloning.MultimodeCoherent.norm_tracePairing_displacement_le at formalization/Cloning/WeylIdlerUniqueness.lean:19 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   have hT : ‖tracePairing T‖ ≤ ‖T‖ :=     ((tracePairingCLM (H := Fock d)).le_opNorm T).trans       (by simpa using mul_le_mul_of_nonneg_right (norm_tracePairingCLM_le (H := Fock d)) (norm_nonneg T))   calc     _ ≤ ‖tracePairing T‖ * ‖displacement a‖ := (trac | 0.000 | 1.475 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   have hT : ‖tracePairing T‖ ≤ ‖T‖ :=     ((tracePairingCLM (H := Fock d)).le_opNorm T).trans       (by simpa using mul_le_mul_of_nonneg_right (norm_tracePairingCLM_le (H := Fock d)) (norm_nonneg T))   calc     _ ≤ ‖tracePairing T‖ * ‖displacement a‖ | 0.000 | 1.475 | unattributed |
| Elab.async: elaborating proof of Cloning.MultimodeCoherent.integral_weighted_characteristic | 0.005 | 1.302 | unattributed |
| Elab.definition.value: Cloning.MultimodeCoherent.integral_weighted_characteristic | 0.003 | 1.298 | Cloning.MultimodeCoherent.integral_weighted_characteristic at formalization/Cloning/WeylIdlerUniqueness.lean:82 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   have heq :     gaussianCharacteristicIntegral (d := d) =       (tracePairingCLM (H := Fock d)).flip (InnerProductSpace.rankOne ℂ (coherentVector 0) (coherentVector 0)) :=     by     apply traceClass_functional_ext     intro x     rw [show vectorProjector x  | 0.000 | 1.295 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   have heq :     gaussianCharacteristicIntegral (d := d) =       (tracePairingCLM (H := Fock d)).flip (InnerProductSpace.rankOne ℂ (coherentVector 0) (coherentVector 0)) :=     by     apply traceClass_functional_ext     intro x     rw [show vectorPro | 0.000 | 1.295 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticHave__: have heq :   gaussianCharacteristicIntegral (d := d) =     (tracePairingCLM (H := Fock d)).flip (InnerProductSpace.rankOne ℂ (coherentVector 0) (coherentVector 0)) :=   by   apply traceClass_functional_ext   intro x   rw [show vectorProjector x = rankOneOp | 0.000 | 1.252 | unattributed |

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.WeylIdlerUniqueness-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.WeylIdlerUniqueness-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.WeylIdlerUniqueness-1.setup.json Cloning/WeylIdlerUniqueness.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.PCTHybridMixtureFactor — repetition 1

Recorded profile commit: `3eb587e0f00748c3a9b63f9eeedc1646e4cb77be`; source SHA-256: `dc112ae5e22432d2e6502a06efd023939d9e5b40b13b63a044f06b480272ef54`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | 3eb587e0f00748c3a9b63f9eeedc1646e4cb77be |
| Source matches recorded profile commit | True |
| Source matches benchmark commit | True |
| Preserved profile source | Cloning.PCTHybridMixtureFactor-1.source.lean.txt |
| Configuration matches benchmark | True |
| Source/config/artifact/setup inputs stable | True |
| Measurement valid | True |
| Profile mode | firefox |
| Import context | Cloning.PCTHybridMixtureFactor-1.import-context.json |

Controlled profile environment: `{'LAKE_ARTIFACT_CACHE': 'false', 'LEAN_NUM_THREADS': '2'}`. The raw metadata records selected effective environment and import paths.

| Configuration input | SHA-256 |
| --- | --- |
| formalization/lake-manifest.json | e4630915680b82b58c6a005e1ba1e515e865e5541c7e665d4a2d57f783eeadb4 |
| formalization/lakefile.toml | ddeb0d2c8217676fc393afd24c13629993c580f35f9d8ad15240c6a167b020c1 |
| formalization/lean-toolchain | dc6d65016fad3123d44bf17b5bf0598286284ab16ba75d5c17eb22ed11f47361 |

| Lean environment statistic | Value |
| --- | --- |
| Environment extensions | 302 |
| Imported constant-map buckets | 2097152 |
| Imported constants | 438517 |
| Imported compacted-region bytes (not RSS) | 4057451904 |
| Imported compacted regions (Lean labels these modules) | 20375 |
| Memory-mapped compacted regions | 20286 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| elaboration | 11.200 |
| typeclass inference | 7.050 |
| import | 4.080 |
| interpretation | 1.830 |
| tactic execution | 1.020 |
| type checking | 0.076 |
| let-to-have transformation | 0.040 |
| initialization | 0.019 |
| simp | 0.014 |
| linting | 0.010 |
| ring | 0.007 |
| congr simp thm | 0.006 |
| dsimp | 0.005 |
| share common exprs | 0.005 |
| instantiate metavars | 0.004 |
| process pre-definitions | 0.003 |
| parsing | 0.003 |
| compilation (LCNF base) | 0.001 |
| fix level params | 0.001 |
| compilation (LCNF mono) | 0.001 |
| norm_num | 0.000 |
| compilation (LCNF impure) | 0.000 |
| compilation (IR) | 0.000 |
| attribute application | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| import took 4.08s | 4.080 | 1 |
| elaboration took 3.95s | 3.950 | 19 |
| elaboration took 3.61s | 3.610 | 10 |
| elaboration took 3.58s | 3.580 | 5 |
| typeclass inference of AddCommMonoid took 423ms | 0.423 | 12 |
| typeclass inference of TopologicalSpace took 422ms | 0.422 | 11 |
| typeclass inference of Module took 349ms | 0.349 | 13 |
| tactic execution of Lean.Parser.Tactic.refine took 325ms | 0.325 | 14 |
| typeclass inference of SecondCountableTopologyEither took 297ms | 0.297 | 15 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 235ms | 0.235 | 22 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 5.874 | 20.261 | unattributed |
| Meta.isDefEq: ✅️ { toAdd := ContinuousLinearMap.add, add_assoc := ⋯, toZero := ContinuousLinearMap.zero, zero_add := ⋯, add_zero := ⋯,   nsmul := fun x1 x2 => x1 • x2, nsmul_zero := ⋯,   nsmul_succ :=     ⋯ } =?= { toAdd := ContinuousLinearMap.add, add_assoc := ⋯, toZero := ContinuousLinearMap.zero, | 4.461 | 4.461 | unattributed |
| Meta.isDefEq: ❌️ (MeasureTheory.ae ?m.6).sets.Mem   {x \| (fun x => f x = g x) x} =?= (MeasureTheory.ae MeasureTheory.volume).sets.Mem {x \| (fun x => f x = g x) x} | 2.550 | 2.581 | unattributed |
| Meta.isDefEq: ❌️ (MeasureTheory.ae ?m.54).sets.Mem   {x \| (fun x => f x = g x) x} =?= (MeasureTheory.ae MeasureTheory.volume).sets.Mem {x \| (fun x => f x = g x) x} | 1.317 | 1.413 | unattributed |
| Meta.isDefEq: ❌️ {x \| (fun x => f x = g x) x} ∈   (MeasureTheory.ae ?m.6).sets =?= {x \| (fun x => f x = g x) x} ∈ (MeasureTheory.ae MeasureTheory.volume).sets | 1.304 | 3.918 | unattributed |
| Meta.isDefEq: ❌️ ∀ᵐ (x : Fin k → ℝ) ∂?m.6, f x = g x =?= ∀ᵐ (x : Fin k → ℝ), f x = g x | 0.870 | 5.654 | unattributed |
| Meta.isDefEq: ❌️ f =ᵐ[?m.6] g =?= f =ᵐ[MeasureTheory.volume] g | 0.869 | 6.523 | unattributed |
| Meta.isDefEq: ❌️ {x \| (fun x => f x = g x) x} ∈   MeasureTheory.ae ?m.6 =?= {x \| (fun x => f x = g x) x} ∈ MeasureTheory.ae MeasureTheory.volume | 0.864 | 4.784 | unattributed |
| Meta.isDefEq: ❌️ {x \| (fun x => f x = g x) x} ∈   (MeasureTheory.ae ?m.54).sets =?= {x \| (fun x => f x = g x) x} ∈ (MeasureTheory.ae MeasureTheory.volume).sets | 0.617 | 2.142 | unattributed |
| Meta.isDefEq: ❌️ ∀ᵐ (x : Fin k → ℝ) ∂?m.54, f x = g x =?= ∀ᵐ (x : Fin k → ℝ), f x = g x | 0.475 | 3.091 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 5.874 | 20.261 | unattributed |
| Meta.isDefEq: ❌️ { f //   MeasureTheory.AEStronglyMeasurable f ?m.6 } =?= { f // MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume } | 0.002 | 6.539 | unattributed |
| Meta.isDefEq: ❌️ fun f =>   MeasureTheory.AEStronglyMeasurable f ?m.6 =?= fun f => MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume | 0.002 | 6.538 | unattributed |
| Meta.isDefEq: ❌️ MeasureTheory.AEStronglyMeasurable f ?m.6 =?= MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume | 0.002 | 6.535 | unattributed |
| Meta.isDefEq: ❌️ ∃ g,   MeasureTheory.StronglyMeasurable g ∧     f =ᵐ[?m.6] g =?= ∃ g, MeasureTheory.StronglyMeasurable g ∧ f =ᵐ[MeasureTheory.volume] g | 0.002 | 6.533 | unattributed |
| Meta.isDefEq: ❌️ fun g =>   MeasureTheory.StronglyMeasurable g ∧     f =ᵐ[?m.6] g =?= fun g => MeasureTheory.StronglyMeasurable g ∧ f =ᵐ[MeasureTheory.volume] g | 0.001 | 6.531 | unattributed |
| Meta.isDefEq: ❌️ MeasureTheory.StronglyMeasurable g ∧   f =ᵐ[?m.6] g =?= MeasureTheory.StronglyMeasurable g ∧ f =ᵐ[MeasureTheory.volume] g | 0.007 | 6.530 | unattributed |
| Meta.isDefEq: ❌️ f =ᵐ[?m.6] g =?= f =ᵐ[MeasureTheory.volume] g | 0.869 | 6.523 | unattributed |
| Meta.isDefEq: ❌️ (Fin k → ℝ) →ₘ[?m.6]   Cloning.InfiniteTraceClass.TraceClass     ↥(Cloning.MultimodeCoherent.Fock         d) =?= (Fin k → ℝ) →ₘ[MeasureTheory.volume]   Cloning.InfiniteTraceClass.TraceClass ↥(Cloning.MultimodeCoherent.Fock d) | 0.001 | 5.829 | unattributed |
| Meta.isDefEq: ❌️ Quotient   (MeasureTheory.Measure.aeEqSetoid (Cloning.InfiniteTraceClass.TraceClass ↥(Cloning.MultimodeCoherent.Fock d))     ?m.6) =?= Quotient   (MeasureTheory.Measure.aeEqSetoid (Cloning.InfiniteTraceClass.TraceClass ↥(Cloning.MultimodeCoherent.Fock d))     MeasureTheory.volume) | 0.001 | 5.827 | unattributed |

Unattributed elaboration events above threshold: 3; the detailed trace rankings supply attribution where their labels identify declarations.

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.PCTHybridMixtureFactor-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.PCTHybridMixtureFactor-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.PCTHybridMixtureFactor-1.setup.json Cloning/PCTHybridMixtureFactor.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.WernerPhysicalPullback — repetition 1

Recorded profile commit: `3eb587e0f00748c3a9b63f9eeedc1646e4cb77be`; source SHA-256: `328dd36bde83e302e13d99f6168651cb90f5a10b39811339590e645822c5b30b`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | 3eb587e0f00748c3a9b63f9eeedc1646e4cb77be |
| Source matches recorded profile commit | True |
| Source matches benchmark commit | True |
| Preserved profile source | Cloning.WernerPhysicalPullback-1.source.lean.txt |
| Configuration matches benchmark | True |
| Source/config/artifact/setup inputs stable | True |
| Measurement valid | True |
| Profile mode | firefox |
| Import context | Cloning.WernerPhysicalPullback-1.import-context.json |

Controlled profile environment: `{'LAKE_ARTIFACT_CACHE': 'false', 'LEAN_NUM_THREADS': '2'}`. The raw metadata records selected effective environment and import paths.

| Configuration input | SHA-256 |
| --- | --- |
| formalization/lake-manifest.json | e4630915680b82b58c6a005e1ba1e515e865e5541c7e665d4a2d57f783eeadb4 |
| formalization/lakefile.toml | ddeb0d2c8217676fc393afd24c13629993c580f35f9d8ad15240c6a167b020c1 |
| formalization/lean-toolchain | dc6d65016fad3123d44bf17b5bf0598286284ab16ba75d5c17eb22ed11f47361 |

| Lean environment statistic | Value |
| --- | --- |
| Environment extensions | 302 |
| Imported constant-map buckets | 2097152 |
| Imported constants | 432839 |
| Imported compacted-region bytes (not RSS) | 3966409928 |
| Imported compacted regions (Lean labels these modules) | 19946 |
| Memory-mapped compacted regions | 19861 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| interpretation | 3.900 |
| typeclass inference | 2.620 |
| import | 2.590 |
| tactic execution | 2.240 |
| elaboration | 0.678 |
| simp | 0.201 |
| type checking | 0.195 |
| initialization | 0.019 |
| process pre-definitions | 0.015 |
| linting | 0.014 |
| parsing | 0.008 |
| share common exprs | 0.006 |
| norm_num | 0.005 |
| congr simp thm | 0.003 |
| compilation (LCNF base) | 0.002 |
| compilation (LCNF mono) | 0.002 |
| instantiate metavars | 0.002 |
| fix level params | 0.001 |
| let-to-have transformation | 0.001 |
| compilation (LCNF impure) | 0.001 |
| attribute application | 0.001 |
| compilation (IR) | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| import took 2.59s | 2.590 | 1 |
| tactic execution of Lean.Parser.Tactic.change took 1.91s | 1.910 | 2 |
| elaboration took 561ms | 0.561 | 4 |
| typeclass inference of CoeFun took 106ms | 0.106 | 3 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 4.285 | 5.697 | unattributed |
| Meta.isDefEq: ✅️ {   re :=     (↑(↑(ContinuousLinearMap.adjoint (Cloning.GeneralSymmetricOccupation.isometry L (s + 1)).toContinuousLinearMap) x)             i).re *         ((starRingEnd ℂ) (↑i✝³ i)).re -       (↑(↑(ContinuousLinearMap.adjoint (Cloning.GeneralSymmetricOccupation.isometry L (s + 1)) | 0.915 | 0.998 | unattributed |
| Meta.isDefEq: ✅️ { toAdd := ContinuousLinearMap.add, add_assoc := ⋯, toZero := ContinuousLinearMap.zero, zero_add := ⋯, add_zero := ⋯,   nsmul := fun x1 x2 => x1 • x2, nsmul_zero := ⋯,   nsmul_succ :=     ⋯ } =?= { toAdd := ContinuousLinearMap.add, add_assoc := ⋯, toZero := ContinuousLinearMap.zero, | 0.374 | 0.462 | unattributed |
| Meta.isDefEq: ✅️ b.repr.toLinearEquiv.2 (lp.single 2 i✝ 1) =?= b.repr.toLinearEquiv.2 (lp.single 2 i✝ 1) | 0.335 | 0.335 | unattributed |
| Meta.synthInstance: ❌️ Nonempty (Fin s) | 0.305 | 0.305 | unattributed |
| Meta.isDefEq: ✅️ ⋯.choose.repr.toLinearEquiv.2 (lp.single 2 i✝ 1) =?= ⋯.choose.repr.toLinearEquiv.2 (lp.single 2 i✝ 1) | 0.163 | 0.527 | unattributed |
| Elab.lint: running linters | 0.158 | 0.158 | unattributed |
| Meta.synthInstance: ❌️ Nonempty (Fin L) | 0.138 | 0.138 | unattributed |
| Meta.isDefEq: ✅️ (↑(↑(ContinuousLinearMap.adjoint             (ContinuousLinearMap.adjoint (Cloning.GeneralSymmetricOccupation.isometry L (s + 1)).toContinuousLinearMap))         i✝²)     i).1 =?= (↑(↑(ContinuousLinearMap.adjoint             (ContinuousLinearMap.adjoint (Cloning.GeneralSymmetricOccu | 0.124 | 1.551 | unattributed |
| Meta.isDefEq: ✅️ (↑(ContinuousLinearMap.adjoint         (ContinuousLinearMap.adjoint (Cloning.GeneralSymmetricOccupation.isometry L (s + 1)).toContinuousLinearMap))     i✝²).1 =?= (↑(ContinuousLinearMap.adjoint         (ContinuousLinearMap.adjoint (Cloning.GeneralSymmetricOccupation.isometry L (s +  | 0.115 | 1.314 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 4.285 | 5.697 | unattributed |
| Elab.async: elaborating proof of Cloning.GeneralSymmetricOccupation.occupationRecovery_column | 0.001 | 2.032 | unattributed |
| Elab.definition.value: Cloning.GeneralSymmetricOccupation.occupationRecovery_column | 0.005 | 2.031 | Cloning.GeneralSymmetricOccupation.occupationRecovery_column at formalization/Cloning/WernerPhysicalPullback.lean:103 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   rw [← isometry_single]   change     (QuantumChannel.ofIsometry (occupationPad L s)).toLinearMap         ((QuantumChannel.isometricRecovery (isometry L (s + 1)) (vacuumRegister L s)).toLinearMap           (vectorProjector (isometry L (s + 1) (lp.single 2 q 1 | 0.000 | 2.026 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   rw [← isometry_single]   change     (QuantumChannel.ofIsometry (occupationPad L s)).toLinearMap         ((QuantumChannel.isometricRecovery (isometry L (s + 1)) (vacuumRegister L s)).toLinearMap           (vectorProjector (isometry L (s + 1) (lp.sin | 0.000 | 2.026 | unattributed |
| Elab.step: Lean.Parser.Tactic.change: change   (QuantumChannel.ofIsometry (occupationPad L s)).toLinearMap       ((QuantumChannel.isometricRecovery (isometry L (s + 1)) (vacuumRegister L s)).toLinearMap         (vectorProjector (isometry L (s + 1) (lp.single 2 q 1)))) =     _ | 0.001 | 1.974 | unattributed |
| Meta.isDefEq: ✅️ (Cloning.InfiniteTraceClass.QuantumChannel.ofIsometry       (Cloning.GeneralSymmetricOccupation.occupationPad L s)).toLinearMap   ((Cloning.InfiniteTraceClass.QuantumChannel.isometricRecovery (Cloning.GeneralSymmetricOccupation.isometry L (s + 1))         (Cloning.GeneralSymmetricOc | 0.000 | 1.891 | unattributed |
| Meta.isDefEq: ✅️ LinearMap.instFunLike.1   (Cloning.InfiniteTraceClass.QuantumChannel.ofIsometry       (Cloning.GeneralSymmetricOccupation.occupationPad L s)).toLinearMap   ((Cloning.InfiniteTraceClass.QuantumChannel.isometricRecovery (Cloning.GeneralSymmetricOccupation.isometry L (s + 1))         ( | 0.000 | 1.891 | unattributed |
| Meta.isDefEq: ✅️ (Cloning.InfiniteTraceClass.QuantumChannel.ofIsometry         (Cloning.GeneralSymmetricOccupation.occupationPad L s)).toLinearMap.toFun   ((Cloning.InfiniteTraceClass.QuantumChannel.isometricRecovery (Cloning.GeneralSymmetricOccupation.isometry L (s + 1))         (Cloning.GeneralSym | 0.000 | 1.891 | unattributed |
| Meta.isDefEq: ✅️ (Cloning.InfiniteTraceClass.QuantumChannel.ofIsometry           (Cloning.GeneralSymmetricOccupation.occupationPad L s)).toLinearMap.toAddHom.1   ((Cloning.InfiniteTraceClass.QuantumChannel.isometricRecovery (Cloning.GeneralSymmetricOccupation.isometry L (s + 1))         (Cloning.Gen | 0.001 | 1.890 | unattributed |

Unattributed elaboration events above threshold: 1; the detailed trace rankings supply attribution where their labels identify declarations.

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.WernerPhysicalPullback-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.WernerPhysicalPullback-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.WernerPhysicalPullback-1.setup.json Cloning/WernerPhysicalPullback.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.PCTGlobalPhysical — repetition 1

Recorded profile commit: `3eb587e0f00748c3a9b63f9eeedc1646e4cb77be`; source SHA-256: `fb0231237298a06a32147e115e6e8f29f0ad572e8a0f4698db82b86654f553c6`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | 3eb587e0f00748c3a9b63f9eeedc1646e4cb77be |
| Source matches recorded profile commit | True |
| Source matches benchmark commit | True |
| Preserved profile source | Cloning.PCTGlobalPhysical-1.source.lean.txt |
| Configuration matches benchmark | True |
| Source/config/artifact/setup inputs stable | True |
| Measurement valid | True |
| Profile mode | firefox |
| Import context | Cloning.PCTGlobalPhysical-1.import-context.json |

Controlled profile environment: `{'LAKE_ARTIFACT_CACHE': 'false', 'LEAN_NUM_THREADS': '2'}`. The raw metadata records selected effective environment and import paths.

| Configuration input | SHA-256 |
| --- | --- |
| formalization/lake-manifest.json | e4630915680b82b58c6a005e1ba1e515e865e5541c7e665d4a2d57f783eeadb4 |
| formalization/lakefile.toml | ddeb0d2c8217676fc393afd24c13629993c580f35f9d8ad15240c6a167b020c1 |
| formalization/lean-toolchain | dc6d65016fad3123d44bf17b5bf0598286284ab16ba75d5c17eb22ed11f47361 |

| Lean environment statistic | Value |
| --- | --- |
| Environment extensions | 302 |
| Imported constant-map buckets | 2097152 |
| Imported constants | 436428 |
| Imported compacted-region bytes (not RSS) | 4021491520 |
| Imported compacted regions (Lean labels these modules) | 20199 |
| Memory-mapped compacted regions | 20113 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| interpretation | 6.960 |
| elaboration | 3.920 |
| typeclass inference | 3.280 |
| import | 3.240 |
| tactic execution | 0.846 |
| type checking | 0.158 |
| initialization | 0.019 |
| let-to-have transformation | 0.009 |
| simp | 0.009 |
| process pre-definitions | 0.008 |
| linting | 0.007 |
| share common exprs | 0.007 |
| parsing | 0.005 |
| congr simp thm | 0.002 |
| fix level params | 0.002 |
| instantiate metavars | 0.001 |
| attribute application | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| elaboration took 3.39s | 3.390 | 11 |
| import took 3.24s | 3.240 | 1 |
| elaboration took 304ms | 0.304 | 2 |
| tactic execution of Lean.Parser.Tactic.change took 296ms | 0.296 | 8 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 230ms | 0.230 | 9 |
| typeclass inference of CoeFun took 221ms | 0.221 | 6 |
| typeclass inference of CoeFun took 211ms | 0.211 | 5 |
| typeclass inference of CoeFun took 205ms | 0.205 | 4 |
| typeclass inference of CoeFun took 195ms | 0.195 | 3 |
| typeclass inference of CoeFun took 195ms | 0.195 | 7 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 6.711 | 9.186 | unattributed |
| Meta.isDefEq.delta: ✅️ SetLike.instMembership =?= SetLike.instMembership | 1.156 | 1.330 | unattributed |
| Meta.isDefEq: ✅️ {   re :=     (LinearMap.id (↑((Cloning.GeneralSymmetricOccupation.isometry n (s + 1)).toLinearMap x) i✝)).re *         (↑(Cloning.PCT.tensorVector fun i => (Cloning.PCTGlobal.fixedFrame hcard) (i✝ i)) i).re -       (LinearMap.id (↑((Cloning.GeneralSymmetricOccupation.isometry n (s  | 0.702 | 0.702 | unattributed |
| Meta.isDefEq: ✅️ {   re :=     (LinearMap.id (↑((Cloning.GeneralSymmetricOccupation.isometry n (s + 1)).toLinearMap x) i✝)).re *         (↑(Cloning.PCT.tensorVector fun i =>                 (Cloning.PCTGlobal.coordinateFrame (Fintype.equivFinOfCardEq hcard).symm) (i✝ i))             i).re -       (L | 0.450 | 0.450 | unattributed |
| Meta.isDefEq: ✅️ ((fun i =>         ((fun i =>               ((fun i =>                     ((fun i => ((fun i => ((fun i => RCLike.innerProductSpace) i).toNormedSpace) i).toModule)                         i).toDistribMulAction)                   i).toMulAction)             i).toSMul)       i).1   ( | 0.208 | 0.759 | unattributed |
| Meta.check: ✅️ DFunLike.hasCoeToFun | 0.160 | 1.544 | unattributed |
| Elab.lint: running linters | 0.137 | 0.137 | unattributed |
| Elab.step: Lean.Parser.Tactic.rewriteSeq: rewrite [purificationChannel_apply, recoveredMatrix_lift] | 0.126 | 0.232 | unattributed |
| Meta.isDefEq: ✅️ ((fun i =>         ((fun i =>               ((fun i =>                     ((fun i => ((fun i => ((fun i => RCLike.innerProductSpace) i).toNormedSpace) i).toModule)                         i).toDistribMulAction)                   i).toMulAction)             i).toSMul)       i).1   ( | 0.099 | 0.823 | unattributed |
| Meta.isDefEq.delta: ✅️ Submodule.setLike =?= Submodule.setLike | 0.082 | 0.082 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 6.711 | 9.186 | unattributed |
| Elab.async: elaborating proof of Cloning.PCTGlobal.channel_matrix_apply | 0.008 | 3.403 | unattributed |
| Elab.definition.value: Cloning.PCTGlobal.channel_matrix_apply | 0.002 | 3.395 | Cloning.PCTGlobal.channel_matrix_apply at formalization/Cloning/PCTGlobalPhysical.lean:83 |
| Meta.isDefEq: ✅️ NormedAddCommGroup.toENormedAddCommMonoid.toAddCommMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddCommMonoid | 0.002 | 2.118 | unattributed |
| Meta.isDefEq: ✅️ { toAddMonoid := NormedAddCommGroup.toENormedAddCommMonoid.toAddMonoid,   add_comm :=     ⋯ } =?= { toAddMonoid := Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddMonoid, add_comm := ⋯ } | 0.009 | 2.115 | unattributed |
| Meta.isDefEq: ✅️ NormedAddCommGroup.toENormedAddCommMonoid.toAddMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddMonoid | 0.003 | 2.106 | unattributed |
| Meta.isDefEq: ✅️ NormedAddCommGroup.toNormedAddGroup.toAddMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddMonoid | 0.002 | 2.103 | unattributed |
| Meta.isDefEq.delta: ✅️ NormedAddCommGroup.toNormedAddGroup.toAddMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddMonoid | 0.010 | 2.101 | unattributed |
| Meta.isDefEq: ✅️ NormedAddCommGroup.toNormedAddGroup.toSubNegMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toSubNegMonoid | 0.002 | 2.091 | unattributed |
| Meta.isDefEq.delta: ✅️ NormedAddCommGroup.toNormedAddGroup.toSubNegMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toSubNegMonoid | 0.003 | 2.089 | unattributed |

Unattributed elaboration events above threshold: 2; the detailed trace rankings supply attribution where their labels identify declarations.

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.PCTGlobalPhysical-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.PCTGlobalPhysical-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.PCTGlobalPhysical-1.setup.json Cloning/PCTGlobalPhysical.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.PCTUnitaryTransportChannels — repetition 1

Recorded profile commit: `3eb587e0f00748c3a9b63f9eeedc1646e4cb77be`; source SHA-256: `9eff2831f65aaf27d9d81958f1a14501a9126e4a389de0db9e76bf6a0990e57a`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | 3eb587e0f00748c3a9b63f9eeedc1646e4cb77be |
| Source matches recorded profile commit | True |
| Source matches benchmark commit | True |
| Preserved profile source | Cloning.PCTUnitaryTransportChannels-1.source.lean.txt |
| Configuration matches benchmark | True |
| Source/config/artifact/setup inputs stable | True |
| Measurement valid | True |
| Profile mode | firefox |
| Import context | Cloning.PCTUnitaryTransportChannels-1.import-context.json |

Controlled profile environment: `{'LAKE_ARTIFACT_CACHE': 'false', 'LEAN_NUM_THREADS': '2'}`. The raw metadata records selected effective environment and import paths.

| Configuration input | SHA-256 |
| --- | --- |
| formalization/lake-manifest.json | e4630915680b82b58c6a005e1ba1e515e865e5541c7e665d4a2d57f783eeadb4 |
| formalization/lakefile.toml | ddeb0d2c8217676fc393afd24c13629993c580f35f9d8ad15240c6a167b020c1 |
| formalization/lean-toolchain | dc6d65016fad3123d44bf17b5bf0598286284ab16ba75d5c17eb22ed11f47361 |

| Lean environment statistic | Value |
| --- | --- |
| Environment extensions | 302 |
| Imported constant-map buckets | 2097152 |
| Imported constants | 440341 |
| Imported compacted-region bytes (not RSS) | 4104050792 |
| Imported compacted regions (Lean labels these modules) | 20500 |
| Memory-mapped compacted regions | 20410 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| import | 3.010 |
| interpretation | 0.713 |
| typeclass inference | 0.479 |
| tactic execution | 0.455 |
| elaboration | 0.301 |
| type checking | 0.118 |
| initialization | 0.019 |
| simp | 0.015 |
| process pre-definitions | 0.009 |
| linting | 0.006 |
| share common exprs | 0.005 |
| parsing | 0.003 |
| attribute application | 0.003 |
| fix level params | 0.001 |
| let-to-have transformation | 0.001 |
| instantiate metavars | 0.001 |
| congr simp thm | 0.001 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| import took 3.01s | 3.010 | 1 |
| elaboration took 205ms | 0.205 | 9 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 101ms | 0.101 | 2 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 3.505 | 4.196 | unattributed |
| Elab.lint: running linters | 0.145 | 0.145 | unattributed |
| Meta.isDefEq: ✅️ b.repr.toLinearEquiv.2 (lp.single 2 i 1) =?= b.repr.toLinearEquiv.2 (lp.single 2 i 1) | 0.090 | 0.090 | unattributed |
| Meta.isDefEq: ✅️ ⋯.choose.repr.toLinearEquiv.2 (lp.single 2 i 1) =?= ⋯.choose.repr.toLinearEquiv.2 (lp.single 2 i 1) | 0.071 | 0.167 | unattributed |
| Elab.step: Lean.Parser.Tactic.rewriteSeq: rewrite [← frameState_transport, tensorUnitary_star, unitaryChannel_star] | 0.047 | 0.097 | unattributed |
| Elab.step: Lean.Parser.Tactic.rewriteSeq: rewrite [← tensorState_conjugated, tensorUnitary_star, unitaryChannel_star] | 0.046 | 0.095 | unattributed |
| Elab.step: Lean.Parser.Tactic.rewriteSeq: rewrite [frameState_val, frameState_val, reduced_frameParticle_transport, tensor_unitaryChannel_matrixTensorPower] | 0.039 | 0.075 | unattributed |
| Elab.step: Lean.Parser.Tactic.rewriteSeq: rewrite [hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one] | 0.039 | 0.104 | unattributed |
| Elab.step: Lean.Parser.Term.binop: expected type: Matrix A A ℂ, term binop% HMul.hMul✝ ((U : Matrix A A ℂ) * ρ.matrix) (U : Matrix A A ℂ)ᴴ | 0.037 | 0.037 | unattributed |
| Meta.check: ✅️ fun _a =>   Cloning.PCTPurificationChannel.registerLiftCLM _a =     Cloning.PCTPurificationChannel.registerLiftCLM       (Cloning.InfiniteFiniteCorner.matrixOf ⇑(Cloning.PCT.registerBasis A) ↑X) | 0.023 | 0.023 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 3.505 | 4.196 | unattributed |
| Elab.command: Lean.Parser.Command.definition: /-- Postcompose a reverse mixed channel with an actual quantum channel. -/ def postQuantum {Ω H K J : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [NormedAddCommGroup H] [InnerProductSpace ℂ H]     [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpac | 0.006 | 0.294 | Cloning.PCTUnitaryTransport.postQuantum at formalization/Cloning/PCTUnitaryTransportChannels.lean:81 |
| Elab.definition.value: Cloning.PCTUnitaryTransport.postQuantum | 0.000 | 0.271 | Cloning.PCTUnitaryTransport.postQuantum at formalization/Cloning/PCTUnitaryTransportChannels.lean:81 |
| Elab.step: Lean.Parser.Term.structInst: expected type: Cloning.Hybrid.HybridToQuantum H J μ, term { map := M.toPositiveTracePreservingMap.toContinuousLinearMap.comp S.map,   completelyPositive := fun n X hX => M.completelyPositive n _ (S.completelyPositive n X hX),   tracePreserving := fun X => (M.t | 0.009 | 0.271 | unattributed |
| Elab.async: elaborating proof of Cloning.PCTUnitaryTransport.unitaryChannel_star | 0.002 | 0.221 | unattributed |
| Elab.definition.value: Cloning.PCTUnitaryTransport.unitaryChannel_star | 0.001 | 0.218 | Cloning.PCTUnitaryTransport.unitaryChannel_star at formalization/Cloning/PCTUnitaryTransportChannels.lean:23 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   rw [← Cloning.PCTGlobal.registerLiftCLM_matrixOf X, unitaryChannel_registerLift, unitaryChannel_registerLift]   have hU : (U : Matrix A A ℂ)ᴴ * U = 1 := Unitary.star_mul_self_of_mem U.property   simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose, Mat | 0.000 | 0.218 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   rw [← Cloning.PCTGlobal.registerLiftCLM_matrixOf X, unitaryChannel_registerLift, unitaryChannel_registerLift]   have hU : (U : Matrix A A ℂ)ᴴ * U = 1 := Unitary.star_mul_self_of_mem U.property   simp only [Unitary.coe_star, Matrix.star_eq_conjTrans | 0.000 | 0.218 | unattributed |
| Meta.isDefEq: ✅️ ⋯.choose i =?= ⋯.choose i | 0.000 | 0.170 | unattributed |
| Meta.isDefEq: ✅️ HilbertBasis.instFunLike.1 ⋯.choose i =?= HilbertBasis.instFunLike.1 ⋯.choose i | 0.000 | 0.170 | unattributed |

Unattributed elaboration events above threshold: 1; the detailed trace rankings supply attribution where their labels identify declarations.

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.PCTUnitaryTransportChannels-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.PCTUnitaryTransportChannels-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.PCTUnitaryTransportChannels-1.setup.json Cloning/PCTUnitaryTransportChannels.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.InfiniteTraceClass — repetition 1

Recorded profile commit: `3eb587e0f00748c3a9b63f9eeedc1646e4cb77be`; source SHA-256: `8989a10ec2f035d84eeadeb1ab47af9dbbbb80ccbfcdf85f31577d3c5e55f3c9`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | 3eb587e0f00748c3a9b63f9eeedc1646e4cb77be |
| Source matches recorded profile commit | True |
| Source matches benchmark commit | True |
| Preserved profile source | Cloning.InfiniteTraceClass-1.source.lean.txt |
| Configuration matches benchmark | True |
| Source/config/artifact/setup inputs stable | True |
| Measurement valid | True |
| Profile mode | firefox |
| Import context | Cloning.InfiniteTraceClass-1.import-context.json |

Controlled profile environment: `{'LAKE_ARTIFACT_CACHE': 'false', 'LEAN_NUM_THREADS': '2'}`. The raw metadata records selected effective environment and import paths.

| Configuration input | SHA-256 |
| --- | --- |
| formalization/lake-manifest.json | e4630915680b82b58c6a005e1ba1e515e865e5541c7e665d4a2d57f783eeadb4 |
| formalization/lakefile.toml | ddeb0d2c8217676fc393afd24c13629993c580f35f9d8ad15240c6a167b020c1 |
| formalization/lean-toolchain | dc6d65016fad3123d44bf17b5bf0598286284ab16ba75d5c17eb22ed11f47361 |

| Lean environment statistic | Value |
| --- | --- |
| Environment extensions | 302 |
| Imported constant-map buckets | 2097152 |
| Imported constants | 429787 |
| Imported compacted-region bytes (not RSS) | 3928341488 |
| Imported compacted regions (Lean labels these modules) | 19760 |
| Memory-mapped compacted regions | 19678 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| typeclass inference | 22.300 |
| import | 2.270 |
| tactic execution | 2.030 |
| interpretation | 1.400 |
| type checking | 1.400 |
| elaboration | 0.291 |
| simp | 0.079 |
| process pre-definitions | 0.043 |
| linting | 0.039 |
| instantiate metavars | 0.028 |
| share common exprs | 0.027 |
| initialization | 0.019 |
| parsing | 0.014 |
| fix level params | 0.008 |
| congr simp thm | 0.002 |
| let-to-have transformation | 0.001 |
| compilation (LCNF base) | 0.000 |
| compilation (LCNF mono) | 0.000 |
| attribute application | 0.000 |
| compilation (LCNF impure) | 0.000 |
| compilation (IR) | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| import took 2.27s | 2.270 | 1 |
| typeclass inference of NegPart took 233ms | 0.233 | 18 |
| typeclass inference of PosPart took 220ms | 0.220 | 32 |
| typeclass inference of NegPart took 216ms | 0.216 | 14 |
| type checking took 180ms | 0.180 | 7 |
| typeclass inference of NegPart took 179ms | 0.179 | 33 |
| typeclass inference of PosPart took 172ms | 0.172 | 20 |
| typeclass inference of AddLeftMono took 170ms | 0.170 | 15 |
| typeclass inference of CoeFun took 164ms | 0.164 | 30 |
| typeclass inference of PosPart took 157ms | 0.157 | 10 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 5.820 | 11.352 | unattributed |
| Meta.synthInstance: ✅️ Algebra ℝ (H →L[ℂ] H) | 4.944 | 8.982 | unattributed |
| Meta.isDefEq: ❌️ Complex.commRing.toSemiring =?= NormedField.toField.toSemiring | 1.330 | 1.645 | unattributed |
| Meta.synthInstance: ✅️ Algebra ℂ (H →L[ℂ] H) | 1.015 | 1.571 | unattributed |
| Meta.synthInstance: ✅️ Module ℝ (H →L[ℂ] H) | 1.011 | 1.218 | unattributed |
| Meta.synthInstance: ✅️ Module ℂ (H →L[ℂ] H) | 0.751 | 1.145 | unattributed |
| Meta.synthInstance: ❌️ Module ℝ H | 0.638 | 1.555 | unattributed |
| Meta.check: ✅️ IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus | 0.512 | 0.512 | unattributed |
| Meta.check: ✅️ ContinuousLinearMap.instNonnegSpectrumClassRealId | 0.387 | 0.387 | unattributed |
| Meta.synthInstance: ✅️ PosPart (H →L[ℂ] H) | 0.380 | 2.581 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 5.820 | 11.352 | unattributed |
| Meta.synthInstance: ✅️ Algebra ℝ (H →L[ℂ] H) | 4.944 | 8.982 | unattributed |
| Elab.step: Lean.Parser.Term.paren: expected type: <not-available>, term (⟪b i, CFC.abs T (b i)⟫_ℂ) | 0.000 | 6.266 | unattributed |
| Elab.step: InnerProductSpace.«term⟪_,_⟫__»: expected type: <not-available>, term ⟪b i, CFC.abs T (b i)⟫_ℂ | 0.001 | 6.266 | unattributed |
| Elab.step: Lean.Parser.Term.app: expected type: <not-available>, term inner✝ ℂ (b i) (CFC.abs T (b i)) | 0.008 | 6.265 | unattributed |
| Elab.step: Lean.Parser.Term.app: expected type: H, term CFC.abs T (b i) | 0.375 | 6.258 | unattributed |
| Meta.synthInstance: ✅️ apply @Algebra.to_smulCommClass to SMulCommClass ℝ (H →L[ℂ] H) (H →L[ℂ] H) | 0.002 | 5.472 | unattributed |
| Meta.synthInstance.tryResolve: ✅️ SMulCommClass ℝ (H →L[ℂ] H) (H →L[ℂ] H) ≟ SMulCommClass ℝ (H →L[ℂ] H) (H →L[ℂ] H) | 0.040 | 5.471 | unattributed |
| Elab.step: Lean.Parser.Term.proj: expected type: ℝ, term (⟪b i, CFC.abs T (b i)⟫_ℂ).re | 0.000 | 5.223 | unattributed |
| Meta.synthInstance: ✅️ SMulCommClass ℝ (H →L[ℂ] H) (H →L[ℂ] H) | 0.117 | 3.971 | unattributed |

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.InfiniteTraceClass-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.InfiniteTraceClass-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.InfiniteTraceClass-1.setup.json Cloning/InfiniteTraceClass.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.Thermal — repetition 1

Recorded profile commit: `3eb587e0f00748c3a9b63f9eeedc1646e4cb77be`; source SHA-256: `d3dc50c83b60b9e7a734b11aed79064d33bbdf3b44b9b210f093f1c94e0b9a91`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | 3eb587e0f00748c3a9b63f9eeedc1646e4cb77be |
| Source matches recorded profile commit | True |
| Source matches benchmark commit | True |
| Preserved profile source | Cloning.Thermal-1.source.lean.txt |
| Configuration matches benchmark | True |
| Source/config/artifact/setup inputs stable | True |
| Measurement valid | True |
| Profile mode | firefox |
| Import context | Cloning.Thermal-1.import-context.json |

Controlled profile environment: `{'LAKE_ARTIFACT_CACHE': 'false', 'LEAN_NUM_THREADS': '2'}`. The raw metadata records selected effective environment and import paths.

| Configuration input | SHA-256 |
| --- | --- |
| formalization/lake-manifest.json | e4630915680b82b58c6a005e1ba1e515e865e5541c7e665d4a2d57f783eeadb4 |
| formalization/lakefile.toml | ddeb0d2c8217676fc393afd24c13629993c580f35f9d8ad15240c6a167b020c1 |
| formalization/lean-toolchain | dc6d65016fad3123d44bf17b5bf0598286284ab16ba75d5c17eb22ed11f47361 |

| Lean environment statistic | Value |
| --- | --- |
| Environment extensions | 292 |
| Imported constant-map buckets | 2097152 |
| Imported constants | 332509 |
| Imported compacted-region bytes (not RSS) | 2980554984 |
| Imported compacted regions (Lean labels these modules) | 14856 |
| Memory-mapped compacted regions | 14793 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| interpretation | 2.890 |
| typeclass inference | 2.530 |
| import | 1.750 |
| simp | 0.512 |
| tactic execution | 0.500 |
| ring | 0.271 |
| type checking | 0.226 |
| elaboration | 0.165 |
| norm_num | 0.066 |
| linting | 0.066 |
| share common exprs | 0.041 |
| process pre-definitions | 0.029 |
| parsing | 0.020 |
| initialization | 0.019 |
| instantiate metavars | 0.013 |
| congr simp thm | 0.005 |
| fix level params | 0.003 |
| compilation (LCNF base) | 0.003 |
| compilation (LCNF mono) | 0.002 |
| let-to-have transformation | 0.002 |
| compilation (LCNF impure) | 0.001 |
| compilation (IR) | 0.000 |
| attribute application | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| import took 1.75s | 1.750 | 1 |
| interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 278ms | 0.278 | 5 |
| interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 234ms | 0.234 | 2 |
| interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 171ms | 0.171 | 3 |
| interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 161ms | 0.161 | 4 |
| interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 137ms | 0.137 | 6 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 3.130 | 3.179 | unattributed |
| linarith: ✅️ adding product terms | 0.980 | 1.103 | unattributed |
| linarith: ✅️ running on preferred type ℝ | 0.670 | 1.389 | unattributed |
| Elab.step: Mathlib.Tactic.Ring.ring1: ring1 | 0.308 | 0.308 | unattributed |
| Meta.synthInstance: ❌️ Nonempty (Fin s) | 0.285 | 0.285 | unattributed |
| linarith.detail: ✅️ linearFormsAndMaxVar | 0.265 | 0.265 | unattributed |
| linarith: ✅️ Invoking oracle | 0.255 | 0.255 | unattributed |
| Elab.step: Mathlib.Tactic.linarith: linarith | 0.163 | 0.749 | unattributed |
| Elab.lint: running linters | 0.160 | 0.180 | unattributed |
| linarith: ✅️ Running preprocessors | 0.107 | 1.359 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 3.130 | 3.179 | unattributed |
| linarith: ✅️ running on preferred type ℝ | 0.670 | 1.389 | unattributed |
| linarith: ✅️ Running preprocessors | 0.107 | 1.359 | unattributed |
| linarith: ✅️ Mathlib.Tactic.Linarith.nlinarithExtras: nonlinear arithmetic extras | 0.051 | 1.188 | unattributed |
| linarith: ✅️ adding product terms | 0.980 | 1.103 | unattributed |
| Elab.step: Mathlib.Tactic.nlinarith: nlinarith | 0.030 | 1.010 | unattributed |
| Elab.step: Mathlib.Tactic.linarith: linarith | 0.163 | 0.749 | unattributed |
| Elab.async: elaborating proof of Cloning.Thermal.fidelity_le_one | 0.003 | 0.675 | unattributed |
| Elab.definition.value: Cloning.Thermal.fidelity_le_one | 0.002 | 0.672 | Cloning.Thermal.fidelity_le_one at formalization/Cloning/Thermal.lean:93 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   have hprod : q * x < 1 := mul_lt_one_of_nonneg_of_lt_one_right hq1.le hx0 hx1   have hsqrt : Real.sqrt q * Real.sqrt x < 1 :=     by     rw [← Real.sqrt_mul hq0, Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]     simpa using hprod   have hsq : (Real.sqrt q * Re | 0.000 | 0.670 | unattributed |

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.Thermal-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.Thermal-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.Thermal-1.setup.json Cloning/Thermal.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.AmplifierWeylThermal — repetition 1

Recorded profile commit: `3eb587e0f00748c3a9b63f9eeedc1646e4cb77be`; source SHA-256: `eeee0e083b71ae3155a11fc033a5cd888fcac86911f4ed7cfe97ab77fce4760b`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | 3eb587e0f00748c3a9b63f9eeedc1646e4cb77be |
| Source matches recorded profile commit | True |
| Source matches benchmark commit | True |
| Preserved profile source | Cloning.AmplifierWeylThermal-1.source.lean.txt |
| Configuration matches benchmark | True |
| Source/config/artifact/setup inputs stable | True |
| Measurement valid | True |
| Profile mode | firefox |
| Import context | Cloning.AmplifierWeylThermal-1.import-context.json |

Controlled profile environment: `{'LAKE_ARTIFACT_CACHE': 'false', 'LEAN_NUM_THREADS': '2'}`. The raw metadata records selected effective environment and import paths.

| Configuration input | SHA-256 |
| --- | --- |
| formalization/lake-manifest.json | e4630915680b82b58c6a005e1ba1e515e865e5541c7e665d4a2d57f783eeadb4 |
| formalization/lakefile.toml | ddeb0d2c8217676fc393afd24c13629993c580f35f9d8ad15240c6a167b020c1 |
| formalization/lean-toolchain | dc6d65016fad3123d44bf17b5bf0598286284ab16ba75d5c17eb22ed11f47361 |

| Lean environment statistic | Value |
| --- | --- |
| Environment extensions | 302 |
| Imported constant-map buckets | 2097152 |
| Imported constants | 436981 |
| Imported compacted-region bytes (not RSS) | 4029008984 |
| Imported compacted regions (Lean labels these modules) | 20237 |
| Memory-mapped compacted regions | 20148 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| import | 3.490 |
| typeclass inference | 1.280 |
| interpretation | 0.844 |
| tactic execution | 0.308 |
| type checking | 0.088 |
| elaboration | 0.065 |
| ring | 0.032 |
| norm_num | 0.028 |
| initialization | 0.019 |
| simp | 0.016 |
| linting | 0.008 |
| share common exprs | 0.007 |
| instantiate metavars | 0.006 |
| process pre-definitions | 0.005 |
| parsing | 0.004 |
| congr simp thm | 0.001 |
| dsimp | 0.001 |
| fix level params | 0.001 |
| let-to-have transformation | 0.000 |
| attribute application | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| import took 3.49s | 3.490 | 1 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 150ms | 0.150 | 5 |
| typeclass inference of CoeFun took 144ms | 0.144 | 6 |
| typeclass inference of CoeFun took 139ms | 0.139 | 7 |
| typeclass inference of CoeFun took 137ms | 0.137 | 4 |
| typeclass inference of CoeFun took 132ms | 0.132 | 2 |
| typeclass inference of CoeFun took 131ms | 0.131 | 3 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 4.489 | 5.224 | unattributed |
| Meta.isDefEq.delta: ✅️ SetLike.instMembership =?= SetLike.instMembership | 0.403 | 0.414 | unattributed |
| Elab.lint: running linters | 0.165 | 0.165 | unattributed |
| Elab.step: Lean.Parser.Tactic.rewriteSeq: rewrite [hm, map_smul, smul_eq_mul, vacuumProjector_characteristic,   show Φ.toLinearMap (coherentProjector 0) = vectorMixture (numberBasis d) (productGeometric (fun _ => 1 - 1 / g)) from     gainChannel_vacuum g hg,   productThermal_characteristic (fun _ => | 0.081 | 0.337 | unattributed |
| linarith: ✅️ Mathlib.Tactic.Linarith.cancelDenoms: cancel denominators | 0.064 | 0.064 | unattributed |
| Elab.step: Mathlib.Tactic.linarith: linarith | 0.051 | 0.198 | unattributed |
| Meta.synthInstance: ✅️ SMul ℂ (↥(Cloning.MultimodeCoherent.Fock d) →L[ℂ] ↥(Cloning.MultimodeCoherent.Fock d)) | 0.047 | 0.147 | unattributed |
| Meta.isDefEq.delta: ✅️ x ∈   Cloning.InfiniteTraceClass.traceClassSubmodule     ↥(Cloning.MultimodeCoherent.Fock         ?m.123) =?= x ∈ Cloning.InfiniteTraceClass.traceClassSubmodule ↥(Cloning.MultimodeCoherent.Fock ?m.123) | 0.043 | 0.128 | unattributed |
| Meta.isDefEq.delta: ✅️ x ∈   Cloning.InfiniteTraceClass.traceClassSubmodule     ↥(Cloning.MultimodeCoherent.Fock         ?m.5) =?= x ∈ Cloning.InfiniteTraceClass.traceClassSubmodule ↥(Cloning.MultimodeCoherent.Fock ?m.5) | 0.043 | 0.126 | unattributed |
| Meta.isDefEq.delta: ✅️ x ∈   Cloning.InfiniteTraceClass.traceClassSubmodule     ↥(Cloning.MultimodeCoherent.Fock         ?m.8) =?= x ∈ Cloning.InfiniteTraceClass.traceClassSubmodule ↥(Cloning.MultimodeCoherent.Fock ?m.8) | 0.042 | 0.121 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 4.489 | 5.224 | unattributed |
| Meta.isDefEq: ✅️ NormedAddCommGroup.toENormedAddCommMonoid.toAddCommMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddCommMonoid | 0.001 | 0.647 | unattributed |
| Meta.isDefEq: ✅️ { toAddMonoid := NormedAddCommGroup.toENormedAddCommMonoid.toAddMonoid,   add_comm :=     ⋯ } =?= { toAddMonoid := Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddMonoid, add_comm := ⋯ } | 0.002 | 0.647 | unattributed |
| Meta.isDefEq: ✅️ NormedAddCommGroup.toENormedAddCommMonoid.toAddMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddMonoid | 0.001 | 0.645 | unattributed |
| Meta.isDefEq: ✅️ NormedAddCommGroup.toNormedAddGroup.toAddMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddMonoid | 0.000 | 0.644 | unattributed |
| Meta.isDefEq.delta: ✅️ NormedAddCommGroup.toNormedAddGroup.toAddMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddMonoid | 0.003 | 0.643 | unattributed |
| Meta.isDefEq: ✅️ NormedAddCommGroup.toNormedAddGroup.toSubNegMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toSubNegMonoid | 0.000 | 0.641 | unattributed |
| Meta.isDefEq.delta: ✅️ NormedAddCommGroup.toNormedAddGroup.toSubNegMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toSubNegMonoid | 0.001 | 0.640 | unattributed |
| Meta.isDefEq: ✅️ NormedAddCommGroup.toNormedAddGroup.toAddGroup =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddGroup | 0.001 | 0.639 | unattributed |
| Meta.isDefEq: ✅️ Cloning.InfiniteTraceClass.TraceClass.instNormedAddCommGroup.toAddGroup =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddGroup | 0.000 | 0.639 | unattributed |

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.AmplifierWeylThermal-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.AmplifierWeylThermal-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.AmplifierWeylThermal-1.setup.json Cloning/AmplifierWeylThermal.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.PCTClosedForm — repetition 1

Recorded profile commit: `3eb587e0f00748c3a9b63f9eeedc1646e4cb77be`; source SHA-256: `a237c4cbc91c79ac818a1a4b7ca3c4445c8e4eba19dd333600b7d727e219c846`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | 3eb587e0f00748c3a9b63f9eeedc1646e4cb77be |
| Source matches recorded profile commit | True |
| Source matches benchmark commit | True |
| Preserved profile source | Cloning.PCTClosedForm-1.source.lean.txt |
| Configuration matches benchmark | True |
| Source/config/artifact/setup inputs stable | True |
| Measurement valid | True |
| Profile mode | firefox |
| Import context | Cloning.PCTClosedForm-1.import-context.json |

Controlled profile environment: `{'LAKE_ARTIFACT_CACHE': 'false', 'LEAN_NUM_THREADS': '2'}`. The raw metadata records selected effective environment and import paths.

| Configuration input | SHA-256 |
| --- | --- |
| formalization/lake-manifest.json | e4630915680b82b58c6a005e1ba1e515e865e5541c7e665d4a2d57f783eeadb4 |
| formalization/lakefile.toml | ddeb0d2c8217676fc393afd24c13629993c580f35f9d8ad15240c6a167b020c1 |
| formalization/lean-toolchain | dc6d65016fad3123d44bf17b5bf0598286284ab16ba75d5c17eb22ed11f47361 |

| Lean environment statistic | Value |
| --- | --- |
| Environment extensions | 302 |
| Imported constant-map buckets | 2097152 |
| Imported constants | 402298 |
| Imported compacted-region bytes (not RSS) | 3613593264 |
| Imported compacted regions (Lean labels these modules) | 18056 |
| Memory-mapped compacted regions | 17976 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| import | 2.320 |
| interpretation | 1.120 |
| typeclass inference | 0.340 |
| tactic execution | 0.113 |
| ring | 0.047 |
| type checking | 0.030 |
| simp | 0.025 |
| initialization | 0.019 |
| elaboration | 0.016 |
| norm_num | 0.010 |
| linting | 0.010 |
| share common exprs | 0.007 |
| process pre-definitions | 0.004 |
| instantiate metavars | 0.003 |
| parsing | 0.003 |
| fix level params | 0.000 |
| congr simp thm | 0.000 |
| blocked (unaccounted) | 0.000 |
| let-to-have transformation | 0.000 |
| attribute application | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| import took 2.32s | 2.320 | 1 |
| interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 245ms | 0.245 | 5 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 3.274 | 3.314 | unattributed |
| linarith: ✅️ adding product terms | 0.186 | 0.186 | unattributed |
| Elab.lint: running linters | 0.135 | 0.135 | unattributed |
| linarith: ✅️ running on preferred type ℝ | 0.084 | 0.266 | unattributed |
| linarith.detail: ✅️ linearFormsAndMaxVar | 0.075 | 0.075 | unattributed |
| Tactic.field_simp: ✅️ discharge √(g + q * (g - 1)) ≠ 0 | 0.072 | 0.072 | unattributed |
| linarith: ✅️ Invoking oracle | 0.062 | 0.062 | unattributed |
| Tactic.field_simp: ✅️ discharge g + q * (g - 1) ≠ 0 | 0.047 | 0.047 | unattributed |
| Elab.step: Mathlib.Tactic.Ring.ring1: ring1 | 0.044 | 0.044 | unattributed |
| Elab.step: Mathlib.Tactic.Positivity.positivity: positivity | 0.042 | 0.042 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 3.274 | 3.314 | unattributed |
| Elab.async: elaborating proof of Cloning.Thermal.fidelity_pct_closedForm | 0.004 | 0.512 | unattributed |
| Elab.definition.value: Cloning.Thermal.fidelity_pct_closedForm | 0.003 | 0.508 | Cloning.Thermal.fidelity_pct_closedForm at formalization/Cloning/PCTClosedForm.lean:33 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   have hg0 : 0 < g := by linarith   have hg1 : 0 ≤ g - 1 := by linarith   have hrad : 0 ≤ q * (g - 1 + g * q) := mul_nonneg hq0 (add_nonneg hg1 (mul_nonneg hg0.le hq0))   have hdpos : 0 < g + (g - 1) * q := add_pos_of_pos_of_nonneg hg0 (mul_nonneg hg1 hq0)    | 0.000 | 0.505 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   have hg0 : 0 < g := by linarith   have hg1 : 0 ≤ g - 1 := by linarith   have hrad : 0 ≤ q * (g - 1 + g * q) := mul_nonneg hq0 (add_nonneg hg1 (mul_nonneg hg0.le hq0))   have hdpos : 0 < g + (g - 1) * q := add_pos_of_pos_of_nonneg hg0 (mul_nonneg hg | 0.011 | 0.505 | unattributed |
| Elab.async: elaborating proof of Cloning.Thermal.fidelity_pct_unrationalized | 0.005 | 0.348 | unattributed |
| Elab.definition.value: Cloning.Thermal.fidelity_pct_unrationalized | 0.003 | 0.343 | Cloning.Thermal.fidelity_pct_unrationalized at formalization/Cloning/PCTClosedForm.lean:8 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   have hg0 : 0 < g := by linarith   have hg1 : 0 ≤ g - 1 := by linarith   have hdpos : 0 < g + (g - 1) * q := add_pos_of_pos_of_nonneg hg0 (mul_nonneg hg1 hq0)   have hd : g + (g - 1) * q ≠ 0 := hdpos.ne'   have hs : Real.sqrt (g + (g - 1) * q) ≠ 0 := (Real.s | 0.000 | 0.339 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   have hg0 : 0 < g := by linarith   have hg1 : 0 ≤ g - 1 := by linarith   have hdpos : 0 < g + (g - 1) * q := add_pos_of_pos_of_nonneg hg0 (mul_nonneg hg1 hq0)   have hd : g + (g - 1) * q ≠ 0 := hdpos.ne'   have hs : Real.sqrt (g + (g - 1) * q) ≠ 0 : | 0.018 | 0.339 | unattributed |
| Elab.step: Mathlib.Tactic.nlinarith: nlinarith [Real.sq_sqrt hdpos.le, Real.sq_sqrt hrad] | 0.001 | 0.316 | unattributed |

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.PCTClosedForm-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.PCTClosedForm-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.PCTClosedForm-1.setup.json Cloning/PCTClosedForm.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.CloningValueComparisonMonotone — repetition 1

Recorded profile commit: `3eb587e0f00748c3a9b63f9eeedc1646e4cb77be`; source SHA-256: `0dbf7031761a5f1b7e1352befdb6a4284734445e63799b3726977bb7c8312551`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | 3eb587e0f00748c3a9b63f9eeedc1646e4cb77be |
| Source matches recorded profile commit | True |
| Source matches benchmark commit | True |
| Preserved profile source | Cloning.CloningValueComparisonMonotone-1.source.lean.txt |
| Configuration matches benchmark | True |
| Source/config/artifact/setup inputs stable | True |
| Measurement valid | True |
| Profile mode | firefox |
| Import context | Cloning.CloningValueComparisonMonotone-1.import-context.json |

Controlled profile environment: `{'LAKE_ARTIFACT_CACHE': 'false', 'LEAN_NUM_THREADS': '2'}`. The raw metadata records selected effective environment and import paths.

| Configuration input | SHA-256 |
| --- | --- |
| formalization/lake-manifest.json | e4630915680b82b58c6a005e1ba1e515e865e5541c7e665d4a2d57f783eeadb4 |
| formalization/lakefile.toml | ddeb0d2c8217676fc393afd24c13629993c580f35f9d8ad15240c6a167b020c1 |
| formalization/lean-toolchain | dc6d65016fad3123d44bf17b5bf0598286284ab16ba75d5c17eb22ed11f47361 |

| Lean environment statistic | Value |
| --- | --- |
| Environment extensions | 302 |
| Imported constant-map buckets | 2097152 |
| Imported constants | 402864 |
| Imported compacted-region bytes (not RSS) | 3619196504 |
| Imported compacted regions (Lean labels these modules) | 18120 |
| Memory-mapped compacted regions | 18043 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| interpretation | 2.790 |
| import | 2.110 |
| typeclass inference | 0.351 |
| tactic execution | 0.081 |
| ring | 0.057 |
| type checking | 0.056 |
| elaboration | 0.024 |
| initialization | 0.019 |
| linting | 0.017 |
| share common exprs | 0.010 |
| instantiate metavars | 0.009 |
| process pre-definitions | 0.007 |
| norm_num | 0.005 |
| simp | 0.005 |
| parsing | 0.004 |
| fix level params | 0.001 |
| congr simp thm | 0.000 |
| let-to-have transformation | 0.000 |
| attribute application | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| import took 2.11s | 2.110 | 1 |
| interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 1s | 1.000 | 3 |
| interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 907ms | 0.907 | 2 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 5.079 | 5.103 | unattributed |
| linarith.detail: ✅️ linearFormsAndMaxVar | 1.036 | 1.036 | unattributed |
| linarith: ✅️ Invoking oracle | 0.492 | 0.492 | unattributed |
| linarith: ✅️ adding product terms | 0.400 | 0.400 | unattributed |
| linarith: ✅️ running on preferred type ℝ | 0.165 | 1.723 | unattributed |
| Elab.lint: running linters | 0.107 | 0.118 | unattributed |
| Elab.step: Mathlib.Tactic.linarith: linarith | 0.066 | 0.173 | unattributed |
| Elab.step: Mathlib.Tactic.Positivity.positivity: positivity | 0.059 | 0.059 | unattributed |
| Elab.step: Mathlib.Tactic.FieldSimp.fieldSimp: field_simp [hr0, hs0, hden, hsum] | 0.050 | 0.074 | unattributed |
| linarith: ✅️ finding squares | 0.048 | 0.048 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 5.079 | 5.103 | unattributed |
| Elab.async: elaborating proof of Cloning.ValueComparison.modeFactor_hasDerivAt | 0.014 | 2.433 | unattributed |
| Elab.definition.value: Cloning.ValueComparison.modeFactor_hasDerivAt | 0.013 | 2.420 | Cloning.ValueComparison.modeFactor_hasDerivAt at formalization/Cloning/CloningValueComparisonMonotone.lean:14 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   have hg0 : 0 < g := by linarith   have hv : 0 < g - 1 + q := by linarith   have hrad : 0 < q * (g - 1 + q) := mul_pos hq hv   have hden : g + q ≠ 0 := ne_of_gt (add_pos hg0 hq)   have hd :=     (((hasDerivAt_const q (Real.sqrt g)).add           (((hasDerivA | 0.000 | 2.407 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   have hg0 : 0 < g := by linarith   have hv : 0 < g - 1 + q := by linarith   have hrad : 0 < q * (g - 1 + q) := mul_pos hq hv   have hden : g + q ≠ 0 := ne_of_gt (add_pos hg0 hq)   have hd :=     (((hasDerivAt_const q (Real.sqrt g)).add           ((( | 0.038 | 2.407 | unattributed |
| linarith: ✅️ running on preferred type ℝ | 0.165 | 1.723 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticHave__: have hprod :   (Real.sqrt g * Real.sqrt (g - 1 + q) - Real.sqrt q) * (Real.sqrt g * Real.sqrt (g - 1 + q) + Real.sqrt q) =     (g - 1) * (g + q) :=   by nlinarith [htsq] | 0.000 | 1.077 | unattributed |
| Elab.step: Lean.Parser.Tactic.focus: focus   refine     no_implicit_lambda%       (have hprod :         (Real.sqrt g * Real.sqrt (g - 1 + q) - Real.sqrt q) * (Real.sqrt g * Real.sqrt (g - 1 + q) + Real.sqrt q) =           (g - 1) * (g + q) :=         ?body✝;       ?_)   case body✝ => with_annotate_s | 0.000 | 1.077 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   refine     no_implicit_lambda%       (have hprod :         (Real.sqrt g * Real.sqrt (g - 1 + q) - Real.sqrt q) * (Real.sqrt g * Real.sqrt (g - 1 + q) + Real.sqrt q) =           (g - 1) * (g + q) :=         ?body✝;       ?_)   case body✝ => with_annotate_sta | 0.000 | 1.077 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   refine     no_implicit_lambda%       (have hprod :         (Real.sqrt g * Real.sqrt (g - 1 + q) - Real.sqrt q) * (Real.sqrt g * Real.sqrt (g - 1 + q) + Real.sqrt q) =           (g - 1) * (g + q) :=         ?body✝;       ?_)   case body✝ => with_ann | 0.004 | 1.077 | unattributed |

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.CloningValueComparisonMonotone-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.CloningValueComparisonMonotone-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.CloningValueComparisonMonotone-1.setup.json Cloning/CloningValueComparisonMonotone.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.TensorFlatProjectorStateFidelity — repetition 1

Recorded profile commit: `3eb587e0f00748c3a9b63f9eeedc1646e4cb77be`; source SHA-256: `576d4d68ef53b41ab4396038ced442774eda9458e3ce73d76465692333e31d62`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | 3eb587e0f00748c3a9b63f9eeedc1646e4cb77be |
| Source matches recorded profile commit | True |
| Source matches benchmark commit | True |
| Preserved profile source | Cloning.TensorFlatProjectorStateFidelity-1.source.lean.txt |
| Configuration matches benchmark | True |
| Source/config/artifact/setup inputs stable | True |
| Measurement valid | True |
| Profile mode | firefox |
| Import context | Cloning.TensorFlatProjectorStateFidelity-1.import-context.json |

Controlled profile environment: `{'LAKE_ARTIFACT_CACHE': 'false', 'LEAN_NUM_THREADS': '2'}`. The raw metadata records selected effective environment and import paths.

| Configuration input | SHA-256 |
| --- | --- |
| formalization/lake-manifest.json | e4630915680b82b58c6a005e1ba1e515e865e5541c7e665d4a2d57f783eeadb4 |
| formalization/lakefile.toml | ddeb0d2c8217676fc393afd24c13629993c580f35f9d8ad15240c6a167b020c1 |
| formalization/lean-toolchain | dc6d65016fad3123d44bf17b5bf0598286284ab16ba75d5c17eb22ed11f47361 |

| Lean environment statistic | Value |
| --- | --- |
| Environment extensions | 313 |
| Imported constant-map buckets | 2097152 |
| Imported constants | 489133 |
| Imported compacted-region bytes (not RSS) | 4706667208 |
| Imported compacted regions (Lean labels these modules) | 22792 |
| Memory-mapped compacted regions | 22705 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| tactic execution | 54.700 |
| typeclass inference | 4.900 |
| interpretation | 4.230 |
| import | 3.940 |
| elaboration | 0.691 |
| type checking | 0.167 |
| initialization | 0.019 |
| linting | 0.007 |
| dsimp | 0.004 |
| parsing | 0.004 |
| process pre-definitions | 0.003 |
| share common exprs | 0.002 |
| instantiate metavars | 0.002 |
| norm_num | 0.001 |
| let-to-have transformation | 0.001 |
| fix level params | 0.000 |
| attribute application | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| tactic execution of Lean.Parser.Tactic.exact took 40.1s | 40.100 | 23 |
| tactic execution of Lean.Parser.Tactic.exact took 12.2s | 12.200 | 19 |
| import took 3.94s | 3.940 | 1 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 1.67s | 1.670 | 10 |
| elaboration took 475ms | 0.475 | 24 |
| typeclass inference of CompleteSpace took 422ms | 0.422 | 12 |
| typeclass inference of CompleteSpace took 416ms | 0.416 | 15 |
| typeclass inference of CompleteSpace took 412ms | 0.412 | 13 |
| typeclass inference of CompleteSpace took 411ms | 0.411 | 14 |
| typeclass inference of InnerProductSpace took 270ms | 0.270 | 16 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 64.041 | 64.912 | unattributed |
| Meta.isDefEq: ❌️ (Cloning.TensorCloning.partitionTransitionChannel (Cloning.TensorLie.padPartition mu k)     (Cloning.TensorLie.padPartition lam k) ⋯     ⋯).1 =?= (Cloning.TensorCloning.partitionTransitionChannel (Cloning.TensorLie.padPartition mu k)     (Cloning.TensorLie.padPartition (↑?m.405) k)  | 18.955 | 18.955 | unattributed |
| Meta.isDefEq: ❌️ if h :     Cloning.TensorCloning.PartitionCompatible (Cloning.TensorLie.padPartition mu k)       (Cloning.TensorLie.padPartition lam k) then   have he := ⋯;   let a :=     ⟨fun i =>       Cloning.TensorLie.padPartition mu k i +         (Cloning.TensorLie.padPartition lam k i - Cloni | 15.389 | 15.389 | unattributed |
| Meta.isDefEq: ❌️ (Cloning.TensorCloning.partitionTransitionChannel (Cloning.TensorLie.padPartition mu k)     (Cloning.TensorLie.padPartition (fun a => mu a + nu a) k) ⋯     ⋯).toLinearMap =?= (Cloning.TensorCloning.partitionTransitionChannel (Cloning.TensorLie.padPartition mu k) ↑?m.309 ⋯     ⋯).toL | 6.129 | 6.149 | unattributed |
| Meta.isDefEq: ❌️ (Cloning.TensorCloning.partitionTransitionChannel (Cloning.TensorLie.padPartition mu k)       (Cloning.TensorLie.padPartition (fun a => mu a + nu a) k) ⋯       ⋯).toLinearMap.1 =?= (Cloning.TensorCloning.partitionTransitionChannel (Cloning.TensorLie.padPartition mu k)       ↑?m.309  | 4.443 | 4.443 | unattributed |
| Meta.isDefEq: ❌️ Cloning.TensorCloning.partitionTransitionChannel (Cloning.TensorLie.padPartition mu k)   (Cloning.TensorLie.padPartition lam k) ⋯   ⋯ =?= Cloning.TensorCloning.partitionTransitionChannel (Cloning.TensorLie.padPartition mu k)   (Cloning.TensorLie.padPartition (↑?m.405) k) ⋯ ⋯ | 2.873 | 18.262 | unattributed |
| Elab.step: Lean.Parser.Tactic.rewriteSeq: rewrite [partitionTransitionChannel_add, nonnegativePartitionGibbsPositive_pad_sum mu nu hmu hnu k hr,   nonnegativePartitionGibbsPositive_pad_rankFlat mu hmu k hr] | 0.844 | 1.669 | unattributed |
| Meta.isDefEq.delta: ✅️ if hp : 2 = 0 then   Eq.ndrec (motive := fun {p} => ↥(lp (fun x => ℂ) p) → ℝ) (fun f => ↑⋯.toFinset.card) ⋯     (-(Cloning.TensorLie.cyclicSector                 (Cloning.TensorLie.partitionHighestTensor (Cloning.TensorLie.padPartition mu k)                   ⋯)).subtype.toAdd | 0.805 | 0.805 | unattributed |
| Meta.isDefEq: ❌️ Quot.liftOn Finset.univ.val (fun l => ↑(List.map (fun i => Cloning.TensorLie.padPartition lam k i) l))   ⋯ =?= Quot.liftOn Finset.univ.val (fun l => ↑(List.map (fun i => Cloning.TensorLie.padPartition (↑?m.405) k i) l)) ⋯ | 0.716 | 0.716 | unattributed |
| Meta.isDefEq: ❌️ (Cloning.TensorCloning.partitionTransitionChannel (Cloning.TensorLie.padPartition mu k)       (Cloning.TensorLie.padPartition lam k) ⋯       ⋯).toPositiveTracePreservingMap.1 =?= (Cloning.TensorCloning.partitionTransitionChannel       (Cloning.TensorLie.padPartition mu k) (Cloning.T | 0.699 | 18.012 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 64.041 | 64.912 | unattributed |
| Elab.async: elaborating proof of Cloning.TensorLie.partitionTransition_rankFlat_fidelity | 0.005 | 59.394 | unattributed |
| Elab.definition.value: Cloning.TensorLie.partitionTransition_rankFlat_fidelity | 0.476 | 59.388 | Cloning.TensorLie.partitionTransition_rankFlat_fidelity at formalization/Cloning/TensorFlatProjectorStateFidelity.lean:48 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   have hsum : (fun a => mu a + (lam a - mu a)) = lam := funext (fun a => Nat.add_sub_of_le (hc.1 a))   have hadd (nu : Fin r → ℕ) (hnu : Antitone nu) :     ((nonnegativePartitionGibbsPositive (padPartition mu k) (padPartition_antitone mu hmu k) (rankFlatSpect | 0.000 | 58.913 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   have hsum : (fun a => mu a + (lam a - mu a)) = lam := funext (fun a => Nat.add_sub_of_le (hc.1 a))   have hadd (nu : Fin r → ℕ) (hnu : Antitone nu) :     ((nonnegativePartitionGibbsPositive (padPartition mu k) (padPartition_antitone mu hmu k) (rank | 0.005 | 58.913 | unattributed |
| Elab.step: Lean.Parser.Tactic.exact: exact Eq.mp (congrArg P he) (hadd _ hc.2) | 0.006 | 40.067 | unattributed |
| Elab.step: Lean.Parser.Term.app: expected type: (Cloning.Hybrid.PositiveTraceClass.map         (Cloning.TensorCloning.partitionTransitionChannel (Cloning.TensorLie.padPartition mu k)             (Cloning.TensorLie.padPartition lam k) ⋯ ⋯).toPositiveTracePreservingMap         (Cloning.TensorLie.nonne | 0.006 | 40.061 | unattributed |
| Elab.step: Lean.Parser.Term.paren: expected type: P ⟨fun a => mu a + (lam a - mu a), ⋯⟩ =   ((Cloning.Hybrid.PositiveTraceClass.map           (Cloning.TensorCloning.partitionTransitionChannel (Cloning.TensorLie.padPartition mu k)               (Cloning.TensorLie.padPartition lam k) ⋯ ⋯).toPositiveTr | 0.000 | 40.054 | unattributed |
| Elab.step: Lean.Parser.Term.app: expected type: P ⟨fun a => mu a + (lam a - mu a), ⋯⟩ =   ((Cloning.Hybrid.PositiveTraceClass.map           (Cloning.TensorCloning.partitionTransitionChannel (Cloning.TensorLie.padPartition mu k)               (Cloning.TensorLie.padPartition lam k) ⋯ ⋯).toPositiveTrac | 0.003 | 40.054 | unattributed |
| Meta.isDefEq: ❌️ ?m.400 =   ((Cloning.Hybrid.PositiveTraceClass.map           (Cloning.TensorCloning.partitionTransitionChannel (Cloning.TensorLie.padPartition mu k)               (Cloning.TensorLie.padPartition lam k) ⋯ ⋯).toPositiveTracePreservingMap           (Cloning.TensorLie.nonnegativePartiti | 0.000 | 40.052 | unattributed |

Unattributed elaboration events above threshold: 2; the detailed trace rankings supply attribution where their labels identify declarations.

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.TensorFlatProjectorStateFidelity-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.TensorFlatProjectorStateFidelity-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after/Cloning.TensorFlatProjectorStateFidelity-1.setup.json Cloning/TensorFlatProjectorStateFidelity.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.PhysicalFlatConverseReduction — repetition 1

Recorded profile commit: `3eb587e0f00748c3a9b63f9eeedc1646e4cb77be`; source SHA-256: `bca45225c36db32c7041c1ebcbafd5bf974abc6bc9fc0172ace4d773088e037f`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | 3eb587e0f00748c3a9b63f9eeedc1646e4cb77be |
| Source matches recorded profile commit | True |
| Source matches benchmark commit | True |
| Preserved profile source | Cloning.PhysicalFlatConverseReduction-1.source.lean.txt |
| Configuration matches benchmark | True |
| Source/config/artifact/setup inputs stable | True |
| Measurement valid | True |
| Profile mode | native |
| Import context | native-guarded/Cloning.PhysicalFlatConverseReduction-1.import-context.json |

Controlled profile environment: `{'LAKE_ARTIFACT_CACHE': 'false', 'LEAN_NUM_THREADS': '2'}`. The raw metadata records selected effective environment and import paths.

| Configuration input | SHA-256 |
| --- | --- |
| formalization/lake-manifest.json | e4630915680b82b58c6a005e1ba1e515e865e5541c7e665d4a2d57f783eeadb4 |
| formalization/lakefile.toml | ddeb0d2c8217676fc393afd24c13629993c580f35f9d8ad15240c6a167b020c1 |
| formalization/lean-toolchain | dc6d65016fad3123d44bf17b5bf0598286284ab16ba75d5c17eb22ed11f47361 |

| Lean environment statistic | Value |
| --- | --- |
| Environment extensions | 313 |
| Imported constant-map buckets | 2097152 |
| Imported constants | 485594 |
| Imported compacted-region bytes (not RSS) | 4658701624 |
| Imported compacted regions (Lean labels these modules) | 22609 |
| Memory-mapped compacted regions | 22522 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| tactic execution | 48.700 |
| typeclass inference | 5.100 |
| import | 4.520 |
| interpretation | 0.711 |
| type checking | 0.551 |
| elaboration | 0.480 |
| simp | 0.069 |
| process pre-definitions | 0.022 |
| initialization | 0.019 |
| share common exprs | 0.007 |
| linting | 0.006 |
| instantiate metavars | 0.004 |
| parsing | 0.004 |
| let-to-have transformation | 0.003 |
| congr simp thm | 0.001 |
| fix level params | 0.001 |
| attribute application | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 48.2s | 48.200 | 10 |
| import took 4.52s | 4.520 | 1 |
| elaboration took 235ms | 0.235 | 2 |
| typeclass inference took 138ms | 0.138 | 7 |
| typeclass inference took 131ms | 0.131 | 4 |
| typeclass inference took 129ms | 0.129 | 5 |
| typeclass inference took 127ms | 0.127 | 6 |
| typeclass inference of AddRightMono took 126ms | 0.126 | 11 |
| typeclass inference of InnerProductSpace took 109ms | 0.109 | 9 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 107ms | 0.107 | 8 |

Firefox CLI flags are omitted and the captured setup has no trace.profiler options for this timer/stats-only fallback. No Firefox rankings or per-declaration trace attribution are available; its process timings are not matched to Firefox-instrumented runs. This setup guard does not generally audit source-level option overrides.

Unattributed elaboration events above threshold: 2; no detailed Firefox attribution is available for this native fallback.

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/native-profile-guarded/Cloning.PhysicalFlatConverseReduction-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/native-profile-guarded/Cloning.PhysicalFlatConverseReduction-1.setup.json Cloning/PhysicalFlatConverseReduction.lean
```

- Firefox CLI flags are omitted and the captured setup has no trace.profiler options; source-level overrides are not generally audited.
- No Firefox rankings or per-declaration trace attribution are available for this timer/stats-only fallback.
- These timer/stats-only process timings are not matched to Firefox-instrumented runs.

### Cloning.TensorCartanChannelCovariance — repetition 1

Recorded profile commit: `3eb587e0f00748c3a9b63f9eeedc1646e4cb77be`; source SHA-256: `f9eb714670b6f2a467b262ef6641f7095912c24c601e6ea206e152aad342667c`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | 3eb587e0f00748c3a9b63f9eeedc1646e4cb77be |
| Source matches recorded profile commit | True |
| Source matches benchmark commit | True |
| Preserved profile source | Cloning.TensorCartanChannelCovariance-1.source.lean.txt |
| Configuration matches benchmark | True |
| Source/config/artifact/setup inputs stable | True |
| Measurement valid | True |
| Profile mode | firefox |
| Import context | continuation/Cloning.TensorCartanChannelCovariance-1.import-context.json |

Controlled profile environment: `{'LAKE_ARTIFACT_CACHE': 'false', 'LEAN_NUM_THREADS': '2'}`. The raw metadata records selected effective environment and import paths.

| Configuration input | SHA-256 |
| --- | --- |
| formalization/lake-manifest.json | e4630915680b82b58c6a005e1ba1e515e865e5541c7e665d4a2d57f783eeadb4 |
| formalization/lakefile.toml | ddeb0d2c8217676fc393afd24c13629993c580f35f9d8ad15240c6a167b020c1 |
| formalization/lean-toolchain | dc6d65016fad3123d44bf17b5bf0598286284ab16ba75d5c17eb22ed11f47361 |

| Lean environment statistic | Value |
| --- | --- |
| Environment extensions | 313 |
| Imported constant-map buckets | 2097152 |
| Imported constants | 480941 |
| Imported compacted-region bytes (not RSS) | 4559161568 |
| Imported compacted regions (Lean labels these modules) | 22213 |
| Memory-mapped compacted regions | 22124 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| typeclass inference | 22.800 |
| interpretation | 16.300 |
| import | 12.400 |
| tactic execution | 10.300 |
| simp | 0.728 |
| elaboration | 0.660 |
| type checking | 0.434 |
| initialization | 0.019 |
| linting | 0.016 |
| instantiate metavars | 0.012 |
| process pre-definitions | 0.010 |
| share common exprs | 0.009 |
| congr simp thm | 0.008 |
| parsing | 0.003 |
| fix level params | 0.001 |
| let-to-have transformation | 0.001 |
| attribute application | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| import took 12.4s | 12.400 | 1 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 9.34s | 9.340 | 77 |
| interpretation of Lean.Elab.Tactic._aux_Mathlib_Tactic_Widget_Calc___elabRules_Lean_calcTactic_1._boxed took 2.3s | 2.300 | 112 |
| simp took 658ms | 0.658 | 42 |
| elaboration took 412ms | 0.412 | 55 |
| typeclass inference of CoeFun took 264ms | 0.264 | 47 |
| typeclass inference of CoeFun took 240ms | 0.240 | 54 |
| type checking took 240ms | 0.240 | 113 |
| tactic execution of Lean.Parser.Tactic.exact took 207ms | 0.207 | 78 |
| typeclass inference of HSMul took 202ms | 0.202 | 93 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 38.497 | 46.234 | unattributed |
| Elab.step: Lean.Parser.Tactic.rewriteSeq: rewrite [show partitionTensorAction mu hmu Uᴴ = (partitionTensorAction mu hmu U).adjoint from     cyclicTensorOperator_star _ _ _ _ U,   cartanProductAction_star] at h | 8.787 | 9.826 | unattributed |
| Meta.isDefEq.delta: ✅️ if hp : 2 = 0 then   Eq.ndrec (motive := fun {p} => ↥(lp (fun x => ℂ) p) → ℝ) (fun f => ↑⋯.toFinset.card) ⋯     (-(Cloning.TensorLie.cyclicSector                 (Cloning.TensorLie.partitionHighestTensor (fun i => mu i + nu i) ⋯)).subtype.toAddMonoidHom           x +       (Cl | 2.910 | 2.910 | unattributed |
| Meta.isDefEq: ✅️ { toAdd := ContinuousLinearMap.add, add_assoc := ⋯, toZero := ContinuousLinearMap.zero, zero_add := ⋯, add_zero := ⋯,   nsmul := fun x1 x2 => x1 • x2, nsmul_zero := ⋯,   nsmul_succ :=     ⋯ } =?= { toAdd := ContinuousLinearMap.add, add_assoc := ⋯, toZero := ContinuousLinearMap.zero, | 2.776 | 6.097 | unattributed |
| Meta.isDefEq.delta: ✅️ x1✝ • x2✝ =?= x1✝ • x2✝ | 2.493 | 2.493 | unattributed |
| Meta.isDefEq.delta: ✅️ if hp : 2 = 0 then   Eq.ndrec (motive := fun {p} => ↥(lp (fun x => ℂ) p) → ℝ) (fun f => ↑⋯.toFinset.card) ⋯     (-(Cloning.TensorLie.cyclicSector (Cloning.TensorLie.partitionHighestTensor mu hmu)).subtype.toAddMonoidHom x +       (Cloning.TensorLie.cyclicSector (Cloning.Tensor | 1.899 | 1.912 | unattributed |
| Meta.isDefEq.delta: ✅️ if hp : 2 = 0 then   Eq.ndrec (motive := fun {p} => ↥(lp (fun x => ℂ) p) → ℝ) (fun f => ↑⋯.toFinset.card) ⋯     (-(Cloning.TensorLie.tensorProductSector                 (Cloning.TensorLie.cyclicSector (Cloning.TensorLie.partitionHighestTensor mu hmu))                 (Cloning. | 1.869 | 1.869 | unattributed |
| Meta.check: ✅️ LinearIsometryEquiv.instCoeFun | 1.793 | 6.440 | unattributed |
| Meta.isDefEq: ✅️ fun x1 x2 => x1 • x2 =?= fun x1 x2 => x1 • x2 | 0.682 | 3.321 | unattributed |
| Meta.isDefEq: ✅️ {   toNorm :=     (Cloning.TensorLie.cyclicSector           (Cloning.TensorLie.partitionHighestTensor (fun i => mu i + nu i) ⋯)).normedAddCommGroup.toNorm,   toAddCommGroup :=     (Cloning.TensorLie.cyclicSector           (Cloning.TensorLie.partitionHighestTensor (fun i => mu i + nu | 0.463 | 3.496 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 38.497 | 46.234 | unattributed |
| Elab.async: elaborating proof of Cloning.TensorLie.physicalCartanChannel_covariant | 0.018 | 25.087 | unattributed |
| Elab.definition.value: Cloning.TensorLie.physicalCartanChannel_covariant | 0.006 | 25.069 | Cloning.TensorLie.physicalCartanChannel_covariant at formalization/Cloning/TensorCartanChannelCovariance.lean:43 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   let V := (cartanInclusion mu nu hmu hnu).toContinuousLinearMap   let W := cartanProductAction mu nu hmu hnu U   let S := partitionTensorAction (fun i ↦ mu i + nu i) (sumPartition_antitone mu nu hmu hnu) U   let T := cartanProductOperator mu nu hmu hnu A.1   | 0.000 | 25.053 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   let V := (cartanInclusion mu nu hmu hnu).toContinuousLinearMap   let W := cartanProductAction mu nu hmu hnu U   let S := partitionTensorAction (fun i ↦ mu i + nu i) (sumPartition_antitone mu nu hmu hnu) U   let T := cartanProductOperator mu nu hmu  | 0.011 | 25.053 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticHave__: have hprod :   cartanProductOperator mu nu hmu hnu (operatorConjugation (partitionTensorAction mu hmu U) A.1) =     W.comp (T.comp W.adjoint) :=   by   have h := cartanProductOperator_conjugate mu nu hmu hnu U hU A.1   rw [show partitionTensorAction mu hmu | 0.002 | 11.397 | unattributed |
| Elab.step: Lean.Parser.Tactic.focus: focus   refine     no_implicit_lambda%       (have hprod :         cartanProductOperator mu nu hmu hnu (operatorConjugation (partitionTensorAction mu hmu U) A.1) =           W.comp (T.comp W.adjoint) :=         ?body✝;       ?_)   case body✝ =>     with_annotate_ | 0.000 | 11.395 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   refine     no_implicit_lambda%       (have hprod :         cartanProductOperator mu nu hmu hnu (operatorConjugation (partitionTensorAction mu hmu U) A.1) =           W.comp (T.comp W.adjoint) :=         ?body✝;       ?_)   case body✝ =>     with_annotate_st | 0.000 | 11.395 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   refine     no_implicit_lambda%       (have hprod :         cartanProductOperator mu nu hmu hnu (operatorConjugation (partitionTensorAction mu hmu U) A.1) =           W.comp (T.comp W.adjoint) :=         ?body✝;       ?_)   case body✝ =>     with_an | 0.000 | 11.395 | unattributed |
| Elab.step: Lean.Parser.Tactic.case: case body✝ =>   with_annotate_state"by"     ( have h := cartanProductOperator_conjugate mu nu hmu hnu U hU A.1       rw [show partitionTensorAction mu hmu Uᴴ = (partitionTensorAction mu hmu U).adjoint from           cyclicTensorOperator_star _ _ _ _ U,         car | 0.007 | 10.051 | unattributed |

Unattributed elaboration events above threshold: 2; the detailed trace rankings supply attribution where their labels identify declarations.

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after-continuation/Cloning.TensorCartanChannelCovariance-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after-continuation/Cloning.TensorCartanChannelCovariance-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after-continuation/Cloning.TensorCartanChannelCovariance-1.setup.json Cloning/TensorCartanChannelCovariance.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.TensorCartanStateOperator — repetition 1

Recorded profile commit: `3eb587e0f00748c3a9b63f9eeedc1646e4cb77be`; source SHA-256: `3ae1e4805c1a3809235778d3abc8d7a650d6c58b543cb15e94e70d49be870def`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | 3eb587e0f00748c3a9b63f9eeedc1646e4cb77be |
| Source matches recorded profile commit | True |
| Source matches benchmark commit | True |
| Preserved profile source | Cloning.TensorCartanStateOperator-1.source.lean.txt |
| Configuration matches benchmark | True |
| Source/config/artifact/setup inputs stable | True |
| Measurement valid | True |
| Profile mode | firefox |
| Import context | continuation/Cloning.TensorCartanStateOperator-1.import-context.json |

Controlled profile environment: `{'LAKE_ARTIFACT_CACHE': 'false', 'LEAN_NUM_THREADS': '2'}`. The raw metadata records selected effective environment and import paths.

| Configuration input | SHA-256 |
| --- | --- |
| formalization/lake-manifest.json | e4630915680b82b58c6a005e1ba1e515e865e5541c7e665d4a2d57f783eeadb4 |
| formalization/lakefile.toml | ddeb0d2c8217676fc393afd24c13629993c580f35f9d8ad15240c6a167b020c1 |
| formalization/lean-toolchain | dc6d65016fad3123d44bf17b5bf0598286284ab16ba75d5c17eb22ed11f47361 |

| Lean environment statistic | Value |
| --- | --- |
| Environment extensions | 313 |
| Imported constant-map buckets | 2097152 |
| Imported constants | 480896 |
| Imported compacted-region bytes (not RSS) | 4557056304 |
| Imported compacted regions (Lean labels these modules) | 22207 |
| Memory-mapped compacted regions | 22121 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| typeclass inference | 12.100 |
| tactic execution | 12.000 |
| interpretation | 8.620 |
| import | 5.540 |
| elaboration | 0.481 |
| type checking | 0.331 |
| simp | 0.243 |
| let-to-have transformation | 0.063 |
| initialization | 0.019 |
| process pre-definitions | 0.016 |
| share common exprs | 0.010 |
| linting | 0.008 |
| instantiate metavars | 0.008 |
| congr simp thm | 0.005 |
| parsing | 0.005 |
| fix level params | 0.002 |
| attribute application | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 9.54s | 9.540 | 53 |
| import took 5.54s | 5.540 | 1 |
| tactic execution of Lean.Parser.Tactic.exact took 537ms | 0.537 | 67 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 406ms | 0.406 | 15 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 255ms | 0.255 | 13 |
| tactic execution of Lean.Parser.Tactic.change took 246ms | 0.246 | 59 |
| typeclass inference of CoeFun took 244ms | 0.244 | 56 |
| elaboration took 242ms | 0.242 | 49 |
| typeclass inference of CoeFun took 239ms | 0.239 | 40 |
| typeclass inference of HSMul took 201ms | 0.201 | 48 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 19.661 | 25.300 | unattributed |
| Elab.step: Lean.Parser.Tactic.rewriteSeq: rewrite [hA, partitionMatrixOperator_eq_matrixLift] at hc | 8.397 | 9.540 | unattributed |
| Meta.isDefEq.delta: ✅️ if hp : 2 = 0 then   Eq.ndrec (motive := fun {p} => ↥(lp (fun x => ℂ) p) → ℝ) (fun f => ↑⋯.toFinset.card) ⋯     (-(Cloning.TensorLie.cyclicSector (Cloning.TensorLie.partitionHighestTensor mu hmu)).subtype.toAddMonoidHom x +       (Cloning.TensorLie.cyclicSector (Cloning.Tensor | 3.305 | 4.159 | unattributed |
| Meta.isDefEq.delta: ✅️ if hp : 2 = 0 then   Eq.ndrec (motive := fun {p} => ↥(lp (fun x => ℂ) p) → ℝ) (fun f => ↑⋯.toFinset.card) ⋯     (-(Cloning.TensorLie.cyclicSector                 (Cloning.TensorLie.partitionHighestTensor (fun i => mu i + nu i) ⋯)).subtype.toAddMonoidHom           x +       (Cl | 1.190 | 1.190 | unattributed |
| Meta.isDefEq.delta: ✅️ if 2 = ⊤ then   ⨆ i,     ‖↑(-(Cloning.TensorLie.cyclicSector (Cloning.TensorLie.partitionHighestTensor mu hmu)).subtype.toAddMonoidHom x +             (Cloning.TensorLie.cyclicSector (Cloning.TensorLie.partitionHighestTensor mu hmu)).subtype.toAddMonoidHom y)         i‖ else   | 0.822 | 0.822 | unattributed |
| Meta.isDefEq: ✅️ {   toNorm :=     (Cloning.TensorLie.cyclicSector (Cloning.TensorLie.partitionHighestTensor mu hmu)).normedAddCommGroup.toNorm,   toAddCommGroup :=     (Cloning.TensorLie.cyclicSector           (Cloning.TensorLie.partitionHighestTensor mu hmu)).normedAddCommGroup.toAddCommGroup,   t | 0.744 | 5.110 | unattributed |
| Meta.isDefEq: ✅️ { toAdd := ContinuousLinearMap.add, add_assoc := ⋯, toZero := ContinuousLinearMap.zero, zero_add := ⋯, add_zero := ⋯,   nsmul := fun x1 x2 => x1 • x2, nsmul_zero := ⋯,   nsmul_succ :=     ⋯ } =?= { toAdd := ContinuousLinearMap.add, add_assoc := ⋯, toZero := ContinuousLinearMap.zero, | 0.530 | 1.138 | unattributed |
| Meta.isDefEq.delta: ✅️ if hp : 2 = 0 then   Eq.ndrec (motive := fun {p} => ↥(lp (fun x => ℂ) p) → ℝ) (fun f => ↑⋯.toFinset.card) ⋯     (-(Cloning.TensorLie.cyclicSector                 (Cloning.TensorLie.partitionHighestTensor (fun i => mu i + nu i) ⋯)).subtype.toAddMonoidHom           x +       (Cl | 0.521 | 0.521 | unattributed |
| Meta.isDefEq.delta: ✅️ x1✝ • x2✝ =?= x1✝ • x2✝ | 0.462 | 0.474 | unattributed |
| Meta.isDefEq.delta: ✅️ if hp : 2 = 0 then   Eq.ndrec (motive := fun {p} => ↥(lp (fun x => ℂ) p) → ℝ) (fun f => ↑⋯.toFinset.card) ⋯     (-(Cloning.TensorLie.tensorProductSector                 (Cloning.TensorLie.cyclicSector (Cloning.TensorLie.partitionHighestTensor mu hmu))                 (Cloning. | 0.449 | 0.491 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 19.661 | 25.300 | unattributed |
| Elab.async: elaborating proof of Cloning.TensorLie.physicalCartanChannel_operator | 0.013 | 13.423 | unattributed |
| Elab.definition.value: Cloning.TensorLie.physicalCartanChannel_operator | 0.020 | 13.411 | Cloning.TensorLie.physicalCartanChannel_operator at formalization/Cloning/TensorCartanStateOperator.lean:100 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   let M := matrixOf (partitionBasis mu hmu) A.1   have hA : partitionMatrixOperator mu hmu M = A := partitionMatrixOperator_matrixOf _ _ A   have hc := congrArg Subtype.val (physicalCartanChannel_partitionMatrixOperator mu nu hmu hnu M)   rw [hA, partitionMat | 0.000 | 13.390 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   let M := matrixOf (partitionBasis mu hmu) A.1   have hA : partitionMatrixOperator mu hmu M = A := partitionMatrixOperator_matrixOf _ _ A   have hc := congrArg Subtype.val (physicalCartanChannel_partitionMatrixOperator mu nu hmu hnu M)   rw [hA, par | 0.003 | 13.390 | unattributed |
| Elab.step: Lean.Parser.Tactic.rwSeq: rw [hA, partitionMatrixOperator_eq_matrixLift] at hc | 0.003 | 9.547 | unattributed |
| Elab.step: Lean.Parser.Tactic.paren: (rewrite [hA, partitionMatrixOperator_eq_matrixLift] at hc; with_annotate_state"]" (try (with_reducible rfl))) | 0.000 | 9.544 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq: rewrite [hA, partitionMatrixOperator_eq_matrixLift] at hc; with_annotate_state"]" (try (with_reducible rfl)) | 0.000 | 9.544 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented: rewrite [hA, partitionMatrixOperator_eq_matrixLift] at hc; with_annotate_state"]" (try (with_reducible rfl)) | 0.004 | 9.544 | unattributed |
| Elab.step: Lean.Parser.Tactic.rewriteSeq: rewrite [hA, partitionMatrixOperator_eq_matrixLift] at hc | 8.397 | 9.540 | unattributed |

Unattributed elaboration events above threshold: 1; the detailed trace rankings supply attribution where their labels identify declarations.

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after-continuation/Cloning.TensorCartanStateOperator-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after-continuation/Cloning.TensorCartanStateOperator-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-after-continuation/Cloning.TensorCartanStateOperator-1.setup.json Cloning/TensorCartanStateOperator.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.PhysicalFlatPinchingInflation — repetition 1

Recorded profile commit: `3eb587e0f00748c3a9b63f9eeedc1646e4cb77be`; source SHA-256: `ec819ddc2ab205994ecc7801f948b9af02e042e5a79928b0d04a9ea16dc786b4`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | 3eb587e0f00748c3a9b63f9eeedc1646e4cb77be |
| Source matches recorded profile commit | True |
| Source matches benchmark commit | True |
| Preserved profile source | Cloning.PhysicalFlatPinchingInflation-1.source.lean.txt |
| Configuration matches benchmark | True |
| Source/config/artifact/setup inputs stable | True |
| Measurement valid | True |
| Profile mode | native |
| Import context | native-guarded/Cloning.PhysicalFlatPinchingInflation-1.import-context.json |

Controlled profile environment: `{'LAKE_ARTIFACT_CACHE': 'false', 'LEAN_NUM_THREADS': '2'}`. The raw metadata records selected effective environment and import paths.

| Configuration input | SHA-256 |
| --- | --- |
| formalization/lake-manifest.json | e4630915680b82b58c6a005e1ba1e515e865e5541c7e665d4a2d57f783eeadb4 |
| formalization/lakefile.toml | ddeb0d2c8217676fc393afd24c13629993c580f35f9d8ad15240c6a167b020c1 |
| formalization/lean-toolchain | dc6d65016fad3123d44bf17b5bf0598286284ab16ba75d5c17eb22ed11f47361 |

| Lean environment statistic | Value |
| --- | --- |
| Environment extensions | 313 |
| Imported constant-map buckets | 2097152 |
| Imported constants | 485459 |
| Imported compacted-region bytes (not RSS) | 4655907904 |
| Imported compacted regions (Lean labels these modules) | 22598 |
| Memory-mapped compacted regions | 22508 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| tactic execution | 22.800 |
| typeclass inference | 14.300 |
| import | 5.250 |
| interpretation | 0.717 |
| type checking | 0.443 |
| elaboration | 0.259 |
| simp | 0.123 |
| initialization | 0.019 |
| process pre-definitions | 0.012 |
| linting | 0.011 |
| share common exprs | 0.006 |
| congr simp thm | 0.004 |
| parsing | 0.004 |
| instantiate metavars | 0.003 |
| let-to-have transformation | 0.002 |
| fix level params | 0.001 |
| attribute application | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| tactic execution of Lean.Parser.Tactic.change took 20.9s | 20.900 | 2 |
| import took 5.25s | 5.250 | 1 |
| typeclass inference of NormedSpace took 4.84s | 4.840 | 28 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 746ms | 0.746 | 25 |
| typeclass inference of AddRightMono took 602ms | 0.602 | 32 |
| tactic execution of Lean.Parser.Tactic.simpa took 200ms | 0.200 | 35 |
| tactic execution of Lean.Parser.Tactic.exact took 198ms | 0.198 | 23 |
| tactic execution of Lean.Parser.Tactic.exact took 166ms | 0.166 | 4 |
| typeclass inference of AddLeftMono took 154ms | 0.154 | 3 |
| type checking took 144ms | 0.144 | 36 |

Firefox CLI flags are omitted and the captured setup has no trace.profiler options for this timer/stats-only fallback. No Firefox rankings or per-declaration trace attribution are available; its process timings are not matched to Firefox-instrumented runs. This setup guard does not generally audit source-level option overrides.

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/native-profile-guarded/Cloning.PhysicalFlatPinchingInflation-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/native-profile-guarded/Cloning.PhysicalFlatPinchingInflation-1.setup.json Cloning/PhysicalFlatPinchingInflation.lean
```

- Firefox CLI flags are omitted and the captured setup has no trace.profiler options; source-level overrides are not generally audited.
- No Firefox rankings or per-declaration trace attribution are available for this timer/stats-only fallback.
- These timer/stats-only process timings are not matched to Firefox-instrumented runs.

### Diagnostic profiling attempts

These attempts are preserved separately and excluded from completed-profile coverage and comparisons. The full cold build result is independent of a diagnostic instrumentation failure.

| Module | Role | Exit | Reason | Original receipt |
| --- | --- | --- | --- | --- |
| Cloning.PhysicalFlatConverseReduction | failed-profile-attempt | 1 | Untouched module passed the full cold build, but Firefox trace collection hit its existing typeclass and elaboration heartbeat limits. No Firefox export occurred after errors. Excluded from successful cohort. | profiles-attempt-1.json #11 |
| Cloning.PhysicalFlatPinchingInflation | failed-profile-attempt | 1 | Untouched module passed the full cold build, but Firefox trace collection hit its existing typeclass heartbeat limit. No Firefox export occurred after errors. Excluded from successful cohort. | continuation/profiles.json #2 |
| Cloning.PhysicalFlatConverseReduction | diagnostic-native-control | 0 | Exploratory native-only control passed, but setup/trace unchanged flags were inherited from the failed record, not remeasured by this driver. Excluded from canonical cohort; the fresh guarded native run is canonical. | native-exploratory/profiles.json #0 |

## 8. Findings ranked by actionability

Two measured proof-body conversions were accepted. The dead-code sweep occurred before the baseline, so its private-helper removal is not credited as an elaboration improvement. The two cleanup commits are `f66714d5f0b21c248696d833f35f86f364ae413a` (Weyl) and `babccc31fa77c515aa9b7079501bd374835206ca` (Werner). The complete after snapshot measures proof/configuration state `3eb587e0f00748c3a9b63f9eeedc1646e4cb77be`.

### Repeated compiler controls

| Proof conversion | Bare wall A → B | Bare wall reduction | Native CPU A → B | Native CPU reduction | Traced tactic A → B |
| --- | ---: | ---: | ---: | ---: | ---: |
| Weyl projector equality | 106.89 → 6.62 s | 93.81% | 110.05 → 9.62 s | 91.26% | 106.00 → 1.48 s |
| Werner trace equality | 39.54 → 6.74 s | 82.95% | 43.14 → 8.88 s | 79.42% | 38.80 → 2.46 s |

These are medians of three alternating A/B pairs in each mode, with 12 successful runs per intervention and 24 in total. Native CPU is per-run GNU user plus system CPU before taking the median. Bare runs omit profiling, trace and statistics flags. The profile controls use pp=false identically in both arms; their tactic totals are exclusive elapsed timers. Repository before/after warm profiles use pp=true. The two experiments measure local compiler improvements, not an additive prediction of the full cold-build change. Neither bare experiment reproduced a maximum-process RSS decrease, so no memory gain is claimed.

### Exact changes and preservation

Weyl's `integral_weighted_characteristic` now explicitly rewrites `vectorProjector x = rankOneOperator x x` before the costly conversion under `tracePairing`. The original named trace event spent 103 s in that conversion; the explicit equality avoids the deep definitional comparison.

Werner's `wernerOutput_trace_one` replaces `change ... at htp` with a chain using `traceCLM_apply`, the channel's trace-preservation equality, and `traceCLM_apply(...).symm`. The original named conversion took 36.7 s. The replacement establishes the same local equality with existing lemmas.

The source/API guard covers all 994 owned source files. The other 992 files are byte-identical to the post-dead-sweep baseline; the two changed files are byte-identical outside the selected theorem bodies. Names, statements, hypotheses, namespaces, imports, attributes, options and variables stay the same. All 316 result-index checks and the three toolchain/Lake configuration files remain byte-identical. The raw guard's current_commit is the historical f66714d context with the accepted Werner working-source variant present; it is not labeled as the final after commit. The preserved candidate hashes and measured before/after manifests bind the exact variants. This is a source/API receipt, not an independent whole-library type-exporter comparison.

Each ignored body-only sorry diagnostic sharply reduced the relevant tactic phase, identifying proof cost before changing implementation. Those two diagnostic executions are excluded from the 24 valid A/B runs and from accepted source. The accepted variants have complete proofs. Full builds and public result checks are separate from source-bound axiom and independent-checker evidence; the elaboration measurements do not replace fresh final verification.

### Coverage and remaining measured leads

The before warm-profile census covers exactly ten files: the cold top five plus five targeted files. Seven are among the cold top 30. The matched after queue preserves those ten and adds any newly appearing cold top-five modules. Compilation covers all 994 own modules; that broader build coverage is distinct from warm-profile coverage. The remaining 23 cold top-30 leaders did not receive before warm profiles, and this pass does not diagnose every theorem.

PCTHybridMixtureFactor has mixed elaboration/typeclass costs, three anonymous elaboration events, and unresolved measure-metavariable comparisons. PCTGlobalPhysical mixes import, interpretation and anonymous elaboration; interpretation does not identify an arithmetic closer. PCTUnitaryTransportChannels is import-dominated with small local proof phases. InfiniteTraceClass has diffuse typeclass costs but no demonstrated closed-search cache target. Each requires its own focused attribution and controlled intervention before an edit is justified.

Thermal, AmplifierWeylThermal, PCTClosedForm and ComparisonMonotone remain below the full 5 s phase routing floor in these warm runs. ComparisonMonotone has bounded one-second arithmetic candidates; static Main-leaf and modern-module analyses identify possible import experiments. Neither earned measured cleanup credit. The recorded simp/dsimp and congr events do not justify a broad tactic sweep. No cache, heartbeat change, import split, header migration, or arithmetic rollout was accepted.

### Instrumentation-sensitive extra profiles

All ten matched after Firefox profiles passed. Two newly selected after cold-top-five modules encountered heartbeat failures in extra Firefox-traced attempts: PhysicalFlatConverseReduction at the existing typeclass/normalization limits (62.36 s failed wrapper wall), and PhysicalFlatPinchingInflation at the existing typeclass limit of 200,000 (30.74 s failed wrapper wall). Both records have exit 1, measurement_valid=false and stable source/configuration/setup/import inputs. Failed wall times describe failed diagnostics and are excluded from successful timing comparisons.

The preserved preliminary native PhysicalFlatConverseReduction control exited 0 (GNU wall 60.56 s, CPU 59.06 s; wrapper wall 60.61 s). It is explicitly exploratory: the first driver inherited setup/trace guard fields rather than measuring them anew. It is excluded from canonical successful coverage. The fully guarded native repeats both passed with source/configuration/setup/build-trace/import guards measured anew. They ran profile/statistics without Firefox trace flags or source/heartbeat changes:

| Unmatched native module | GNU wall | Native user+system CPU | Maximum-process RSS |
| --- | ---: | ---: | ---: |
| PhysicalFlatConverseReduction | 59.14 s | 58.99 s | 3,250,112 KiB |
| PhysicalFlatPinchingInflation | 30.14 s | 42.00 s | 3,275,648 KiB |

Canonical after coverage contains 15 successful own-file diagnostics: the ten matched Firefox files plus five new cold-top-five files (three Firefox, two native). The native entries have no before warm counterpart, no Firefox rankings or trace pointers, and do not enter the ten-file matched table or the 24 accepted A/B runs. The two failed trace attempts and preliminary control retain their exact original index SHA/position bindings separately from the canonical cohort.

The pinned Lean source shows that heartbeat budgets count current-thread small allocations, and enabled tracing performs extra allocation/bookkeeping inside elaboration. This supplies a plausible instrumentation-sensitive mechanism; the exact allocation/search trigger is unmeasured. The logged failures precede Firefox export, so post-elaboration pp=true export does not explain them. No proof options, source or heartbeat budgets were changed to obtain these diagnostic records.

### Timing and compatibility limits

The cold snapshots recorded GNU wall 12,316 → 4,030 s and native user-plus-system CPU 13,569.99 → 8,791.40 s. Maximum-process RSS was 3,396,256 → 3,416,144 KiB; no whole-build RSS improvement is observed. Both runs compiled 994 owned modules with 499 whole-log warnings, zero errors/sorry messages and no upstream compilation. These differences are observations on a shared host. CPU utilization changed from GNU-reported 110% to 218% (CPU/wall 1.10 → 2.18), exposing a substantial scheduling/load difference. Matching pins, source/config manifests, environment and timing-tool versions does not ensure identical contemporaneous load; other projects were active. Use the repeated bare controls for causal local improvement claims. Do not assign an entire full-build wall/CPU change to these two edits.

With pp=true, process wall/native CPU and cumulative interpretation totals may include trace formatting/export. C++ and Firefox intervals are elapsed measurements, with overlapping threads and inclusive frames; they are not OS CPU samples. Rounded Lake Built durations are elapsed estimates rather than per-file CPU. Maximum GNU RSS is a maximum process peak rather than simultaneous memory summed across compiler workers. Weighted import-chain and CPU/core references describe scheduling models, not verified intrinsic wall-time bounds. GNU page-fault/swap fields and swap-space use are retained as observations without inferring active swapping from space use alone.

The project keeps its legacy module-header mode. The missing-modern-header census is explicitly disclosed as a compatibility adaptation of the skill; no unmeasured export/API migration was forced. The baseline source/config match is a separately labeled supplemental post-build comparison, whereas the after runner performs its built-in end check. Warning counts cover the entire log and may include cached upstream messages. Dependency guards check path/size/mtime metadata rather than all artifact content hashes.

Report filename dates identify the 6 October Pacific-time campaign; the after run starts on 7 October UTC. Exact UTC windows in the evidence are authoritative. Historical Comparator/Nanoda/axiom certificates remain immutable and separate from the elaboration measurements; fresh final verification is source-bound in its own records.

## 9. What is not established

Logged job durations do not establish per-file CPU, exclusive elaboration cost, or a cleanup speedup. The global process inventory does not establish contention causality. Peak process RSS does not establish aggregate memory demand. The weighted import chain and CPU/core references are scheduling models, not measured critical-path bounds. Missing profiles leave tail causes unclassified; large unattributed elaboration requires detailed trace attribution. The legacy module-header exception is an explicit adaptation, not satisfaction of the skill's zero-header-deficit rule. Successful elaboration does not by itself refresh the independent comparator/nanoda certificates or their historical pins.

## 10. Methodology

Recorded timed command (working directory: `formalization`):

```sh
LAKE_ARTIFACT_CACHE=false LEAN_NUM_THREADS=2 /opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/after/resources.txt /Users/jw/.elan/bin/lake --no-ansi --no-cache build All
```

The project-only wrapper records the commit, rejects uncommitted owned proof/config changes, archives source sizes, guards dependency artifacts, invalidates only exact owned module artifacts, and records process samples. For a repeat, choose a fresh output directory:

```sh
python3 scripts/benchmark_elaboration.py --output .verify-work/elaboration-campaign/NEW_MEASUREMENT --threads 2 --size-helper formalization/verification/elaboration/2026-10-06/skills/count_lean_lines.py --time gtime
```

Recorded Lake artifact-cache setting: `false`; upstream oleans remain inputs. Record the same host, GNU-time version, and thread setting. Profile serially after the build, then summarize the raw text/trace files before rendering this report.

```sh
python3 scripts/report_elaboration.py --benchmark BENCHMARK_DIRECTORY --profiles PROFILE_SUMMARY_DIRECTORY --prior PRIOR_BENCHMARK_DIRECTORY --output REPORT.md
```

## 11. Pointers

Measurement directory: [formalization/verification/elaboration/2026-10-06/after](formalization/verification/elaboration/2026-10-06/after). Prior benchmark: [formalization/verification/elaboration/2026-10-06/before](formalization/verification/elaboration/2026-10-06/before) at `cbb2fd2007ae367e201d4a6ac7c069899db90dbd`; role: prior measurement for trend comparison.

| Evidence file | SHA-256 |
| --- | --- |
| [summary.json](formalization/verification/elaboration/2026-10-06/after/summary.json) | c24bc7e66a0c8bf57623b7bd20284f1b6d47f5a8a478fe6b1d05451fc4e3ae9c |
| [size.json](formalization/verification/elaboration/2026-10-06/after/size.json) | 3aedea570e14277db4fb648568f802c588aac232f8c346d34de7a955026541f2 |
| [imports.json](formalization/verification/elaboration/2026-10-06/after/imports.json) | f70c604535acac8784947f57a609d73878dae14b050c4c5c51524877930812d0 |
| [skill-size.txt](formalization/verification/elaboration/2026-10-06/after/skill-size.txt) | 1e1d48e98fb058c0fde735b9c40d41ad2c8f5f6e5b237239ee9c349de3833438 |
| [build.log](formalization/verification/elaboration/2026-10-06/after/build.log) | 703d4989a69213947c2431e1714d976675bb96077e53c2d93d89d6ac7c2dd7b0 |
| [resources.txt](formalization/verification/elaboration/2026-10-06/after/resources.txt) | c91740dc4627096ec7c67afa592f66fe55d82e649364d9d720dcc341c4de559d |
| [process-inventory.json](formalization/verification/elaboration/2026-10-06/after/process-inventory.json) | 7eb8c19ae4dad25c386d42320b0208994016b015687f015454d2a296b598fa3c |
| [dependencies-before.json](formalization/verification/elaboration/2026-10-06/after/dependencies-before.json) | 07231494c7ecd316c52ccba38d8e1641671b844bfbb3f5a5f3a53dd61ec64c32 |
| [dependencies-after.json](formalization/verification/elaboration/2026-10-06/after/dependencies-after.json) | 07231494c7ecd316c52ccba38d8e1641671b844bfbb3f5a5f3a53dd61ec64c32 |
| [invalidated.json](formalization/verification/elaboration/2026-10-06/after/invalidated.json) | d9cc84aabdfaad31314f03b04720b29f5d8adc0d4d60ef9436aaea29d00545d3 |
| [source-config-hashes.json](formalization/verification/elaboration/2026-10-06/after/source-config-hashes.json) | 79e92cce1a039342af451b751e74f232c814e4a5d4c84b23b97ec502a05abe41 |
| [benchmark-runner.py](formalization/verification/elaboration/2026-10-06/after/benchmark-runner.py) | fc202556ed4ee2a3e7366a00180502515f16ef644484e6463ea8ed2c4e579417 |
| process-samples.json (omitted original; counts published separately) | cd661cfdaa3d5939c31a6005206a399de3621ae4d9fe2bc77c14d611bce94d70 |

Profile summary: [formalization/verification/elaboration/2026-10-06/profiles-after/summary.json](formalization/verification/elaboration/2026-10-06/profiles-after/summary.json); SHA-256: `7e7eb59295c2969da2ea0655064bce12cc9dba0a95dcfc11c8c55443e2b3667d`. Its per-profile input hashes bind the raw text and trace evidence.
