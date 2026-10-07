# Cloning elaboration report — 2026-10-06

## 1. Setup/provenance

UTC window: `2026-10-06T22:44:14.173734+00:00` → `2026-10-07T02:09:30.814062+00:00`. Measured Git commit: `cbb2fd2007ae367e201d4a6ac7c069899db90dbd`. Target: `All`.

Host: `Darwin Mac.attlocal.net 27.2.0 Darwin Kernel Version 27.2.0: Tue Sep 29 21:45:37 PDT 2026; root:xnu-13432.40.177.0.3~56/RELEASE_ARM64_T8112 arm64`; logical CPUs: 8; memory bytes: 17179869184.

Lean: `Lean (version 4.29.0-rc6, arm64-apple-darwin24.6.0, commit 00659f8e6071d7e46131ed643bf8003b99b044e9, Release)`. Lake: `Lake version 5.0.0-src+00659f8 (Lean version 4.29.0-rc6)`. GNU time: `time (GNU Time) 1.10`. Environment: `{'LAKE_ARTIFACT_CACHE': 'false', 'LEAN_NUM_THREADS': '2'}`.

Workflow: [lean-elaboration-test](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/70bb859295edc2abb9ad81f8f6e31ab2adf8ca07/skills/lean-elaboration-test/SKILL.md) and [lean-elaboration](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/70bb859295edc2abb9ad81f8f6e31ab2adf8ca07/skills/lean-elaboration/SKILL.md), pinned at `70bb859295edc2abb9ad81f8f6e31ab2adf8ca07`.

| Global process inventory | Observed |
| --- | --- |
| Samples | 1201 |
| Maximum total Lean/Lake lines | 22 |
| Maximum compiler lines with owned absolute .lean source | 2 |
| Maximum compiler lines with another absolute .lean source | 12 |
| Maximum lines with unresolved source/cwd | 9 |
| Samples containing another absolute .lean source | 665 |

The public inventory reports counts and omits unrelated paths and command lines. The raw inventory can include this run and concurrent projects. Absolute source paths support the limited attribution above; a Lake command alone does not disclose its cwd. Presence alone is informational; it neither invalidates the run nor establishes artifact mutation or causality. This report uses redacted count evidence; the original process samples are omitted from the public bundle.

No prior benchmark supplied; this report is a standalone measurement.

## 2. Size snapshot

| Metric | Measured | Prior | Δ |
| --- | --- | --- | --- |
| Owned .lean files | 994 | — | — |
| Total source lines | 111939 | — | — |
| Non-comment code lines | 92405 | — | — |
| Comment-only files excluded | 0 | — | — |
| Legacy files without module header | 994 | — | — |

Sizes and first declared namespaces come from `git archive` at the measured commit. The `All` import closure covers all 994 owned modules; actual compilation count is recorded below. The pinned skill prescribes zero files without a `module` header. This project deliberately adapts that strict requirement to its existing Lean file format; the nonzero legacy count is disclosed, and no module-format migration was performed.

## 3. Headline table

| Metric | Measured | Prior | Δ |
| --- | --- | --- | --- |
| GNU-time elapsed wall seconds | 12,316.00 | unavailable | — |
| Wrapper observed wall seconds | 12,316.51 | unavailable | — |
| GNU-time user CPU seconds | 9,052.61 | unavailable | — |
| GNU-time system CPU seconds | 4,517.38 | unavailable | — |
| GNU-time total CPU seconds | 13,569.99 | unavailable | — |
| Actual CPU / GNU wall | 1.10 | unavailable | — |
| Maximum process peak RSS (KiB) | 3,396,256.00 | unavailable | — |
| Logged elapsed job-duration sum seconds | 24,284.90 | unavailable | — |
| Logged duration sum / GNU wall | 1.97 | unavailable | — |
| Actual CPU ms / code line | 146.85 | unavailable | — |
| Logged elapsed ms / code line | 262.81 | unavailable | — |

| Metric | Measured | Prior |
| --- | --- | --- |
| GNU-time %CPU | 110% | — |
| Configured LEAN_NUM_THREADS | 2 | — |
| Lake total jobs (includes cached upstream jobs) | 4563 | — |
| Unique owned modules actually compiled | 994 | — |
| Owned timings visible | 994/994 (100.0%) | — |

Lake's displayed Built durations are rounded wall-time estimates of individual jobs, not measured CPU. Their sum and duration/wall ratio describe overlapping logged work; they must not be called cumulative CPU or actual CPU parallelism. GNU time supplies the separate CPU totals. Peak RSS is the maximum process peak reported by GNU time, not simultaneous memory summed across compiler workers. `LEAN_NUM_THREADS` records runtime configuration, not a measured cap on concurrent compiler processes.

Weighted owned import-chain estimate: 3,281.00 s across 76 modules. CPU/8 reference work floor: 1,696.25 s; CPU/2 nominal pool reference: 6,785.00 s. These references do not establish the actual scheduling bound. The chain uses rounded observed durations and misses untimed work; it is an estimate, not a verified wall-time lower bound.

`Cloning.InfiniteTraceClass → Cloning.InfiniteHilbertSchmidt → Cloning.InfiniteTraceClassBasis → Cloning.InfiniteTraceClassIdeal → Cloning.InfiniteTraceClassNormBounds → Cloning.InfiniteTraceClassSpace → Cloning.InfiniteTraceClassBanach → Cloning.InfiniteTraceClassAlgebra → Cloning.InfiniteTraceClassSeries → Cloning.InfinitePureStateContinuity → Cloning.SymmetricOccupation → Cloning.GeneralSymmetricOccupation → Cloning.GeneralSymmetricDimension → Cloning.WernerPhysicalOperator → Cloning.WernerPhysicalPullback → Cloning.GeneralCoherentCoordinates → Cloning.GeneralCoherentLimits → Cloning.GeneralCoherentChannels → Cloning.GeneralCoherentMixture → Cloning.PCTWernerMixture → Cloning.PCTPartialTrace → Cloning.PCTTensorFrame → Cloning.TensorLieGenerators → Cloning.TensorLieRelations → Cloning.TensorLieHighestWeight → Cloning.TensorLieFiltration → Cloning.TensorLieLeibniz → Cloning.TensorWedge → Cloning.TensorWedgeHighest → Cloning.TensorPartitionHighest → Cloning.TensorCyclicSector → Cloning.TensorCyclicSectorIrreducible → Cloning.TensorCyclicSectorOperators → Cloning.TensorCyclicSectorTensorPower → Cloning.TensorCyclicSectorTransvection → Cloning.TensorCyclicSectorCovariance → Cloning.TensorHighestExtractionBasic → Cloning.TensorHighestExtraction → Cloning.TensorSchurDecompositionData → Cloning.TensorSchurDecomposition → Cloning.TensorSchurDecompositionIsometry → Cloning.TensorSchurDecompositionTrace → Cloning.TensorSchurDecompositionPMF → Cloning.TensorSchurDecompositionMultiplicity → Cloning.TensorSchurDecompositionBounds → Cloning.TensorSchurDecompositionCasimir → Cloning.TensorSchurDecompositionCharacter → Cloning.TensorSchurDecompositionRadialTrace → Cloning.TensorSchurDecompositionRootSum → Cloning.TensorSchurDecompositionRadialEquation → Cloning.TensorSchurDecompositionCharacterSpectrum → Cloning.TensorSchurDecompositionWeylCharacter → Cloning.WeylCharacterDimensionPhysical → Cloning.TensorFlatProjectorLaw → Cloning.TensorFlatProjectorEmbedding → Cloning.TensorFlatProjectorNaturality → Cloning.TensorFlatProjectorSupport → Cloning.TensorFlatProjectorSector → Cloning.TensorFlatProjectorRestriction → Cloning.TensorFlatProjectorSectorSupport → Cloning.TensorFlatProjectorState → Cloning.TensorFlatProjectorMatrix → Cloning.TensorFlatProjectorCompression → Cloning.TensorFlatProjectorFidelity → Cloning.TensorFlatProjectorTraceClass → Cloning.TensorFlatProjectorGibbs → Cloning.TensorFlatProjectorGibbsState → Cloning.TensorFlatProjectorStateFidelity → Cloning.TensorFlatProjectorTransitionCovariance → Cloning.TensorFlatProjectorChannel → Cloning.TensorFlatProjectorAchievability → Cloning.TensorRankOneCoupling → Cloning.TensorRankOneTransition → Cloning.TensorRankOneGlobal → Cloning → All`

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
| Source/config byte stability | True (supplemental post-build check at 2026-10-07T02:09:43.779122+00:00; no runner end check recorded) |
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
| ≥10 s | 557 | — | — |
| ≥20 s | 357 | — | — |
| ≥30 s | 261 | — | — |
| ≥40 s | 193 | — | — |

| Rank | Module | Logged elapsed s | Code lines | Elapsed ms/line | Prior s | Δ s |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | Cloning.WeylIdlerUniqueness | 237.00 | 145 | 1,634.48 | unavailable | — |
| 2 | Cloning.PCTHybridMixtureFactor | 228.00 | 84 | 2,714.29 | unavailable | — |
| 3 | Cloning.WernerPhysicalPullback | 198.00 | 190 | 1,042.11 | unavailable | — |
| 4 | Cloning.PCTGlobalPhysical | 171.00 | 95 | 1,800.00 | unavailable | — |
| 5 | Cloning.PCTUnitaryTransportChannels | 171.00 | 81 | 2,111.11 | unavailable | — |
| 6 | Cloning.MatrixChannelTraceNorm | 169.00 | 46 | 3,673.91 | unavailable | — |
| 7 | Cloning.MatrixLiftedCPTP | 168.00 | 132 | 1,272.73 | unavailable | — |
| 8 | Cloning.InfiniteTraceClass | 158.00 | 371 | 425.88 | unavailable | — |
| 9 | Cloning.MatrixTransitionAchievability | 151.00 | 95 | 1,589.47 | unavailable | — |
| 10 | Cloning.MatrixLANTransfer | 150.00 | 90 | 1,666.67 | unavailable | — |
| 11 | Cloning.PCTJointGaussianReal | 144.00 | 102 | 1,411.76 | unavailable | — |
| 12 | Cloning.InfiniteTraceClassSpace | 140.00 | 127 | 1,102.36 | unavailable | — |
| 13 | Cloning.PCTJointGaussianWhitenedLaw | 133.00 | 68 | 1,955.88 | unavailable | — |
| 14 | Cloning.InfiniteTraceClassNormBounds | 130.00 | 320 | 406.25 | unavailable | — |
| 15 | Cloning.PCTGlobalMatrixBridge | 130.00 | 87 | 1,494.25 | unavailable | — |
| 16 | Cloning.InfiniteHilbertSchmidt | 127.00 | 432 | 293.98 | unavailable | — |
| 17 | Cloning.TensorFlatProjectorStateFidelity | 127.00 | 92 | 1,380.43 | unavailable | — |
| 18 | Cloning.MatrixLiftedCPTPAction | 126.00 | 65 | 1,938.46 | unavailable | — |
| 19 | Cloning.MatrixLiftedTrimming | 126.00 | 112 | 1,125.00 | unavailable | — |
| 20 | Cloning.TensorCyclicFiltration | 126.00 | 176 | 715.91 | unavailable | — |
| 21 | Cloning.PCTPhysicalFidelityLAN | 121.00 | 97 | 1,247.42 | unavailable | — |
| 22 | Cloning.MatrixTraceOrder | 119.00 | 53 | 2,245.28 | unavailable | — |
| 23 | Cloning.AmplifierWeylThermal | 118.00 | 101 | 1,168.32 | unavailable | — |
| 24 | Cloning.PCTGaussianOutputTangent | 114.00 | 102 | 1,117.65 | unavailable | — |
| 25 | Cloning.MatrixFidelityBounds | 111.00 | 89 | 1,247.19 | unavailable | — |
| 26 | Cloning.TensorSchurDecompositionIsometry | 111.00 | 118 | 940.68 | unavailable | — |
| 27 | Cloning.InfiniteTraceClassPolar | 107.00 | 172 | 622.09 | unavailable | — |
| 28 | Cloning.WernerPhysicalOperator | 105.00 | 123 | 853.66 | unavailable | — |
| 29 | Cloning.InfiniteTraceClassIdeal | 104.00 | 135 | 770.37 | unavailable | — |
| 30 | Cloning.PCTHybridFidelity | 104.00 | 69 | 1,507.25 | unavailable | — |

Threshold classification uses rounded displayed durations; a boundary file may lie on either side before rounding.

## 6. Per-namespace work

Each module is assigned once, to its first declared namespace in the measured Git source; facades without one are grouped at root. A module may later open other namespaces. This grouping aggregates rounded elapsed job durations, not CPU.

| First declared namespace | Modules | Code lines | Logged elapsed s | Prior s | Δ s |
| --- | --- | --- | --- | --- | --- |
| Cloning.TensorLie | 187 | 16624 | 4,615.10 | unavailable | — |
| Cloning.InfiniteTraceClass | 54 | 5719 | 2,356.20 | unavailable | — |
| Cloning.Hybrid | 52 | 5590 | 1,898.40 | unavailable | — |
| Cloning.MultimodeCoherent | 49 | 4491 | 1,458.60 | unavailable | — |
| Cloning.TensorCloning | 56 | 4472 | 830.20 | unavailable | — |
| Cloning.MatrixFidelity | 26 | 2152 | 829.20 | unavailable | — |
| Cloning.GeneralSymmetricOccupation | 11 | 1283 | 734.00 | unavailable | — |
| Cloning.TensorLAN | 31 | 2294 | 563.30 | unavailable | — |
| Cloning.PCTGlobal | 6 | 591 | 485.00 | unavailable | — |
| Cloning.MatrixLiftedCPTP | 4 | 343 | 466.00 | unavailable | — |
| Cloning.PCT | 7 | 891 | 460.00 | unavailable | — |
| Cloning.PCTHybridMixture | 4 | 322 | 393.00 | unavailable | — |
| Cloning.TensorLocalUnitary | 17 | 1750 | 385.20 | unavailable | — |
| Cloning.PhysicalFlatConverse | 20 | 1498 | 383.00 | unavailable | — |
| Cloning.GeneralCoherent | 7 | 632 | 336.00 | unavailable | — |
| Cloning.ComplexCoherent | 18 | 1515 | 320.70 | unavailable | — |
| Cloning.InfiniteFidelity | 8 | 655 | 295.30 | unavailable | — |
| Cloning.MixedLANTransfer | 4 | 412 | 285.00 | unavailable | — |
| Cloning.PCTPhysicalFidelity | 5 | 427 | 282.90 | unavailable | — |
| Cloning.PCTUnitaryTransport | 2 | 197 | 265.00 | unavailable | — |
| Cloning.PCTJointGaussianWhitening | 6 | 579 | 261.70 | unavailable | — |
| Cloning.PCTLocalChart | 7 | 632 | 240.40 | unavailable | — |
| Cloning.YoungHyperplane | 24 | 2294 | 176.90 | unavailable | — |
| Cloning.Channels.MatrixChannel | 1 | 46 | 169.00 | unavailable | — |
| Cloning.PCTRankPurification | 25 | 1717 | 160.50 | unavailable | — |
| Cloning.PhysicalCloningConverse | 9 | 734 | 158.00 | unavailable | — |
| Cloning.MultimodeAmplifier | 3 | 364 | 153.00 | unavailable | — |
| Cloning.MatrixTransitionAchievability | 1 | 95 | 151.00 | unavailable | — |
| Cloning.MatrixLANTransfer | 1 | 90 | 150.00 | unavailable | — |
| Cloning.YoungGeneral | 26 | 3115 | 149.00 | unavailable | — |
| Cloning.BosonicAmplifier | 6 | 691 | 148.00 | unavailable | — |
| Cloning.PCTJointGaussianReal | 1 | 102 | 144.00 | unavailable | — |
| Cloning.WeylGNS | 15 | 1079 | 134.30 | unavailable | — |
| Cloning.PCTGaussianOutput | 2 | 202 | 133.00 | unavailable | — |
| Cloning.PBW | 5 | 646 | 127.00 | unavailable | — |
| Cloning.InfiniteTraceClass.HilbertSchmidt | 1 | 432 | 127.00 | unavailable | — |
| Cloning.MatrixLiftedTrimming | 1 | 112 | 126.00 | unavailable | — |
| Cloning.YoungFlat | 13 | 1037 | 119.70 | unavailable | — |
| Cloning.Hybrid.PositiveField | 3 | 242 | 111.00 | unavailable | — |
| Cloning.PCTRankAdapted | 15 | 878 | 110.40 | unavailable | — |
| Cloning.SymmetricOccupation | 4 | 465 | 109.00 | unavailable | — |
| Cloning.InfiniteTraceClass.Polar | 1 | 172 | 107.00 | unavailable | — |
| Cloning.WeylCharacter | 8 | 692 | 105.60 | unavailable | — |
| Cloning.InfiniteTraceClass.TraceClass | 1 | 197 | 99.00 | unavailable | — |
| Cloning.Thermal | 4 | 687 | 97.20 | unavailable | — |
| Cloning.PCTGaussianCovariance | 4 | 348 | 92.00 | unavailable | — |
| Cloning.PoissonApproximation | 1 | 73 | 87.00 | unavailable | — |
| Cloning.PCTJointGaussianConvolution | 1 | 59 | 86.00 | unavailable | — |
| Cloning.PCTPurificationChannel | 4 | 678 | 79.80 | unavailable | — |
| Cloning.PCTProjectorPurity | 15 | 1039 | 78.10 | unavailable | — |
| Cloning.CountableScheffe | 1 | 186 | 77.00 | unavailable | — |
| Cloning.Occupation | 3 | 223 | 76.00 | unavailable | — |
| Cloning.Moments | 1 | 85 | 76.00 | unavailable | — |
| Cloning.PCTReducedGaussian | 2 | 177 | 69.00 | unavailable | — |
| Cloning.PCTRankGlobal | 7 | 518 | 66.50 | unavailable | — |
| Cloning.WeylSqueezer | 10 | 424 | 66.30 | unavailable | — |
| Cloning.PCTCountMeasurement | 7 | 532 | 66.10 | unavailable | — |
| Cloning.MatrixCovariantBalance | 1 | 141 | 65.00 | unavailable | — |
| Cloning.MultimodeLeastNoise | 1 | 128 | 64.00 | unavailable | — |
| Cloning.GaussianAffinity | 2 | 338 | 63.00 | unavailable | — |
| Cloning.ClassicalFidelity | 1 | 153 | 59.00 | unavailable | — |
| Cloning.PCTPhysicalState | 3 | 192 | 58.40 | unavailable | — |
| (root / facade) | 12 | 1481 | 57.30 | unavailable | — |
| Cloning | 3 | 320 | 55.00 | unavailable | — |
| Cloning.CoherentCoefficients | 1 | 80 | 54.00 | unavailable | — |
| Cloning.YoungCompatibility | 3 | 457 | 51.10 | unavailable | — |
| Cloning.Rounding | 1 | 231 | 49.00 | unavailable | — |
| Cloning.WeylSqueezerProduct | 3 | 308 | 48.50 | unavailable | — |
| Cloning.CovariantAmplifier | 7 | 364 | 48.50 | unavailable | — |
| Cloning.BlockFidelity | 1 | 121 | 48.00 | unavailable | — |
| Cloning.MultimodeIdler | 6 | 615 | 47.70 | unavailable | — |
| Cloning.YoungFlatCoupling | 8 | 653 | 47.30 | unavailable | — |
| Cloning.YoungMultinomial | 8 | 546 | 46.60 | unavailable | — |
| Cloning.BosonicNumberLaw | 1 | 264 | 46.00 | unavailable | — |
| Cloning.CountMultinomial | 6 | 420 | 45.30 | unavailable | — |
| Cloning.ValueExpansion | 9 | 732 | 44.30 | unavailable | — |
| Cloning.WernerNormalization | 1 | 91 | 42.00 | unavailable | — |
| Cloning.InfinitePowersStormer | 1 | 135 | 41.00 | unavailable | — |
| Cloning.PCTCount | 5 | 468 | 40.20 | unavailable | — |
| Cloning.PCTJointGaussianLaw | 1 | 180 | 40.00 | unavailable | — |
| Cloning.InfiniteOccupationStates | 1 | 119 | 39.00 | unavailable | — |
| Cloning.WernerAsymptotics | 1 | 207 | 38.00 | unavailable | — |
| Cloning.PBWSymmetricFrame | 4 | 383 | 37.90 | unavailable | — |
| Cloning.FiniteKrausLift | 1 | 110 | 37.00 | unavailable | — |
| Cloning.PCTFlatGaussianCross | 6 | 488 | 36.50 | unavailable | — |
| Cloning.LAN | 1 | 197 | 35.00 | unavailable | — |
| Cloning.InfiniteBilinearWeakClosure | 1 | 67 | 34.00 | unavailable | — |
| Cloning.InfiniteFiniteCorner | 1 | 122 | 33.00 | unavailable | — |
| Cloning.Hybrid.PositiveTraceClass | 5 | 289 | 32.90 | unavailable | — |
| Cloning.ValueComparison | 6 | 411 | 30.20 | unavailable | — |
| Cloning.PCTPrescribed | 5 | 297 | 30.10 | unavailable | — |
| Cloning.ThermalIdlerFidelity | 1 | 110 | 30.00 | unavailable | — |
| Cloning.PurificationSupport | 1 | 141 | 30.00 | unavailable | — |
| Cloning.ThermalWitness | 2 | 458 | 30.00 | unavailable | — |
| Cloning.InfiniteTraceClassWeakLimit | 1 | 87 | 30.00 | unavailable | — |
| Cloning.PhysicalFlatGrassmann | 5 | 361 | 29.90 | unavailable | — |
| Cloning.PCTPurity | 5 | 432 | 28.10 | unavailable | — |
| Cloning.PhysicalFlatPCT | 4 | 163 | 27.40 | unavailable | — |
| Cloning.Channels | 2 | 119 | 25.20 | unavailable | — |
| Cloning.MultimodeThermalIdlerFidelity | 1 | 114 | 25.00 | unavailable | — |
| Cloning.PCTRankOne | 3 | 171 | 23.00 | unavailable | — |
| Cloning.YoungDimensionRatio | 3 | 560 | 22.60 | unavailable | — |
| Cloning.MatrixRegularization | 1 | 86 | 22.00 | unavailable | — |
| Cloning.SampleRatio | 4 | 139 | 20.70 | unavailable | — |
| Cloning.OrbitalSeededOptimum | 1 | 43 | 20.00 | unavailable | — |
| Cloning.QubitDegeneracy | 1 | 225 | 18.00 | unavailable | — |
| Cloning.YoungTwoRow | 3 | 819 | 16.20 | unavailable | — |
| Cloning.PhysicalAllStateMinimax | 3 | 142 | 16.10 | unavailable | — |
| Cloning.YoungRounding | 2 | 755 | 15.00 | unavailable | — |
| Cloning.Compression | 2 | 208 | 14.80 | unavailable | — |
| Cloning.ScalarTaylor | 3 | 131 | 14.30 | unavailable | — |
| Cloning.BosonicStochasticOrder | 2 | 195 | 14.20 | unavailable | — |
| Cloning.InfiniteFidelityCorner | 2 | 211 | 13.50 | unavailable | — |
| Cloning.InfiniteTraceClassAsymptoticBound | 1 | 49 | 13.00 | unavailable | — |
| Cloning.SpectralGap | 2 | 321 | 12.10 | unavailable | — |
| Cloning.InfiniteFidelityHilbertSum | 2 | 186 | 11.70 | unavailable | — |
| Cloning.BoundedOperator | 1 | 85 | 10.00 | unavailable | — |
| Cloning.CoherentGaussianMixture | 1 | 163 | 9.00 | unavailable | — |
| Cloning.MultimodeCoherentGaussianMixture | 1 | 109 | 8.50 | unavailable | — |
| Cloning.PositiveKernel | 1 | 133 | 7.40 | unavailable | — |
| Cloning.CartanChannel | 1 | 74 | 7.40 | unavailable | — |
| Cloning.MatrixLiftedChannel | 1 | 100 | 7.20 | unavailable | — |
| Cloning.ComplexGaussianMoments | 1 | 81 | 6.20 | unavailable | — |
| Cloning.TensorCartanLieBalance | 1 | 116 | 6.00 | unavailable | — |
| Cloning.UniversalLeastNoise | 1 | 150 | 5.80 | unavailable | — |
| Cloning.InfiniteDiagonalFidelity | 1 | 104 | 5.60 | unavailable | — |
| Cloning.Hybrid.PhaseBody | 1 | 140 | 5.60 | unavailable | — |
| Cloning.InfiniteLANTransfer | 1 | 92 | 5.00 | unavailable | — |
| Cloning.Projector | 1 | 224 | 4.00 | unavailable | — |

## 7. Own-file profiles

Cumulative C++ timers are exclusive **elapsed** times summed across threads, not OS CPU. Trace self weights are elapsed intervals; inclusive trace rankings overlap. Detailed profiling adds instrumentation overhead; these are warm own-file attribution runs. Saved Lake setups bind mapped artifact paths; direct import families are content hashed and mapped transitive artifacts are guarded by path/size/mtime. Newly unmapped direct imports fall back to the recorded search path; their nonmapped transitive closure is not inventoried. The dominant-phase screen requires >5 s and >25% of the displayed phase sum. Declaration pointers identify declarations, not automatically an exact costly tactic.

| Module | Run | Exit | Process wall s | Phase sum s | Dominant screen | >100 ms events |
| --- | --- | --- | --- | --- | --- | --- |
| Cloning.WeylIdlerUniqueness | 1 | 0 | 193.20 | 125.13 | tactic execution | 6 |
| Cloning.PCTHybridMixtureFactor | 1 | 0 | 33.91 | 29.94 | elaboration | 22 |
| Cloning.WernerPhysicalPullback | 1 | 0 | 332.32 | 84.24 | interpretation, tactic execution | 10 |
| Cloning.PCTGlobalPhysical | 1 | 0 | 84.20 | 34.47 | import, interpretation | 25 |
| Cloning.PCTUnitaryTransportChannels | 1 | 0 | 10.06 | 9.43 | import | 7 |
| Cloning.InfiniteTraceClass | 1 | 0 | 24.31 | 44.21 | typeclass inference | 85 |
| Cloning.Thermal | 1 | 0 | 7.02 | 13.64 | no phase above both thresholds | 8 |
| Cloning.AmplifierWeylThermal | 1 | 0 | 9.01 | 7.80 | no phase above both thresholds | 7 |
| Cloning.PCTClosedForm | 1 | 0 | 6.26 | 5.26 | no phase above both thresholds | 2 |
| Cloning.CloningValueComparisonMonotone | 1 | 0 | 8.81 | 7.27 | no phase above both thresholds | 3 |

### Cloning.WeylIdlerUniqueness — repetition 1

Recorded profile commit: `80e4b7ca1aa43969f85105171bfd80bf662d6b32`; source SHA-256: `c3ad276535f7e0b776dae495c8a0a8e42e9967d8a36f8ed7d5a8ef55193ac80d`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | cbb2fd2007ae367e201d4a6ac7c069899db90dbd |
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
| tactic execution | 105.000 |
| interpretation | 7.850 |
| import | 5.820 |
| typeclass inference | 5.470 |
| type checking | 0.428 |
| simp | 0.339 |
| elaboration | 0.148 |
| initialization | 0.018 |
| process pre-definitions | 0.015 |
| linting | 0.012 |
| share common exprs | 0.011 |
| parsing | 0.007 |
| instantiate metavars | 0.006 |
| congr simp thm | 0.004 |
| dsimp | 0.002 |
| fix level params | 0.001 |
| let-to-have transformation | 0.001 |
| compilation (LCNF base) | 0.001 |
| compilation (LCNF mono) | 0.000 |
| compilation (LCNF impure) | 0.000 |
| attribute application | 0.000 |
| compilation (IR) | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| tactic execution of Lean.Parser.Tactic.change took 103s | 103.000 | 4 |
| import took 5.82s | 5.820 | 1 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 221ms | 0.221 | 5 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 134ms | 0.134 | 6 |
| simp took 130ms | 0.130 | 2 |
| tactic execution of Lean.Parser.Tactic.refine took 114ms | 0.114 | 3 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 110.253 | 111.655 | unattributed |
| Meta.isDefEq: ✅️ b.repr.toLinearEquiv.2 (lp.single 2 i✝ 1) =?= b.repr.toLinearEquiv.2 (lp.single 2 i✝ 1) | 97.332 | 97.332 | unattributed |
| Meta.isDefEq: ✅️ {   re :=     (↑((CFC.abs                   ↑(↑(Cloning.InfiniteTraceClass.traceClassRightMultiply                           (Cloning.InfiniteTraceClass.rankOneOperator x x))                       (((InnerProductSpace.rankOne ℂ) (Cloning.MultimodeCoherent.coherentVector 0))          | 2.112 | 100.494 | unattributed |
| Meta.isDefEq.delta: ✅️ ⋯.choose =?= ⋯.choose | 1.073 | 101.647 | unattributed |
| Meta.isDefEq: ✅️ ⋯.choose.repr.toLinearEquiv.2 (lp.single 2 i✝² 1) =?= ⋯.choose.repr.toLinearEquiv.2 (lp.single 2 i✝² 1) | 0.789 | 102.465 | unattributed |
| Meta.check: ✅️ DFunLike.hasCoeToFun | 0.597 | 0.668 | unattributed |
| Meta.isDefEq: ✅️ Real.mul✝   (↑((CFC.abs             ↑(↑(Cloning.InfiniteTraceClass.traceClassRightMultiply (Cloning.InfiniteTraceClass.rankOneOperator x x))                 (((InnerProductSpace.rankOne ℂ) (Cloning.MultimodeCoherent.coherentVector 0))                   (Cloning.MultimodeCoherent.coh | 0.311 | 98.125 | unattributed |
| Meta.isDefEq: ✅️ (↑(CFC.abs           ↑(↑(Cloning.InfiniteTraceClass.traceClassRightMultiply (Cloning.InfiniteTraceClass.rankOneOperator x x))               (((InnerProductSpace.rankOne ℂ) (Cloning.MultimodeCoherent.coherentVector 0))                 (Cloning.MultimodeCoherent.coherentVector 0))))). | 0.266 | 97.686 | unattributed |
| Meta.isDefEq: ✅️ Real.add✝   ((↑((CFC.abs               ↑(↑(Cloning.InfiniteTraceClass.traceClassRightMultiply (Cloning.InfiniteTraceClass.rankOneOperator x x))                   (((InnerProductSpace.rankOne ℂ) (Cloning.MultimodeCoherent.coherentVector 0))                     (Cloning.MultimodeCoher | 0.223 | 98.354 | unattributed |
| Elab.lint: running linters | 0.162 | 0.162 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 110.253 | 111.655 | unattributed |
| Elab.async: elaborating proof of Cloning.MultimodeCoherent.integral_weighted_characteristic | 0.005 | 104.367 | unattributed |
| Elab.definition.value: Cloning.MultimodeCoherent.integral_weighted_characteristic | 0.004 | 104.361 | Cloning.MultimodeCoherent.integral_weighted_characteristic at formalization/Cloning/WeylIdlerUniqueness.lean:82 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   have heq :     gaussianCharacteristicIntegral (d := d) =       (tracePairingCLM (H := Fock d)).flip (InnerProductSpace.rankOne ℂ (coherentVector 0) (coherentVector 0)) :=     by     apply traceClass_functional_ext     intro x     change       (∫ a : Fin d → | 0.000 | 104.358 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   have heq :     gaussianCharacteristicIntegral (d := d) =       (tracePairingCLM (H := Fock d)).flip (InnerProductSpace.rankOne ℂ (coherentVector 0) (coherentVector 0)) :=     by     apply traceClass_functional_ext     intro x     change       (∫ a  | 0.000 | 104.358 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticHave__: have heq :   gaussianCharacteristicIntegral (d := d) =     (tracePairingCLM (H := Fock d)).flip (InnerProductSpace.rankOne ℂ (coherentVector 0) (coherentVector 0)) :=   by   apply traceClass_functional_ext   intro x   change     (∫ a : Fin d → ℂ, (weylGaus | 0.000 | 104.311 | unattributed |
| Elab.step: Lean.Parser.Tactic.focus: focus   refine     no_implicit_lambda%       (have heq :         gaussianCharacteristicIntegral (d := d) =           (tracePairingCLM (H := Fock d)).flip (InnerProductSpace.rankOne ℂ (coherentVector 0) (coherentVector 0)) :=         ?body✝;       ?_)   case body✝ | 0.000 | 104.311 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   refine     no_implicit_lambda%       (have heq :         gaussianCharacteristicIntegral (d := d) =           (tracePairingCLM (H := Fock d)).flip (InnerProductSpace.rankOne ℂ (coherentVector 0) (coherentVector 0)) :=         ?body✝;       ?_)   case body✝ = | 0.000 | 104.311 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   refine     no_implicit_lambda%       (have heq :         gaussianCharacteristicIntegral (d := d) =           (tracePairingCLM (H := Fock d)).flip (InnerProductSpace.rankOne ℂ (coherentVector 0) (coherentVector 0)) :=         ?body✝;       ?_)   cas | 0.000 | 104.311 | unattributed |
| Elab.step: Lean.Parser.Tactic.case: case body✝ =>   with_annotate_state"by"     ( apply traceClass_functional_ext       intro x       change         (∫ a : Fin d → ℂ, (weylGaussianWeight a : ℂ) * tracePairing (rankOneOperator x x) (displacement a)) =           tracePairing (rankOneOperator x x) (Inn | 0.003 | 103.714 | unattributed |

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.WeylIdlerUniqueness-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.WeylIdlerUniqueness-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.WeylIdlerUniqueness-1.setup.json Cloning/WeylIdlerUniqueness.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.PCTHybridMixtureFactor — repetition 1

Recorded profile commit: `80e4b7ca1aa43969f85105171bfd80bf662d6b32`; source SHA-256: `dc112ae5e22432d2e6502a06efd023939d9e5b40b13b63a044f06b480272ef54`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | cbb2fd2007ae367e201d4a6ac7c069899db90dbd |
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
| Imported compacted-region bytes (not RSS) | 4057454664 |
| Imported compacted regions (Lean labels these modules) | 20375 |
| Memory-mapped compacted regions | 20286 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| elaboration | 11.700 |
| typeclass inference | 7.470 |
| import | 7.170 |
| interpretation | 2.310 |
| tactic execution | 1.090 |
| type checking | 0.077 |
| let-to-have transformation | 0.042 |
| initialization | 0.019 |
| simp | 0.014 |
| linting | 0.011 |
| ring | 0.008 |
| congr simp thm | 0.006 |
| share common exprs | 0.005 |
| dsimp | 0.005 |
| instantiate metavars | 0.005 |
| parsing | 0.004 |
| process pre-definitions | 0.004 |
| compilation (LCNF base) | 0.002 |
| norm_num | 0.001 |
| fix level params | 0.001 |
| compilation (LCNF mono) | 0.001 |
| compilation (LCNF impure) | 0.000 |
| compilation (IR) | 0.000 |
| attribute application | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| import took 7.17s | 7.170 | 1 |
| elaboration took 4.19s | 4.190 | 19 |
| elaboration took 3.76s | 3.760 | 5 |
| elaboration took 3.73s | 3.730 | 10 |
| typeclass inference of TopologicalSpace took 448ms | 0.448 | 11 |
| typeclass inference of AddCommMonoid took 445ms | 0.445 | 12 |
| typeclass inference of Module took 376ms | 0.376 | 13 |
| tactic execution of Lean.Parser.Tactic.refine took 344ms | 0.344 | 14 |
| typeclass inference of SecondCountableTopologyEither took 315ms | 0.315 | 15 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 252ms | 0.252 | 22 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 9.107 | 24.212 | unattributed |
| Meta.isDefEq: ✅️ { toAdd := ContinuousLinearMap.add, add_assoc := ⋯, toZero := ContinuousLinearMap.zero, zero_add := ⋯, add_zero := ⋯,   nsmul := fun x1 x2 => x1 • x2, nsmul_zero := ⋯,   nsmul_succ :=     ⋯ } =?= { toAdd := ContinuousLinearMap.add, add_assoc := ⋯, toZero := ContinuousLinearMap.zero, | 4.660 | 4.713 | unattributed |
| Meta.isDefEq: ❌️ (MeasureTheory.ae ?m.6).sets.Mem   {x \| (fun x => f x = g x) x} =?= (MeasureTheory.ae MeasureTheory.volume).sets.Mem {x \| (fun x => f x = g x) x} | 2.563 | 2.690 | unattributed |
| Meta.isDefEq: ❌️ {x \| (fun x => f x = g x) x} ∈   (MeasureTheory.ae ?m.6).sets =?= {x \| (fun x => f x = g x) x} ∈ (MeasureTheory.ae MeasureTheory.volume).sets | 1.192 | 4.081 | unattributed |
| Meta.isDefEq: ❌️ (MeasureTheory.ae ?m.54).sets.Mem   {x \| (fun x => f x = g x) x} =?= (MeasureTheory.ae MeasureTheory.volume).sets.Mem {x \| (fun x => f x = g x) x} | 0.978 | 1.494 | unattributed |
| Meta.isDefEq: ❌️ ∀ᵐ (x : Fin k → ℝ) ∂?m.6, f x = g x =?= ∀ᵐ (x : Fin k → ℝ), f x = g x | 0.906 | 5.889 | unattributed |
| Meta.isDefEq: ❌️ f =ᵐ[?m.6] g =?= f =ᵐ[MeasureTheory.volume] g | 0.905 | 6.794 | unattributed |
| Meta.isDefEq: ❌️ {x \| (fun x => f x = g x) x} ∈   MeasureTheory.ae ?m.6 =?= {x \| (fun x => f x = g x) x} ∈ MeasureTheory.ae MeasureTheory.volume | 0.900 | 4.983 | unattributed |
| Meta.isDefEq: ❌️ (MeasureTheory.ae ?m.54).sets =?= (MeasureTheory.ae MeasureTheory.volume).sets | 0.830 | 0.830 | unattributed |
| Meta.isDefEq: ❌️ ∀ᵐ (x : Fin k → ℝ) ∂?m.54, f x = g x =?= ∀ᵐ (x : Fin k → ℝ), f x = g x | 0.502 | 3.269 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 9.107 | 24.212 | unattributed |
| Meta.isDefEq: ❌️ { f //   MeasureTheory.AEStronglyMeasurable f ?m.6 } =?= { f // MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume } | 0.002 | 6.812 | unattributed |
| Meta.isDefEq: ❌️ fun f =>   MeasureTheory.AEStronglyMeasurable f ?m.6 =?= fun f => MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume | 0.002 | 6.810 | unattributed |
| Meta.isDefEq: ❌️ MeasureTheory.AEStronglyMeasurable f ?m.6 =?= MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume | 0.002 | 6.808 | unattributed |
| Meta.isDefEq: ❌️ ∃ g,   MeasureTheory.StronglyMeasurable g ∧     f =ᵐ[?m.6] g =?= ∃ g, MeasureTheory.StronglyMeasurable g ∧ f =ᵐ[MeasureTheory.volume] g | 0.002 | 6.805 | unattributed |
| Meta.isDefEq: ❌️ fun g =>   MeasureTheory.StronglyMeasurable g ∧     f =ᵐ[?m.6] g =?= fun g => MeasureTheory.StronglyMeasurable g ∧ f =ᵐ[MeasureTheory.volume] g | 0.001 | 6.803 | unattributed |
| Meta.isDefEq: ❌️ MeasureTheory.StronglyMeasurable g ∧   f =ᵐ[?m.6] g =?= MeasureTheory.StronglyMeasurable g ∧ f =ᵐ[MeasureTheory.volume] g | 0.008 | 6.802 | unattributed |
| Meta.isDefEq: ❌️ f =ᵐ[?m.6] g =?= f =ᵐ[MeasureTheory.volume] g | 0.905 | 6.794 | unattributed |
| Meta.isDefEq: ❌️ (Fin k → ℝ) →ₘ[?m.6]   Cloning.InfiniteTraceClass.TraceClass     ↥(Cloning.MultimodeCoherent.Fock         d) =?= (Fin k → ℝ) →ₘ[MeasureTheory.volume]   Cloning.InfiniteTraceClass.TraceClass ↥(Cloning.MultimodeCoherent.Fock d) | 0.002 | 6.066 | unattributed |
| Meta.isDefEq: ❌️ Quotient   (MeasureTheory.Measure.aeEqSetoid (Cloning.InfiniteTraceClass.TraceClass ↥(Cloning.MultimodeCoherent.Fock d))     ?m.6) =?= Quotient   (MeasureTheory.Measure.aeEqSetoid (Cloning.InfiniteTraceClass.TraceClass ↥(Cloning.MultimodeCoherent.Fock d))     MeasureTheory.volume) | 0.001 | 6.064 | unattributed |

Unattributed elaboration events above threshold: 3; the detailed trace rankings supply attribution where their labels identify declarations.

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.PCTHybridMixtureFactor-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.PCTHybridMixtureFactor-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.PCTHybridMixtureFactor-1.setup.json Cloning/PCTHybridMixtureFactor.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.WernerPhysicalPullback — repetition 1

Recorded profile commit: `80e4b7ca1aa43969f85105171bfd80bf662d6b32`; source SHA-256: `815e8e1962e901e11ae9fbd73bd3988bd0cc58ec6c953685b05fa25226aa17ea`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | cbb2fd2007ae367e201d4a6ac7c069899db90dbd |
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
| tactic execution | 39.400 |
| interpretation | 34.700 |
| import | 5.340 |
| typeclass inference | 3.450 |
| elaboration | 0.792 |
| simp | 0.249 |
| type checking | 0.223 |
| initialization | 0.018 |
| linting | 0.018 |
| process pre-definitions | 0.017 |
| parsing | 0.010 |
| share common exprs | 0.007 |
| norm_num | 0.005 |
| congr simp thm | 0.005 |
| compilation (LCNF base) | 0.003 |
| compilation (LCNF mono) | 0.002 |
| instantiate metavars | 0.002 |
| fix level params | 0.001 |
| let-to-have transformation | 0.001 |
| compilation (LCNF impure) | 0.001 |
| attribute application | 0.000 |
| compilation (IR) | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| tactic execution of Lean.Parser.Tactic.change took 36.7s | 36.700 | 8 |
| import took 5.34s | 5.340 | 1 |
| tactic execution of Lean.Parser.Tactic.change took 2.29s | 2.290 | 2 |
| elaboration took 659ms | 0.659 | 9 |
| typeclass inference of CoeFun took 137ms | 0.137 | 3 |
| typeclass inference of AddMonoidHomClass took 118ms | 0.118 | 4 |
| typeclass inference of CoeFun took 116ms | 0.116 | 6 |
| number of impointerpretation of SetLike.delabSubtypeSetLike._boxed took 113ms | 0.113 | 782 |
| simp took 108ms | 0.108 | 5 |
| typeclass inference of CoeFun took 105ms | 0.105 | 7 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 42.639 | 44.279 | unattributed |
| Meta.isDefEq: ✅️ b.repr.toLinearEquiv.2 (lp.single 2 i✝ 1) =?= b.repr.toLinearEquiv.2 (lp.single 2 i✝ 1) | 27.732 | 27.732 | unattributed |
| Meta.isDefEq: ✅️ {   re :=     (↑((CFC.abs                   ↑((Cloning.GeneralSymmetricOccupation.occupationRecovery L s).toLinearMap                       (Cloning.GeneralSymmetricOccupation.wernerOutput S)))                 (b i✝))             i).re *         ((starRingEnd ℂ) (↑(b i✝) i)).re -    | 1.785 | 30.593 | unattributed |
| Meta.isDefEq: ✅️ {   re :=     (↑(↑(ContinuousLinearMap.adjoint (Cloning.GeneralSymmetricOccupation.isometry L (s + 1)).toContinuousLinearMap) x)             i).re *         ((starRingEnd ℂ) (↑i✝³ i)).re -       (↑(↑(ContinuousLinearMap.adjoint (Cloning.GeneralSymmetricOccupation.isometry L (s + 1)) | 0.833 | 1.209 | unattributed |
| Meta.isDefEq: ✅️ Real.mul✝   (↑((CFC.abs             ↑((Cloning.GeneralSymmetricOccupation.occupationRecovery L s).toLinearMap                 (Cloning.GeneralSymmetricOccupation.wernerOutput S)))           (b i✝))       i).re   ((starRingEnd ℂ)       (↑(b i✝)         i)).re =?= Real.mul✝   (↑((CFC. | 0.688 | 28.224 | unattributed |
| Meta.isDefEq: ✅️ { toAdd := ContinuousLinearMap.add, add_assoc := ⋯, toZero := ContinuousLinearMap.zero, zero_add := ⋯, add_zero := ⋯,   nsmul := fun x1 x2 => x1 • x2, nsmul_zero := ⋯,   nsmul_succ :=     ⋯ } =?= { toAdd := ContinuousLinearMap.add, add_assoc := ⋯, toZero := ContinuousLinearMap.zero, | 0.590 | 0.943 | unattributed |
| Meta.isDefEq: ✅️ Real.add✝   ((↑((CFC.abs               ↑((Cloning.GeneralSymmetricOccupation.occupationRecovery L s).toLinearMap                   (Cloning.GeneralSymmetricOccupation.wernerOutput S)))             (b i✝))         i).re *     ((starRingEnd ℂ) (↑(b i✝) i)).re)   (-((↑((CFC.abs         | 0.506 | 28.744 | unattributed |
| Meta.isDefEq: ✅️ (↑(↑(ContinuousLinearMap.adjoint (Cloning.GeneralSymmetricOccupation.occupationPad L s).toContinuousLinearMap)         (⋯.choose i✝³))     i).1 =?= (↑(↑(ContinuousLinearMap.adjoint             (Cloning.GeneralSymmetricOccupation.occupationPad L s).toContinuousLinearMap)         (⋯.c | 0.340 | 22.937 | unattributed |
| Meta.synthInstance: ❌️ Nonempty (Fin s) | 0.338 | 0.338 | unattributed |
| Meta.isDefEq: ✅️ (↑(ContinuousLinearMap.adjoint (Cloning.GeneralSymmetricOccupation.occupationPad L s).toContinuousLinearMap)       (⋯.choose i✝³)).1   i =?= (↑(ContinuousLinearMap.adjoint (Cloning.GeneralSymmetricOccupation.occupationPad L s).toContinuousLinearMap)       (⋯.choose i✝³)).1   i | 0.335 | 22.597 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 42.639 | 44.279 | unattributed |
| Elab.async: elaborating proof of Cloning.GeneralSymmetricOccupation.wernerOutput_trace_one | 0.002 | 37.419 | unattributed |
| Elab.definition.value: Cloning.GeneralSymmetricOccupation.wernerOutput_trace_one | 0.001 | 37.417 | Cloning.GeneralSymmetricOccupation.wernerOutput_trace_one at formalization/Cloning/WernerPhysicalPullback.lean:206 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   have htp := (occupationRecovery L s).trace_preserving (wernerOutput (s := s) S)   change     traceCLM ((occupationRecovery L s).toLinearMap (wernerOutput (s := s) S)) =       traceCLM (wernerOutput (s := s) S) at htp   rw [← htp, occupationRecovery_wernerOu | 0.000 | 37.416 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   have htp := (occupationRecovery L s).trace_preserving (wernerOutput (s := s) S)   change     traceCLM ((occupationRecovery L s).toLinearMap (wernerOutput (s := s) S)) =       traceCLM (wernerOutput (s := s) S) at htp   rw [← htp, occupationRecovery | 0.001 | 37.416 | unattributed |
| Elab.step: Lean.Parser.Tactic.change: change   traceCLM ((occupationRecovery L s).toLinearMap (wernerOutput (s := s) S)) = traceCLM (wernerOutput (s := s) S) at htp | 0.003 | 37.149 | unattributed |
| Meta.isDefEq: ✅️ Cloning.InfiniteTraceClass.traceCLM     ((Cloning.GeneralSymmetricOccupation.occupationRecovery L s).toLinearMap       (Cloning.GeneralSymmetricOccupation.wernerOutput S)) =   Cloning.InfiniteTraceClass.traceCLM     (Cloning.GeneralSymmetricOccupation.wernerOutput       S) =?= Cloni | 0.000 | 36.683 | unattributed |
| Meta.isDefEq: ✅️ Cloning.InfiniteTraceClass.traceCLM   ((Cloning.GeneralSymmetricOccupation.occupationRecovery L s).toLinearMap     (Cloning.GeneralSymmetricOccupation.wernerOutput       S)) =?= Cloning.InfiniteTraceClass.trace   ↑((Cloning.GeneralSymmetricOccupation.occupationRecovery L s).toLinear | 0.000 | 36.147 | unattributed |
| Meta.isDefEq: ✅️ Cloning.InfiniteTraceClass.traceCLM   ((Cloning.GeneralSymmetricOccupation.occupationRecovery L s).toLinearMap     (Cloning.GeneralSymmetricOccupation.wernerOutput       S)) =?= ∑' (i : ↑(Exists.choose ⋯)),   ⟪⋯.choose i,     ↑((Cloning.GeneralSymmetricOccupation.occupationRecovery  | 0.000 | 36.147 | unattributed |
| Meta.isDefEq: ✅️ Cloning.InfiniteTraceClass.traceCLM   ((Cloning.GeneralSymmetricOccupation.occupationRecovery L s).toLinearMap     (Cloning.GeneralSymmetricOccupation.wernerOutput       S)) =?= wrapped✝.1 fun i =>   ⟪⋯.choose i,     ↑((Cloning.GeneralSymmetricOccupation.occupationRecovery L s).toLi | 0.000 | 36.146 | unattributed |

Unattributed elaboration events above threshold: 1; the detailed trace rankings supply attribution where their labels identify declarations.

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.WernerPhysicalPullback-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.WernerPhysicalPullback-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.WernerPhysicalPullback-1.setup.json Cloning/WernerPhysicalPullback.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.PCTGlobalPhysical — repetition 1

Recorded profile commit: `80e4b7ca1aa43969f85105171bfd80bf662d6b32`; source SHA-256: `fb0231237298a06a32147e115e6e8f29f0ad572e8a0f4698db82b86654f553c6`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | cbb2fd2007ae367e201d4a6ac7c069899db90dbd |
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
| Imported compacted-region bytes (not RSS) | 4021497408 |
| Imported compacted regions (Lean labels these modules) | 20199 |
| Memory-mapped compacted regions | 20110 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| import | 12.400 |
| interpretation | 9.250 |
| elaboration | 5.830 |
| typeclass inference | 5.170 |
| tactic execution | 1.470 |
| type checking | 0.221 |
| simp | 0.026 |
| initialization | 0.025 |
| process pre-definitions | 0.017 |
| linting | 0.014 |
| let-to-have transformation | 0.013 |
| share common exprs | 0.011 |
| parsing | 0.007 |
| congr simp thm | 0.006 |
| instantiate metavars | 0.004 |
| fix level params | 0.003 |
| attribute application | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| import took 12.4s | 12.400 | 1 |
| elaboration took 5.02s | 5.020 | 22 |
| tactic execution of Lean.Parser.Tactic.change took 611ms | 0.611 | 15 |
| typeclass inference of CoeFun took 441ms | 0.441 | 13 |
| elaboration took 435ms | 0.435 | 5 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 345ms | 0.345 | 16 |
| typeclass inference of CoeFun took 341ms | 0.341 | 12 |
| typeclass inference of CoeFun took 306ms | 0.306 | 14 |
| typeclass inference of CoeFun took 294ms | 0.294 | 11 |
| typeclass inference of CoeFun took 267ms | 0.267 | 8 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 17.409 | 21.101 | unattributed |
| Meta.isDefEq: ✅️ { toAdd := ContinuousLinearMap.add, add_assoc := ⋯, toZero := ContinuousLinearMap.zero, zero_add := ⋯, add_zero := ⋯,   nsmul := fun x1 x2 => x1 • x2, nsmul_zero := ⋯,   nsmul_succ :=     ⋯ } =?= { toAdd := ContinuousLinearMap.add, add_assoc := ⋯, toZero := ContinuousLinearMap.zero, | 2.299 | 2.694 | unattributed |
| Meta.isDefEq: ✅️ {   re :=     (LinearMap.id (↑((Cloning.GeneralSymmetricOccupation.isometry n (s + 1)).toLinearMap x) i✝)).re *         (↑(Cloning.PCT.tensorVector fun i =>                 (Cloning.PCTGlobal.coordinateFrame (Fintype.equivFinOfCardEq hcard).symm) (i✝ i))             i).re -       (L | 0.965 | 0.965 | unattributed |
| Meta.isDefEq: ✅️ {   re :=     (LinearMap.id (↑((Cloning.GeneralSymmetricOccupation.isometry n (s + 1)).toLinearMap x) i✝)).re *         (↑(Cloning.PCT.tensorVector fun i => (Cloning.PCTGlobal.fixedFrame hcard) (i✝ i)) i).re -       (LinearMap.id (↑((Cloning.GeneralSymmetricOccupation.isometry n (s  | 0.868 | 1.438 | unattributed |
| Meta.check: ✅️ DFunLike.hasCoeToFun | 0.347 | 2.537 | unattributed |
| Meta.isDefEq: ✅️ Real.add✝   ((LinearMap.id (↑((Cloning.GeneralSymmetricOccupation.isometry n (s + 1)).toLinearMap x) i✝)).re *     (↑(Cloning.PCT.tensorVector fun i => (Cloning.PCTGlobal.fixedFrame hcard) (i✝ i)) i).im)   ((LinearMap.id (↑((Cloning.GeneralSymmetricOccupation.isometry n (s + 1)).toL | 0.244 | 0.267 | unattributed |
| Meta.isDefEq: ✅️ Real.add✝   ((LinearMap.id (↑((Cloning.GeneralSymmetricOccupation.isometry n (s + 1)).toLinearMap x) i✝)).re *     (↑(Cloning.PCT.tensorVector fun i => (Cloning.PCTGlobal.fixedFrame hcard) (i✝ i)) i).re)   (-((LinearMap.id (↑((Cloning.GeneralSymmetricOccupation.isometry n (s + 1)).t | 0.215 | 0.261 | unattributed |
| Elab.step: Lean.Parser.Tactic.rewriteSeq: rewrite [purificationChannel_apply, recoveredMatrix_lift] | 0.192 | 0.348 | unattributed |
| Elab.lint: running linters | 0.183 | 0.183 | unattributed |
| Meta.isDefEq: ✅️ fun x1 x2 => x1 • x2 =?= fun x1 x2 => x1 • x2 | 0.178 | 0.395 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 17.409 | 21.101 | unattributed |
| Elab.async: elaborating proof of Cloning.PCTGlobal.channel_matrix_apply | 0.009 | 5.031 | unattributed |
| Elab.definition.value: Cloning.PCTGlobal.channel_matrix_apply | 0.002 | 5.022 | Cloning.PCTGlobal.channel_matrix_apply at formalization/Cloning/PCTGlobalPhysical.lean:83 |
| Meta.isDefEq: ✅️ NormedAddCommGroup.toENormedAddCommMonoid.toAddCommMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddCommMonoid | 0.004 | 3.377 | unattributed |
| Meta.isDefEq: ✅️ { toAddMonoid := NormedAddCommGroup.toENormedAddCommMonoid.toAddMonoid,   add_comm :=     ⋯ } =?= { toAddMonoid := Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddMonoid, add_comm := ⋯ } | 0.016 | 3.373 | unattributed |
| Meta.isDefEq: ✅️ NormedAddCommGroup.toENormedAddCommMonoid.toAddMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddMonoid | 0.006 | 3.357 | unattributed |
| Meta.isDefEq: ✅️ NormedAddCommGroup.toNormedAddGroup.toAddMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddMonoid | 0.003 | 3.352 | unattributed |
| Meta.isDefEq.delta: ✅️ NormedAddCommGroup.toNormedAddGroup.toAddMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddMonoid | 0.016 | 3.348 | unattributed |
| Meta.isDefEq: ✅️ NormedAddCommGroup.toNormedAddGroup.toSubNegMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toSubNegMonoid | 0.003 | 3.332 | unattributed |
| Meta.isDefEq.delta: ✅️ NormedAddCommGroup.toNormedAddGroup.toSubNegMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toSubNegMonoid | 0.005 | 3.329 | unattributed |

Unattributed elaboration events above threshold: 2; the detailed trace rankings supply attribution where their labels identify declarations.

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.PCTGlobalPhysical-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.PCTGlobalPhysical-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.PCTGlobalPhysical-1.setup.json Cloning/PCTGlobalPhysical.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.PCTUnitaryTransportChannels — repetition 1

Recorded profile commit: `80e4b7ca1aa43969f85105171bfd80bf662d6b32`; source SHA-256: `9eff2831f65aaf27d9d81958f1a14501a9126e4a389de0db9e76bf6a0990e57a`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | cbb2fd2007ae367e201d4a6ac7c069899db90dbd |
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
| Imported compacted-region bytes (not RSS) | 4104053552 |
| Imported compacted regions (Lean labels these modules) | 20500 |
| Memory-mapped compacted regions | 20407 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| import | 5.900 |
| tactic execution | 1.320 |
| interpretation | 0.813 |
| typeclass inference | 0.668 |
| elaboration | 0.501 |
| type checking | 0.149 |
| initialization | 0.020 |
| simp | 0.018 |
| process pre-definitions | 0.011 |
| linting | 0.009 |
| share common exprs | 0.006 |
| parsing | 0.004 |
| attribute application | 0.003 |
| fix level params | 0.002 |
| let-to-have transformation | 0.001 |
| instantiate metavars | 0.001 |
| congr simp thm | 0.001 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| import took 5.9s | 5.900 | 1 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 325ms | 0.325 | 2 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 311ms | 0.311 | 9 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 305ms | 0.305 | 11 |
| elaboration took 275ms | 0.275 | 13 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 251ms | 0.251 | 10 |
| elaboration took 117ms | 0.117 | 12 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 6.466 | 7.504 | unattributed |
| Elab.step: Lean.Parser.Tactic.rewriteSeq: rewrite [← tensorState_conjugated, tensorUnitary_star, unitaryChannel_star] | 0.203 | 0.319 | unattributed |
| Elab.lint: running linters | 0.134 | 0.134 | unattributed |
| Elab.step: Lean.Parser.Term.app: expected type: Sort ?u.13229, term unitary (Matrix A A ℂ) | 0.128 | 0.150 | unattributed |
| Meta.check: ✅️ fun _a =>   Cloning.PCTPurificationChannel.registerLiftCLM       (Cloning.InfiniteFiniteCorner.matrixOf ⇑(Cloning.PCT.registerBasis A) ↑X * _a) =     Cloning.PCTPurificationChannel.registerLiftCLM       (Cloning.InfiniteFiniteCorner.matrixOf ⇑(Cloning.PCT.registerBasis A) ↑X) | 0.121 | 0.157 | unattributed |
| Meta.isDefEq: ✅️ b.repr.toLinearEquiv.2 (lp.single 2 i 1) =?= b.repr.toLinearEquiv.2 (lp.single 2 i 1) | 0.118 | 0.118 | unattributed |
| Meta.check: ✅️ fun _a =>   (Cloning.PCTUnitaryTransport.unitaryChannel (Cloning.PCTUnitaryTransport.tensorUnitary (star U) L)).toLinearMap _a =     ↑(Cloning.PCTPhysicalState.frameState u z L) | 0.097 | 0.187 | unattributed |
| Elab.step: Lean.Parser.Tactic.rewriteSeq: rewrite [hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one] | 0.095 | 0.333 | unattributed |
| Meta.isDefEq: ✅️ ⋯.choose.repr.toLinearEquiv.2 (lp.single 2 i 1) =?= ⋯.choose.repr.toLinearEquiv.2 (lp.single 2 i 1) | 0.094 | 0.219 | unattributed |
| Elab.step: Lean.Parser.Tactic.rewriteSeq: rewrite [← frameState_transport, tensorUnitary_star, unitaryChannel_star] | 0.071 | 0.311 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 6.466 | 7.504 | unattributed |
| Elab.async: elaborating proof of Cloning.PCTUnitaryTransport.unitaryChannel_star | 0.003 | 0.465 | unattributed |
| Elab.definition.value: Cloning.PCTUnitaryTransport.unitaryChannel_star | 0.001 | 0.462 | Cloning.PCTUnitaryTransport.unitaryChannel_star at formalization/Cloning/PCTUnitaryTransportChannels.lean:23 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   rw [← Cloning.PCTGlobal.registerLiftCLM_matrixOf X, unitaryChannel_registerLift, unitaryChannel_registerLift]   have hU : (U : Matrix A A ℂ)ᴴ * U = 1 := Unitary.star_mul_self_of_mem U.property   simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose, Mat | 0.000 | 0.461 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   rw [← Cloning.PCTGlobal.registerLiftCLM_matrixOf X, unitaryChannel_registerLift, unitaryChannel_registerLift]   have hU : (U : Matrix A A ℂ)ᴴ * U = 1 := Unitary.star_mul_self_of_mem U.property   simp only [Unitary.coe_star, Matrix.star_eq_conjTrans | 0.000 | 0.461 | unattributed |
| Elab.command: Lean.Parser.Command.definition: /-- Postcompose a reverse mixed channel with an actual quantum channel. -/ def postQuantum {Ω H K J : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [NormedAddCommGroup H] [InnerProductSpace ℂ H]     [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpac | 0.008 | 0.406 | Cloning.PCTUnitaryTransport.postQuantum at formalization/Cloning/PCTUnitaryTransportChannels.lean:81 |
| Elab.definition.value: Cloning.PCTUnitaryTransport.postQuantum | 0.000 | 0.376 | Cloning.PCTUnitaryTransport.postQuantum at formalization/Cloning/PCTUnitaryTransportChannels.lean:81 |
| Elab.step: Lean.Parser.Term.structInst: expected type: Cloning.Hybrid.HybridToQuantum H J μ, term { map := M.toPositiveTracePreservingMap.toContinuousLinearMap.comp S.map,   completelyPositive := fun n X hX => M.completelyPositive n _ (S.completelyPositive n X hX),   tracePreserving := fun X => (M.t | 0.014 | 0.376 | unattributed |
| Elab.step: Lean.Parser.Tactic.rwSeq: rw [hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one] | 0.000 | 0.335 | unattributed |
| Elab.step: Lean.Parser.Tactic.paren: (rewrite [hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one]; with_annotate_state"]" (try (with_reducible rfl))) | 0.000 | 0.335 | unattributed |

Unattributed elaboration events above threshold: 2; the detailed trace rankings supply attribution where their labels identify declarations.

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.PCTUnitaryTransportChannels-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.PCTUnitaryTransportChannels-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.PCTUnitaryTransportChannels-1.setup.json Cloning/PCTUnitaryTransportChannels.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.InfiniteTraceClass — repetition 1

Recorded profile commit: `80e4b7ca1aa43969f85105171bfd80bf662d6b32`; source SHA-256: `8989a10ec2f035d84eeadeb1ab47af9dbbbb80ccbfcdf85f31577d3c5e55f3c9`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | cbb2fd2007ae367e201d4a6ac7c069899db90dbd |
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
| typeclass inference | 33.300 |
| import | 3.580 |
| tactic execution | 2.890 |
| type checking | 1.930 |
| interpretation | 1.730 |
| elaboration | 0.399 |
| simp | 0.116 |
| process pre-definitions | 0.067 |
| linting | 0.052 |
| instantiate metavars | 0.043 |
| share common exprs | 0.035 |
| initialization | 0.020 |
| parsing | 0.019 |
| fix level params | 0.012 |
| compilation (LCNF base) | 0.008 |
| compilation (LCNF impure) | 0.003 |
| congr simp thm | 0.003 |
| compilation (LCNF mono) | 0.002 |
| let-to-have transformation | 0.001 |
| compilation (IR) | 0.001 |
| attribute application | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| import took 3.58s | 3.580 | 1 |
| typeclass inference of PosPart took 377ms | 0.377 | 79 |
| typeclass inference of NegPart took 345ms | 0.345 | 43 |
| typeclass inference of NegPart took 308ms | 0.308 | 33 |
| typeclass inference of Algebra took 293ms | 0.293 | 27 |
| typeclass inference of PosPart took 288ms | 0.288 | 52 |
| typeclass inference of NegPart took 283ms | 0.283 | 82 |
| typeclass inference of AddLeftMono took 280ms | 0.280 | 36 |
| typeclass inference of CoeFun took 266ms | 0.266 | 73 |
| type checking took 263ms | 0.263 | 18 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 8.830 | 15.952 | unattributed |
| Meta.synthInstance: ✅️ Algebra ℝ (H →L[ℂ] H) | 6.014 | 13.872 | unattributed |
| Meta.isDefEq: ❌️ Complex.commRing.toSemiring =?= NormedField.toField.toSemiring | 1.544 | 3.415 | unattributed |
| Meta.synthInstance: ✅️ Algebra ℂ (H →L[ℂ] H) | 1.524 | 2.329 | unattributed |
| Meta.isDefEq: ❌️ Complex.commRing.toRing =?= NormedField.toField.toRing | 1.203 | 1.870 | unattributed |
| Meta.synthInstance: ✅️ Module ℂ (H →L[ℂ] H) | 1.038 | 1.568 | unattributed |
| Meta.synthInstance: ✅️ Module ℝ (H →L[ℂ] H) | 1.010 | 1.872 | unattributed |
| Meta.isDefEq: ❌️ Real.commRing.toSemiring =?= NormedField.toField.toSemiring | 0.890 | 1.552 | unattributed |
| Meta.check: ✅️ ContinuousLinearMap.algebra | 0.740 | 0.740 | unattributed |
| Meta.check: ✅️ IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus | 0.735 | 0.766 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 8.830 | 15.952 | unattributed |
| Meta.synthInstance: ✅️ Algebra ℝ (H →L[ℂ] H) | 6.014 | 13.872 | unattributed |
| Elab.step: Lean.Parser.Term.paren: expected type: <not-available>, term (⟪b i, CFC.abs T (b i)⟫_ℂ) | 0.000 | 9.355 | unattributed |
| Elab.step: InnerProductSpace.«term⟪_,_⟫__»: expected type: <not-available>, term ⟪b i, CFC.abs T (b i)⟫_ℂ | 0.001 | 9.355 | unattributed |
| Elab.step: Lean.Parser.Term.app: expected type: <not-available>, term inner✝ ℂ (b i) (CFC.abs T (b i)) | 0.012 | 9.355 | unattributed |
| Elab.step: Lean.Parser.Term.app: expected type: H, term CFC.abs T (b i) | 0.378 | 9.343 | unattributed |
| Meta.synthInstance: ✅️ apply @Algebra.to_smulCommClass to SMulCommClass ℝ (H →L[ℂ] H) (H →L[ℂ] H) | 0.002 | 8.717 | unattributed |
| Meta.synthInstance.tryResolve: ✅️ SMulCommClass ℝ (H →L[ℂ] H) (H →L[ℂ] H) ≟ SMulCommClass ℝ (H →L[ℂ] H) (H →L[ℂ] H) | 0.061 | 8.715 | unattributed |
| Elab.step: Lean.Parser.Term.proj: expected type: ℝ, term (⟪b i, CFC.abs T (b i)⟫_ℂ).re | 0.000 | 7.857 | unattributed |
| Meta.synthInstance: ✅️ SMulCommClass ℝ (H →L[ℂ] H) (H →L[ℂ] H) | 0.084 | 6.082 | unattributed |

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.InfiniteTraceClass-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.InfiniteTraceClass-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.InfiniteTraceClass-1.setup.json Cloning/InfiniteTraceClass.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.Thermal — repetition 1

Recorded profile commit: `80e4b7ca1aa43969f85105171bfd80bf662d6b32`; source SHA-256: `d3dc50c83b60b9e7a734b11aed79064d33bbdf3b44b9b210f093f1c94e0b9a91`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | cbb2fd2007ae367e201d4a6ac7c069899db90dbd |
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
| interpretation | 4.060 |
| typeclass inference | 3.930 |
| import | 2.740 |
| tactic execution | 0.793 |
| simp | 0.782 |
| ring | 0.379 |
| type checking | 0.343 |
| elaboration | 0.232 |
| linting | 0.104 |
| norm_num | 0.096 |
| share common exprs | 0.056 |
| process pre-definitions | 0.041 |
| parsing | 0.026 |
| initialization | 0.020 |
| instantiate metavars | 0.016 |
| congr simp thm | 0.006 |
| fix level params | 0.005 |
| compilation (LCNF base) | 0.004 |
| compilation (LCNF mono) | 0.003 |
| let-to-have transformation | 0.002 |
| compilation (LCNF impure) | 0.001 |
| compilation (IR) | 0.001 |
| attribute application | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| import took 2.74s | 2.740 | 1 |
| interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 440ms | 0.440 | 6 |
| interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 395ms | 0.395 | 2 |
| interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 253ms | 0.253 | 3 |
| interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 211ms | 0.211 | 7 |
| interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 197ms | 0.197 | 5 |
| interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 165ms | 0.165 | 4 |
| simp took 104ms | 0.104 | 8 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 4.552 | 4.683 | unattributed |
| linarith: ✅️ adding product terms | 1.424 | 1.818 | unattributed |
| linarith: ✅️ running on preferred type ℝ | 0.644 | 1.927 | unattributed |
| Elab.step: Mathlib.Tactic.Ring.ring1: ring1 | 0.593 | 0.593 | unattributed |
| linarith.detail: ✅️ linearFormsAndMaxVar | 0.420 | 0.420 | unattributed |
| Meta.synthInstance: ❌️ Nonempty (Fin s) | 0.385 | 0.405 | unattributed |
| linarith: ✅️ Invoking oracle | 0.367 | 0.367 | unattributed |
| Elab.lint: running linters | 0.274 | 0.306 | unattributed |
| Elab.step: Mathlib.Tactic.linarith: linarith | 0.185 | 1.000 | unattributed |
| linarith: ✅️ Running preprocessors | 0.170 | 2.216 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 4.552 | 4.683 | unattributed |
| linarith: ✅️ Running preprocessors | 0.170 | 2.216 | unattributed |
| linarith: ✅️ Mathlib.Tactic.Linarith.nlinarithExtras: nonlinear arithmetic extras | 0.050 | 1.942 | unattributed |
| linarith: ✅️ running on preferred type ℝ | 0.644 | 1.927 | unattributed |
| linarith: ✅️ adding product terms | 1.424 | 1.818 | unattributed |
| Elab.step: Mathlib.Tactic.nlinarith: nlinarith | 0.049 | 1.545 | unattributed |
| Elab.async: elaborating proof of Cloning.Thermal.fidelity_le_one | 0.006 | 1.074 | unattributed |
| Elab.definition.value: Cloning.Thermal.fidelity_le_one | 0.003 | 1.067 | Cloning.Thermal.fidelity_le_one at formalization/Cloning/Thermal.lean:93 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   have hprod : q * x < 1 := mul_lt_one_of_nonneg_of_lt_one_right hq1.le hx0 hx1   have hsqrt : Real.sqrt q * Real.sqrt x < 1 :=     by     rw [← Real.sqrt_mul hq0, Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]     simpa using hprod   have hsq : (Real.sqrt q * Re | 0.000 | 1.064 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   have hprod : q * x < 1 := mul_lt_one_of_nonneg_of_lt_one_right hq1.le hx0 hx1   have hsqrt : Real.sqrt q * Real.sqrt x < 1 :=     by     rw [← Real.sqrt_mul hq0, Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]     simpa using hprod   have hsq : (Real.sq | 0.014 | 1.064 | unattributed |

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.Thermal-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.Thermal-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.Thermal-1.setup.json Cloning/Thermal.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.AmplifierWeylThermal — repetition 1

Recorded profile commit: `80e4b7ca1aa43969f85105171bfd80bf662d6b32`; source SHA-256: `eeee0e083b71ae3155a11fc033a5cd888fcac86911f4ed7cfe97ab77fce4760b`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | cbb2fd2007ae367e201d4a6ac7c069899db90dbd |
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
| Imported compacted-region bytes (not RSS) | 4029005856 |
| Imported compacted regions (Lean labels these modules) | 20237 |
| Memory-mapped compacted regions | 20148 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| import | 4.620 |
| typeclass inference | 1.510 |
| interpretation | 0.951 |
| tactic execution | 0.387 |
| type checking | 0.104 |
| elaboration | 0.077 |
| ring | 0.037 |
| norm_num | 0.032 |
| initialization | 0.024 |
| simp | 0.019 |
| linting | 0.009 |
| share common exprs | 0.008 |
| instantiate metavars | 0.007 |
| process pre-definitions | 0.006 |
| parsing | 0.004 |
| congr simp thm | 0.002 |
| dsimp | 0.001 |
| fix level params | 0.001 |
| let-to-have transformation | 0.000 |
| attribute application | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| import took 4.62s | 4.620 | 1 |
| tactic execution of Lean.Parser.Tactic.rewriteSeq took 189ms | 0.189 | 5 |
| typeclass inference of CoeFun took 174ms | 0.174 | 6 |
| typeclass inference of CoeFun took 173ms | 0.173 | 7 |
| typeclass inference of CoeFun took 155ms | 0.155 | 4 |
| typeclass inference of CoeFun took 149ms | 0.149 | 2 |
| typeclass inference of CoeFun took 145ms | 0.145 | 3 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 5.798 | 6.636 | unattributed |
| Meta.isDefEq.delta: ✅️ SetLike.instMembership =?= SetLike.instMembership | 0.263 | 0.483 | unattributed |
| Elab.lint: running linters | 0.164 | 0.164 | unattributed |
| Elab.step: Lean.Parser.Tactic.rewriteSeq: rewrite [hm, map_smul, smul_eq_mul, vacuumProjector_characteristic,   show Φ.toLinearMap (coherentProjector 0) = vectorMixture (numberBasis d) (productGeometric (fun _ => 1 - 1 / g)) from     gainChannel_vacuum g hg,   productThermal_characteristic (fun _ => | 0.101 | 0.421 | unattributed |
| Meta.isDefEq.delta: ✅️ Submodule.setLike =?= Submodule.setLike | 0.084 | 0.104 | unattributed |
| Meta.isDefEq: ✅️ Submodule ℂ   (↥(Cloning.MultimodeCoherent.Fock ?m.15) →L[ℂ]     ↥(Cloning.MultimodeCoherent.Fock         ?m.15)) =?= Submodule ℂ (↥(Cloning.MultimodeCoherent.Fock ?m.15) →L[ℂ] ↥(Cloning.MultimodeCoherent.Fock ?m.15)) | 0.076 | 0.107 | unattributed |
| Meta.isDefEq: ✅️ Submodule ℂ   (↥(Cloning.MultimodeCoherent.Fock ?m.123) →L[ℂ]     ↥(Cloning.MultimodeCoherent.Fock         ?m.123)) =?= Submodule ℂ   (↥(Cloning.MultimodeCoherent.Fock ?m.123) →L[ℂ] ↥(Cloning.MultimodeCoherent.Fock ?m.123)) | 0.075 | 0.106 | unattributed |
| linarith: ✅️ Mathlib.Tactic.Linarith.cancelDenoms: cancel denominators | 0.073 | 0.073 | unattributed |
| Meta.check: ✅️ DFunLike.hasCoeToFun | 0.069 | 0.664 | unattributed |
| Elab.step: Mathlib.Tactic.linarith: linarith | 0.053 | 0.242 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 5.798 | 6.636 | unattributed |
| Elab.async: elaborating proof of Cloning.MultimodeAmplifier.gainChannel_weylMultiplier | 0.007 | 0.776 | unattributed |
| Elab.definition.value: Cloning.MultimodeAmplifier.gainChannel_weylMultiplier | 0.007 | 0.769 | Cloning.MultimodeAmplifier.gainChannel_weylMultiplier at formalization/Cloning/AmplifierWeylThermal.lean:49 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   let Φ := gainChannel (d := d) g hg   have hcov := gainChannel_covariant (d := d) g hg   have hm := (quantumChannel_weyl_multiplier Φ (Real.sqrt g) hcov).1 a   have hv :=     heisenbergDual_pairing Φ.toPositiveTracePreservingMap.toContinuousLinearMap (cohere | 0.000 | 0.763 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   let Φ := gainChannel (d := d) g hg   have hcov := gainChannel_covariant (d := d) g hg   have hm := (quantumChannel_weyl_multiplier Φ (Real.sqrt g) hcov).1 a   have hv :=     heisenbergDual_pairing Φ.toPositiveTracePreservingMap.toContinuousLinearMa | 0.043 | 0.763 | unattributed |
| Meta.isDefEq: ✅️ NormedAddCommGroup.toENormedAddCommMonoid.toAddCommMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddCommMonoid | 0.001 | 0.753 | unattributed |
| Meta.isDefEq: ✅️ { toAddMonoid := NormedAddCommGroup.toENormedAddCommMonoid.toAddMonoid,   add_comm :=     ⋯ } =?= { toAddMonoid := Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddMonoid, add_comm := ⋯ } | 0.003 | 0.753 | unattributed |
| Meta.isDefEq: ✅️ NormedAddCommGroup.toENormedAddCommMonoid.toAddMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddMonoid | 0.001 | 0.750 | unattributed |
| Meta.isDefEq: ✅️ NormedAddCommGroup.toNormedAddGroup.toAddMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddMonoid | 0.001 | 0.749 | unattributed |
| Meta.isDefEq.delta: ✅️ NormedAddCommGroup.toNormedAddGroup.toAddMonoid =?= Cloning.InfiniteTraceClass.TraceClass.instAddCommGroup.toAddMonoid | 0.003 | 0.749 | unattributed |

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.AmplifierWeylThermal-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.AmplifierWeylThermal-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.AmplifierWeylThermal-1.setup.json Cloning/AmplifierWeylThermal.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.PCTClosedForm — repetition 1

Recorded profile commit: `80e4b7ca1aa43969f85105171bfd80bf662d6b32`; source SHA-256: `a237c4cbc91c79ac818a1a4b7ca3c4445c8e4eba19dd333600b7d727e219c846`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | cbb2fd2007ae367e201d4a6ac7c069899db90dbd |
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
| Memory-mapped compacted regions | 17979 |
| Import trust level | 1025 |

| Exclusive elapsed phase | Seconds |
| --- | --- |
| import | 3.200 |
| interpretation | 1.330 |
| typeclass inference | 0.400 |
| tactic execution | 0.136 |
| ring | 0.041 |
| type checking | 0.040 |
| simp | 0.030 |
| initialization | 0.020 |
| elaboration | 0.017 |
| linting | 0.013 |
| norm_num | 0.009 |
| share common exprs | 0.009 |
| process pre-definitions | 0.005 |
| instantiate metavars | 0.004 |
| parsing | 0.002 |
| fix level params | 0.001 |
| congr simp thm | 0.000 |
| let-to-have transformation | 0.000 |
| attribute application | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| import took 3.2s | 3.200 | 1 |
| interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 314ms | 0.314 | 5 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 4.367 | 4.382 | unattributed |
| linarith: ✅️ adding product terms | 0.233 | 0.233 | unattributed |
| Elab.lint: running linters | 0.171 | 0.171 | unattributed |
| linarith.detail: ✅️ linearFormsAndMaxVar | 0.107 | 0.107 | unattributed |
| Tactic.field_simp: ✅️ discharge √(g + q * (g - 1)) ≠ 0 | 0.092 | 0.092 | unattributed |
| linarith: ✅️ Invoking oracle | 0.090 | 0.090 | unattributed |
| linarith: ✅️ running on preferred type ℝ | 0.069 | 0.300 | unattributed |
| Elab.step: Mathlib.Tactic.linarith: linarith | 0.060 | 0.127 | unattributed |
| Tactic.field_simp: ✅️ discharge g + q * (g - 1) ≠ 0 | 0.052 | 0.052 | unattributed |
| Elab.step: Mathlib.Tactic.Positivity.positivity: positivity | 0.050 | 0.050 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 4.367 | 4.382 | unattributed |
| Elab.async: elaborating proof of Cloning.Thermal.fidelity_pct_closedForm | 0.005 | 0.633 | unattributed |
| Elab.definition.value: Cloning.Thermal.fidelity_pct_closedForm | 0.005 | 0.628 | Cloning.Thermal.fidelity_pct_closedForm at formalization/Cloning/PCTClosedForm.lean:33 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   have hg0 : 0 < g := by linarith   have hg1 : 0 ≤ g - 1 := by linarith   have hrad : 0 ≤ q * (g - 1 + g * q) := mul_nonneg hq0 (add_nonneg hg1 (mul_nonneg hg0.le hq0))   have hdpos : 0 < g + (g - 1) * q := add_pos_of_pos_of_nonneg hg0 (mul_nonneg hg1 hq0)    | 0.000 | 0.624 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   have hg0 : 0 < g := by linarith   have hg1 : 0 ≤ g - 1 := by linarith   have hrad : 0 ≤ q * (g - 1 + g * q) := mul_nonneg hq0 (add_nonneg hg1 (mul_nonneg hg0.le hq0))   have hdpos : 0 < g + (g - 1) * q := add_pos_of_pos_of_nonneg hg0 (mul_nonneg hg | 0.014 | 0.624 | unattributed |
| Elab.step: Mathlib.Tactic.nlinarith: nlinarith [Real.sq_sqrt hdpos.le, Real.sq_sqrt hrad] | 0.002 | 0.408 | unattributed |
| Elab.async: elaborating proof of Cloning.Thermal.fidelity_pct_unrationalized | 0.008 | 0.404 | unattributed |
| Elab.definition.value: Cloning.Thermal.fidelity_pct_unrationalized | 0.004 | 0.396 | Cloning.Thermal.fidelity_pct_unrationalized at formalization/Cloning/PCTClosedForm.lean:8 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   have hg0 : 0 < g := by linarith   have hg1 : 0 ≤ g - 1 := by linarith   have hdpos : 0 < g + (g - 1) * q := add_pos_of_pos_of_nonneg hg0 (mul_nonneg hg1 hq0)   have hd : g + (g - 1) * q ≠ 0 := hdpos.ne'   have hs : Real.sqrt (g + (g - 1) * q) ≠ 0 := (Real.s | 0.000 | 0.392 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   have hg0 : 0 < g := by linarith   have hg1 : 0 ≤ g - 1 := by linarith   have hdpos : 0 < g + (g - 1) * q := add_pos_of_pos_of_nonneg hg0 (mul_nonneg hg1 hq0)   have hd : g + (g - 1) * q ≠ 0 := hdpos.ne'   have hs : Real.sqrt (g + (g - 1) * q) ≠ 0 : | 0.020 | 0.392 | unattributed |

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.PCTClosedForm-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.PCTClosedForm-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.PCTClosedForm-1.setup.json Cloning/PCTClosedForm.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

### Cloning.CloningValueComparisonMonotone — repetition 1

Recorded profile commit: `80e4b7ca1aa43969f85105171bfd80bf662d6b32`; source SHA-256: `0dbf7031761a5f1b7e1352befdb6a4284734445e63799b3726977bb7c8312551`.

| Profile provenance | Recorded result |
| --- | --- |
| Benchmark commit | cbb2fd2007ae367e201d4a6ac7c069899db90dbd |
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
| interpretation | 3.280 |
| import | 3.220 |
| typeclass inference | 0.417 |
| tactic execution | 0.101 |
| type checking | 0.067 |
| ring | 0.065 |
| elaboration | 0.030 |
| initialization | 0.021 |
| linting | 0.020 |
| share common exprs | 0.011 |
| instantiate metavars | 0.011 |
| process pre-definitions | 0.008 |
| norm_num | 0.007 |
| simp | 0.006 |
| parsing | 0.004 |
| fix level params | 0.001 |
| congr simp thm | 0.000 |
| let-to-have transformation | 0.000 |
| attribute application | 0.000 |

| Largest event (>100 ms) | Exclusive seconds | Log line |
| --- | --- | --- |
| import took 3.22s | 3.220 | 1 |
| interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 1.2s | 1.200 | 2 |
| interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 1.13s | 1.130 | 3 |

Largest self trace labels:

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 6.713 | 6.739 | unattributed |
| linarith.detail: ✅️ linearFormsAndMaxVar | 1.259 | 1.324 | unattributed |
| linarith: ✅️ Invoking oracle | 0.567 | 0.567 | unattributed |
| linarith: ✅️ adding product terms | 0.454 | 0.454 | unattributed |
| Elab.lint: running linters | 0.122 | 0.135 | unattributed |
| linarith: ✅️ running on preferred type ℝ | 0.118 | 2.118 | unattributed |
| Elab.step: Mathlib.Tactic.linarith: linarith | 0.078 | 0.201 | unattributed |
| Elab.step: Mathlib.Tactic.Positivity.positivity: positivity | 0.068 | 0.068 | unattributed |
| Elab.step: Mathlib.Tactic.Ring.ring1: ring1 | 0.065 | 0.065 | unattributed |
| Elab.step: Mathlib.Tactic.FieldSimp.fieldSimp: field_simp [hr0, hs0, hden, hsum] | 0.057 | 0.084 | unattributed |

Largest inclusive trace labels (overlap):

| Trace label (first 300 characters) | Self s | Inclusive s | Declaration pointer |
| --- | --- | --- | --- |
| runFrontend:  | 6.713 | 6.739 | unattributed |
| Elab.async: elaborating proof of Cloning.ValueComparison.modeFactor_hasDerivAt | 0.017 | 2.931 | unattributed |
| Elab.definition.value: Cloning.ValueComparison.modeFactor_hasDerivAt | 0.004 | 2.915 | Cloning.ValueComparison.modeFactor_hasDerivAt at formalization/Cloning/CloningValueComparisonMonotone.lean:14 |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   have hg0 : 0 < g := by linarith   have hv : 0 < g - 1 + q := by linarith   have hrad : 0 < q * (g - 1 + q) := mul_pos hq hv   have hden : g + q ≠ 0 := ne_of_gt (add_pos hg0 hq)   have hd :=     (((hasDerivAt_const q (Real.sqrt g)).add           (((hasDerivA | 0.000 | 2.900 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   have hg0 : 0 < g := by linarith   have hv : 0 < g - 1 + q := by linarith   have hrad : 0 < q * (g - 1 + q) := mul_pos hq hv   have hden : g + q ≠ 0 := ne_of_gt (add_pos hg0 hq)   have hd :=     (((hasDerivAt_const q (Real.sqrt g)).add           ((( | 0.044 | 2.900 | unattributed |
| linarith: ✅️ running on preferred type ℝ | 0.118 | 2.118 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticHave__: have hnum :   (g - 1 + q + q) * (g + q) -       2 * Real.sqrt q * Real.sqrt (g - 1 + q) * (Real.sqrt g + Real.sqrt q * Real.sqrt (g - 1 + q)) =     (Real.sqrt g * Real.sqrt (g - 1 + q) - Real.sqrt q) ^ 2 :=   by nlinarith [htsq, hrsq] | 0.000 | 1.339 | unattributed |
| Elab.step: Lean.Parser.Tactic.focus: focus   refine     no_implicit_lambda%       (have hnum :         (g - 1 + q + q) * (g + q) -             2 * Real.sqrt q * Real.sqrt (g - 1 + q) * (Real.sqrt g + Real.sqrt q * Real.sqrt (g - 1 + q)) =           (Real.sqrt g * Real.sqrt (g - 1 + q) - Real.sqrt q) | 0.000 | 1.339 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq:   refine     no_implicit_lambda%       (have hnum :         (g - 1 + q + q) * (g + q) -             2 * Real.sqrt q * Real.sqrt (g - 1 + q) * (Real.sqrt g + Real.sqrt q * Real.sqrt (g - 1 + q)) =           (Real.sqrt g * Real.sqrt (g - 1 + q) - Real.sqrt q) ^ | 0.000 | 1.339 | unattributed |
| Elab.step: Lean.Parser.Tactic.tacticSeq1Indented:   refine     no_implicit_lambda%       (have hnum :         (g - 1 + q + q) * (g + q) -             2 * Real.sqrt q * Real.sqrt (g - 1 + q) * (Real.sqrt g + Real.sqrt q * Real.sqrt (g - 1 + q)) =           (Real.sqrt g * Real.sqrt (g - 1 + q) - Real. | 0.007 | 1.339 | unattributed |

Recorded command:

```sh
/opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.CloningValueComparisonMonotone-1.resources.txt /Users/jw/.elan/bin/lake env lean -DautoImplicit=false --profile --stats -Dtrace.profiler=true -Dtrace.profiler.output.pp=true -Dtrace.profiler.output=/Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.CloningValueComparisonMonotone-1.json --setup /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/profiles-before/Cloning.CloningValueComparisonMonotone-1.setup.json Cloning/CloningValueComparisonMonotone.lean
```

- This Lean exporter provides no source positions; pointers identify declarations only.

## 8. Findings ranked by actionability

The dead-code sweep preceded this measurement. Its six-line private theorem removal is not credited as an elaboration improvement. All public theorem statements and result indices were retained.

The complete project-only build compiled all 994 owned modules with zero errors, zero sorry messages, no upstream compilations, and unchanged dependency artifact metadata. The measured proof/config commit is cbb2fd2007ae367e201d4a6ac7c069899db90dbd. Its source/config manifest was additionally checked after completion; this baseline runner did not contain the later built-in end check, so the supplemental check is labeled separately.

The ten serial warm profiles cover the five worst cold jobs and five additional candidates. All ten have successful exits and stable source/config/setup/import inputs, matching the baseline proof/config bytes. Long cold jobs often shrink when profiled alone: PCTUnitaryTransportChannels took 171 s cold versus 10.06 s in the instrumented warm run. This is a reason to profile before changing proofs, not an optimization result.

WeylIdlerUniqueness contains a 103 s `change` event; its cumulative tactic phase is 105 s. The hash-bound trace and source identify a conversion between vectorProjector and rankOneOperator under tracePairing. A nearby provider already uses an explicit equality between those operators. This is a candidate for a controlled proof-body experiment; no performance edit is included in this baseline.

WernerPhysicalPullback also contains a costly `change` event, and PCTHybridMixtureFactor has an elaboration-heavy profile. Each needs separate attribution and measurement. No head-class cache, simp sweep, broad module-header migration, or import split is justified by resemblance alone. Thermal and PCTClosedForm have warm import phases below the skill's 5 s action floor, so the earlier static import/module-boundary suggestions are not validated optimization claims.

These warm runs use `--profile --stats` plus Firefox traces with message pretty-printing enabled. Pinned Lean waits for elaboration, displays statistics, then formats/exports the trace, and only afterward prints cumulative C++ profiling totals. Whole-process GNU CPU/wall and cumulative interpretation totals can therefore include diagnostic formatting. Firefox elapsed slices are captured before exporter formatting; they are elapsed measurements, not OS CPU samples. Exact source positions are absent in this export: source pointers identify hash-bound declarations, and line-level attribution requires an additional source inspection or controlled diagnostic. Subsequent A/B experiments must match their own flags and confirm real compiler savings with paired bare GNU-time runs.

Primary-source timing references: [Frontend](https://github.com/leanprover/lean4/blob/00659f8e6071d7e46131ed643bf8003b99b044e9/src/Lean/Elab/Frontend.lean), [Shell](https://github.com/leanprover/lean4/blob/00659f8e6071d7e46131ed643bf8003b99b044e9/src/Lean/Shell.lean), and [Profiler](https://github.com/leanprover/lean4/blob/00659f8e6071d7e46131ed643bf8003b99b044e9/src/Lean/Util/Profiler.lean).

Other projects ran on this shared host during the cold build. The inventory is descriptive; it does not prove a cause for a particular duration or mutation of this project's inputs. Wall-time differences between full snapshots must not be presented as causal cleanup gains without additional evidence. Peak GNU RSS is a maximum process peak, not simultaneous aggregate memory. The existing legacy module mode is preserved: the missing-modern-header census is reported explicitly rather than forcing an unmeasured API migration.

## 9. What is not established

Logged job durations do not establish per-file CPU, exclusive elaboration cost, or a cleanup speedup. The global process inventory does not establish contention causality. Peak process RSS does not establish aggregate memory demand. The weighted import chain and CPU/core references are scheduling models, not measured critical-path bounds. Missing profiles leave tail causes unclassified; large unattributed elaboration requires detailed trace attribution. The legacy module-header exception is an explicit adaptation, not satisfaction of the skill's zero-header-deficit rule. Successful elaboration does not by itself refresh the independent comparator/nanoda certificates or their historical pins.

## 10. Methodology

Recorded timed command (working directory: `formalization`):

```sh
LAKE_ARTIFACT_CACHE=false LEAN_NUM_THREADS=2 /opt/homebrew/bin/gtime -v -o /Users/jw/.codex/.chatgpt-projects/g-p-6abc3124021c8191aa9668c86db9f180/Cloning-github/.verify-work/elaboration-campaign/before/resources.txt /Users/jw/.elan/bin/lake --no-ansi --no-cache build All
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

Measurement directory: [formalization/verification/elaboration/2026-10-06/before](formalization/verification/elaboration/2026-10-06/before). No prior benchmark supplied.

| Evidence file | SHA-256 |
| --- | --- |
| [summary.json](formalization/verification/elaboration/2026-10-06/before/summary.json) | fd95b6cbd6fc4a87bc79a80fdad990127633e84b37f63cc86ee69e1586049899 |
| [size.json](formalization/verification/elaboration/2026-10-06/before/size.json) | 715a283ad190ae152ca55577b2feb022fc9e80ef5d5f8621b6cb638d0ff22978 |
| [imports.json](formalization/verification/elaboration/2026-10-06/before/imports.json) | f70c604535acac8784947f57a609d73878dae14b050c4c5c51524877930812d0 |
| [skill-size.txt](formalization/verification/elaboration/2026-10-06/before/skill-size.txt) | 71dee55ba87e62aab647f613a9f3d274fd70273710c253cab841c069a5373332 |
| [build.log](formalization/verification/elaboration/2026-10-06/before/build.log) | c762ee058367e834bed8e9dc0e823eb4c18a992cfe4f92da32c11553b75b1027 |
| [resources.txt](formalization/verification/elaboration/2026-10-06/before/resources.txt) | e659577203a340e0a368b34dc4ccca2caf9e4c0d86435ae54f1c005098f37389 |
| [process-inventory.json](formalization/verification/elaboration/2026-10-06/before/process-inventory.json) | db1f32ecb9420d1330a3eddc69ab3f31b023fd107447285ff62eb6a61f9ae244 |
| [dependencies-before.json](formalization/verification/elaboration/2026-10-06/before/dependencies-before.json) | 07231494c7ecd316c52ccba38d8e1641671b844bfbb3f5a5f3a53dd61ec64c32 |
| [dependencies-after.json](formalization/verification/elaboration/2026-10-06/before/dependencies-after.json) | 07231494c7ecd316c52ccba38d8e1641671b844bfbb3f5a5f3a53dd61ec64c32 |
| [invalidated.json](formalization/verification/elaboration/2026-10-06/before/invalidated.json) | f47ababe2ee193656086168e6f054ef070be04bc7cb08fcfbd94b97af3ced766 |
| [source-config-hashes.json](formalization/verification/elaboration/2026-10-06/before/source-config-hashes.json) | f36cc5652fdc00f468e85d3dec114a623dffdba585e8aab7987416774c93db12 |
| [source-config-stability.json](formalization/verification/elaboration/2026-10-06/before/source-config-stability.json) | 73b1ae5e2cbb3a28facc902999db5d8f76544f38c6b5dcb2c7d00983150cb3ce |
| [benchmark-runner.py](formalization/verification/elaboration/2026-10-06/before/benchmark-runner.py) | 389d4a148f7f46dd41372d014d051c7e31f0f3600b084a4687d15381fcc1f5e5 |
| process-samples.json (omitted original; counts published separately) | 311d6c2405a94b77170019e73380e4a831fd9f39bd3208206ed17a1dacc77228 |

Profile summary: [formalization/verification/elaboration/2026-10-06/profiles-before/summary.json](formalization/verification/elaboration/2026-10-06/profiles-before/summary.json); SHA-256: `8df20401606958b10d1a1f7d9b4dc17b2eec7271d339b4e1d32e333ca8978fca`. Its per-profile input hashes bind the raw text and trace evidence.
