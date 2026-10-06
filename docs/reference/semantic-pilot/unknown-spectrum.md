# Unknown-spectrum semantic statement pilot

No mismatch was found in the reviewed statement, definition, and immediate proof-composition scope for paper Theorem 1.2(a),(b). This is a bounded semantic review of three actual exports, not a fresh review of every analytic proof or an independent kernel-checker run.

The review was reconstructed from the frozen manuscript before consulting Lean endpoints or earlier review prose. It applies the semantic and binder checks from the [lean-statement-audit checklist](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/main/skills/lean-statement-audit/SKILL.md), adapted to existing compiled project sources. It does not reproduce that skill's text or its separate draft-authoring workflow.

## Source claim reconstructed first

[Theorem 1.2](https://arxiv.org/html/2609.35986v1#S1.Thmtheorem2), frozen source lines 321–351, uses the standing [§1.1 conventions](https://arxiv.org/html/2609.35986v1#S1.SS1) at lines 163–205. Write physical dimension as **D** to distinguish it from the Lean endpoint's **d=D−1**:

- D is an integer at least 2; positive integers m_n satisfy m_n/n → γ>1.
- A_D is the full real trace-one affine hyperplane. The parameter chamber is p_1>…>p_D>0 with sum 1.
- ρ_{p,U}=U diag(p) U*, and the target is the entire m_n-fold tensor product.
- Fidelity is the unsquared quantity ||sqrt(A)sqrt(B)||_1, including unnormalized positive trace-class operators.
- F_univ(γ,p)=(2sqrt(γ)/(1+γ))^((D−1)/2) times the product over i<j of (sqrt(γ)+sqrt(q_ij(γ−1+q_ij)))/(γ+q_ij), where q_ij=p_j/p_i.

The theorem supplies one spectrum-independent U(D)-covariant channel sequence, specifically the randomized Young-label cloner in [§2.1](https://arxiv.org/html/2609.35986v1#S2.SS1) (source lines 1000–1047). At exceptional m_n≤n it uses exact partial trace, including identity at equality (lines 167–170).

Part (a) evaluates this prescribed sequence: for **every compact K** in the simple full-rank chamber the absolute fidelity error tends uniformly to zero over p∈K and U∈U(D). It does not optimize separately at each p. There is no nonempty or regular-closure premise; singleton and lower-dimensional compact families are explicitly included by the remarks at lines 355–363.

Part (b) requires **nonempty compact K**, with K equal to the closure of its interior in the **full A_D**. The competing channel is selected before p,U: it may depend on K and n, but not on the actual p or eigenbasis. The supremum over all quantum channels of the worst-case fidelity converges to inf_{p∈K} F_univ(γ,p). This is not the singleton optimum and does not assert all-density minimax optimality.

The unknown-spectrum [achievability argument](https://arxiv.org/html/2609.35986v1#S2.SS3), lines 1274–1293, combines sector fidelity, Young concentration, and rounded label affinity. The [converse argument](https://arxiv.org/html/2609.35986v1#S3.SS3), lines 1770–1797, takes interior base spectra, embeds full local spectral-and-orbital windows inside K, uses mixed LAN and the unrestricted hybrid optimum, then extends by continuity to the regular-closure boundary.

## Actual export and binder inventory

SOURCE means an explicit source condition or the epsilon formulation of its asserted convergence. STANDING means a source-wide convention. TYPING means a carrier/representation choice or a universally quantified argument used to express the claim. EXCESS would mark an additional mathematical premise; none was found. No author ruling is needed.

The compiled telescope is printed in [unknown-spectrum.log](unknown-spectrum.log). The table counts every outer binder of the three actual exports; the two implicit dimension binders are included. There are **zero instance binders** in their compiled types. Finite index/Hilbert/topological instances are fixed implementations of these carriers, not caller-supplied analytic assumptions.

### Part (a): eventually_uniform_prescribedUniversalChannel_payoff

Actual source: [TensorCloningPrescribedLimits.lean:40](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/TensorCloningPrescribedLimits.lean#L40). Ten binders: SOURCE 4, STANDING 5, TYPING 1, EXCESS 0.

| Binder | Form | Classification | Source correspondence |
| --- | --- | --- | --- |
| d : ℕ | implicit | TYPING | Physical D=d+1; natural dimension carrier. |
| hd : 1≤d | explicit | STANDING | D≥2, paper line 163; endpoint line 40. |
| K : Set (SimpleSpectrum (d+1)) | explicit | SOURCE | Spectral family in part (a), line 327; endpoint line 41. |
| hK : IsCompact K | explicit | SOURCE | Compactness at line 327; endpoint line 41. |
| m : ℕ→ℕ | explicit | STANDING | Output size sequence, lines 163–170; endpoint line 42. |
| γ : ℝ | explicit | STANDING | Fixed limiting gain, lines 163–165; endpoint line 42. |
| hγ : 1<γ | explicit | STANDING | Expanding regime, line 165; endpoint line 42. |
| hgain : Tendsto (fun n => (m n:ℝ)/n) atTop (𝓝 γ) | explicit | STANDING | Exact gain limit, line 165; endpoint line 43. |
| ε : ℝ | explicit | SOURCE | Epsilon form of the uniform zero-error limit, lines 329–336; endpoint line 43. |
| hε : 0<ε | explicit | SOURCE | Positive tolerance in that same formulation; endpoint line 43. |

The conclusion's eventual n, p, membership proof p∈K, and U are the source's sample index and uniform parameter quantifiers (lines 329–336; endpoint line 44). They are not extra hypotheses. The selected channel `prescribedUniversalChannel n (m n) d` has no p,K,U,γ argument. The same channel is used across every compact K and every p,U at each n. A compiled singleton application in the probe checks that part (a) needs only `isCompact_singleton`.

The use of ℕ permits n=0 and finitely many m_n=0, whereas the paper begins with positive output sizes and the n→∞ sequence. This is a **broader domain**, not a restriction on any paper sequence. Gain γ>1 proves n<m_n eventually ([TensorCloningPrescribedLimits.lean:15](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/TensorCloningPrescribedLimits.lean#L15)), so the extension has no effect on the asserted limit. The paper's early-size convention is implemented exactly. A theorem stated as an eventual uniform epsilon bound expresses the source's uniform convergence without introducing a pointwise-channel optimization.

### Covariance: prescribedUniversalChannel_covariant

Actual source: [TensorCloningPrescribed.lean:70](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/TensorCloningPrescribed.lean#L70). Six explicit binders: SOURCE 0, STANDING 2, TYPING 4, EXCESS 0.

| Binder | Classification | Source correspondence |
| --- | --- | --- |
| n : ℕ | STANDING | Input sample size; line 70. |
| m : ℕ | STANDING | Output sample size; line 70. |
| d : ℕ | TYPING | Physical dimension D=d+1; line 70. |
| U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ | TYPING | Matrix representative of U(D); line 71. |
| hU : Uᴴ*U=1 | TYPING | Exact finite-square-matrix unitarity condition; line 71. |
| X : TraceClass (TensorRegister n (Fin (d+1))) | TYPING | Arbitrary operator on the physical input register; line 72. |

In finite equal dimensions U*U=I is the source unitary carrier condition. This conclusion applies to **all trace-class inputs**, and the covariance theorem also permits D=1 and arbitrary sample sizes. Its restriction to the source's D≥2 physical states gives the claimed covariance; the larger scope does not weaken the claim.

### Part (b): unknownSpectrumValue_tendsto_affine

Actual source: [SpectralAffineTheorem.lean:12](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/SpectralAffineTheorem.lean#L12). Ten binders: SOURCE 4, STANDING 5, TYPING 1, EXCESS 0.

| Binder | Form | Classification | Source correspondence |
| --- | --- | --- | --- |
| d : ℕ | implicit | TYPING | Physical D=d+1; endpoint line 10. |
| hd : 1≤d | explicit | STANDING | D≥2 at paper line 163; endpoint line 12. |
| K : Set (SimpleSpectrum (d+1)) | explicit | SOURCE | Spectral family in part (b), paper line 339; endpoint line 13. |
| hK : IsCompact K | explicit | SOURCE | Compactness, paper line 339; endpoint line 13. |
| hKne : K.Nonempty | explicit | SOURCE | Nonempty, paper line 339; endpoint line 13. |
| hregular : closure (interior (SimpleSpectrum.toAffine '' K)) = SimpleSpectrum.toAffine '' K | explicit | SOURCE | Full trace-one affine regular closure, paper lines 340–341; endpoint lines 14–15. |
| m : ℕ→ℕ | explicit | STANDING | Output sequence, lines 163–170; endpoint line 16. |
| γ : ℝ | explicit | STANDING | Gain, line 165; endpoint line 16. |
| hγ : 1<γ | explicit | STANDING | Gain restriction, line 165; endpoint line 16. |
| hgain : Tendsto (fun n => (m n:ℝ)/n) atTop (𝓝 γ) | explicit | STANDING | Gain limit, line 165; endpoint line 17. |

The conclusion's subtype-bound p:K supplies precisely the infimum over p∈K. No chosen channel, Gaussian estimate, LAN object, sector hypothesis, or convergence witness appears among the actual export's arguments.

Total outer-binder classification across these three exports: **SOURCE 8, STANDING 12, TYPING 6, EXCESS 0** (26 binders, including 2 implicit; 0 instance binders). This count excludes the separate carrier/witness expansion below.

## Expanded carriers and literal definitions

| Carrier/field | Classification | Checked meaning and source |
| --- | --- | --- |
| SimpleSpectrum dimension parameter | TYPING | Fin D coordinates, [Main.lean:24](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/Main.lean#L24). |
| eigenvalue : Fin D→ℝ | TYPING | Real spectral coordinates, Main line 25. |
| positive : ∀i, 0<eigenvalue i | STANDING | Full rank; paper line 175; Main line 26. |
| strictAnti : StrictAnti eigenvalue | STANDING | Strict ordering, with every i<j counted; paper line 175; Main line 27. |
| normalized : ∑i,eigenvalue i=1 | STANDING | Trace-one affine hyperplane; paper lines 172–175; Main line 28. |
| SpectralAffine subtype value | TYPING | All Fin D→ℝ vectors, [SpectralAffineTopology.lean:13](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/SpectralAffineTopology.lean#L13). |
| SpectralAffine subtype proof ∑i,p i=1 | STANDING | Trace one only: no positivity/order/interior built into ambient carrier. |
| SpectralAffine topology | TYPING | Ordinary subtype topology from the full coordinate space, SpectralAffineTopology lines 15–19. |
| SimpleSpectrum topology | TYPING | Induced coordinate topology, [PhysicalCloningConverseSpectrum.lean:12](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/PhysicalCloningConverseSpectrum.lean#L12). |
| MatrixFidelity.State matrix | TYPING | Actual complex square matrix, [MatrixFidelity.lean:102](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/MatrixFidelity.lean#L102). |
| State.positive | SOURCE | Positive semidefinite matrix; State line 104. |
| State.trace_one | SOURCE | Exactly normalized state, State line 105. |
| State's index type and Fintype instance | TYPING | Finite physical coordinates; instantiated by Fin D, not an analytic premise. |
| QuantumChannel domain/codomain H,K | TYPING | Physical registers TensorRegister n/m (Fin D), [TensorLieGenerators.lean:21](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/TensorLieGenerators.lean#L21). |
| NormedAddCommGroup H | TYPING | Fixed Hilbert-space carrier instance. |
| InnerProductSpace ℂ H | TYPING | Fixed complex input inner product. |
| CompleteSpace H | TYPING | Fixed completeness instance. |
| NormedAddCommGroup K | TYPING | Fixed output carrier instance. |
| InnerProductSpace ℂ K | TYPING | Fixed complex output inner product. |
| CompleteSpace K | TYPING | Fixed output completeness instance. |
| QuantumChannel.toLinearMap (inherited) | SOURCE | A complex-linear map on the full trace-class space, [InfiniteTraceClassChannels.lean:126](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/InfiniteTraceClassChannels.lean#L126). |
| map_nonneg (inherited) | SOURCE | Preserves positivity; InfiniteTraceClassChannels line 129. |
| trace_preserving (inherited) | SOURCE | Preserves the actual complex trace of every input; lines 130–131. |
| completelyPositive | SOURCE | Complete positivity at every finite ancilla dimension, [InfiniteCompletelyPositive.lean:167](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/InfiniteCompletelyPositive.lean#L167); definition at line 29. |

The generic channel constructor has two implicit type parameters and the six listed instance parameters. In the endpoint's finite physical registers these are synthesized, with no freedom to assume contractivity, covariance, special sector support, or a Gaussian form. Positivity and complete positivity express the ordinary all-CPTP domain. No stronger continuity/contractivity law is assumed by its definition.

`orbitState` is literally U diag(p) U*, using the source spectrum fields to produce positivity and trace one ([TensorCloningPayoff.lean:32](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/TensorCloningPayoff.lean#L32), [PCTUnitaryTransportChannels.lean:15](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/PCTUnitaryTransportChannels.lean#L15)). `tensorState` is the full matrix tensor power, with norm exactly 1 proved from the trace-one field ([PCTPhysicalState.lean:41](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/PCTPhysicalState.lean#L41)). `statePayoff` applies the input channel and takes root fidelity against that full m-fold tensor state (TensorCloningPayoff lines 14–17). `PositiveTraceClass.rootFidelity` unfolds to the analytic `traceNorm (CFC.sqrt A * CFC.sqrt B)`, not its square ([HybridStates.lean:40](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/HybridStates.lean#L40), [InfiniteFidelity.lean:23](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/InfiniteFidelity.lean#L23)). The payoff equation compiles by reflexivity in the probe; the final norm definition was inspected directly.

`unknownSpectrumValue` is literally
`sup Φ:QuantumChannel, inf θ:K×U(D), spectrumPayoff n m Φ θ.p θ.U`
([TensorCloningPayoff.lean:48](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/TensorCloningPayoff.lean#L48), [LAN.lean:52](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/LAN.lean#L52)). This reflexive equation compiles at the physical register types. The one Φ sits **outside** the parameter infimum: neither a family Φ(p,U) nor a covariant-only optimizer is substituted. Compactness and regular closure are theorem hypotheses, not baked into the minimax definition.

The literal value formula compiles by reflexivity after unfolding `universalValue`, `classicalValue`, `orbitalValue`, `SimpleSpectrum.ratio`, `Thermal.modeFactor`, and `Thermal.classicalBase` ([Main.lean:30](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/Main.lean#L30), Main lines 41–49, [Thermal.lean:220](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/Thermal.lean#L220), Thermal line 285). Its exponent is ((D:ℝ)−1)/2, and PairIndex contains one copy of each i<j. The parameter ratio is p_j/p_i, not reversed. The probe checks the full product formula, rather than only a name for its limiting value.

`SpectralAffine` and `toAffine` compile to the full sum-one subtype and coordinate inclusion by reflexivity. The open embedding and `regularClosure_of_affine` are actual proved maps ([SpectralAffineTopology.lean:38](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/SpectralAffineTopology.lean#L38), line 60). Consequently the exported part (b) premise is full-dimensional relative to A_D, not an interior in K, a singleton carrier, or a lower-dimensional support.

## Prescribed witness and producer-to-consumer closure

The cloner is the actual fixed construction:

1. `YoungRounding.roundingPMF` is the pushforward of uniform volume on [-1/2,1/2)^d under floor(γ(μ_i+y_i)+1/2) ([YoungRounding.lean:32](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/YoungRounding.lean#L32), lines 75–98; [Rounding.lean:29](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/Rounding.lean#L29)).
2. `complete` sets the last coordinate to m minus the head sum; `Compatible` is exactly that the partition difference is Young of size m−n ([YoungCompatibility.lean:29](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/YoungCompatibility.lean#L29)).
3. `fallbackKernel` sends incompatible draws to the one-row partition (m,0,…,0), preserving the source's normalized PMF ([YoungCompatibilityFallback.lean:21](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/YoungCompatibilityFallback.lean#L21), lines 39–50).
4. `universalCopyPMF` combines that kernel with uniform multiplicity sampling; `universalChannel` measures the exhaustive physical Schur decomposition and uses actual Cartan sector channels, with invariant replacement on incompatible sector pairs ([TensorCloningKernel.lean:114](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/TensorCloningKernel.lean#L114), [TensorCloningChannel.lean:28](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/TensorCloningChannel.lean#L28), line 61).
5. `prescribedUniversalChannel` wraps the m≤n partial-trace convention and otherwise uses this construction ([TensorCloningPrescribed.lean:13](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/TensorCloningPrescribed.lean#L13), line 56).

The fallback copy chosen at TensorCloningKernel lines 58–65 is characterized by the proved one-row weight; it is not an arbitrary channel chosen merely from nonemptiness. The global cloner constructors have no spectral p,K,U argument; the sector constructors depend on their Young-label weights. The probe checks the prescribed-channel definition and both branch equations using the actual restriction/channel definitions.

Immediate proof terms were inspected and their compiled project-constant references are included in the log:

- Part (a) actually consumes `eventually_uniform_universalChannel_payoff` together with `eventually_output_gt_input` and the prescribed branch equality (TensorCloningPrescribedLimits lines 46–48). The former consumes the proved uniform retained-mixture fidelity, uniform randomized-label affinity, and bad-mass envelope (TensorCloningUniformUniversal lines 85–104). The retained-mixture theorem supplies its spectral/gap/normalization conditions from compact K and SimpleSpectrum fields, not a new endpoint premise ([TensorCloningRetainedUniversal.lean:20](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/TensorCloningRetainedUniversal.lean#L20)).
- Covariance consumes the actual `universalChannel_covariant` through `prescribedChannel_covariant` (TensorCloningPrescribed line 75). The corresponding exact application in the probe compiles without supplying a separate covariance assumption.
- Part (b) consumes `SimpleSpectrum.regularClosure_of_affine K hregular` as the actual regular-closure argument of `unknownSpectrumValue_tendsto` (SpectralAffineTheorem lines 20–21). That exact application compiles. The consumer combines a proved candidate lower bound and an unrestricted converse upper bound ([PhysicalCloningUniversalTheorem.lean:40](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/PhysicalCloningUniversalTheorem.lean#L40)).
- The candidate lower bound uses the constructed universal channel and the actual sector producer `eventually_uniform_universalKeep_transitionFidelity` ([TensorCloningUniversalAchievability.lean:14](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/TensorCloningUniversalAchievability.lean#L14), line 25). The channel is used as one admissible element of the all-channel supremum, not as its definition.
- The interior upper bound obtains a whitening frame and supplies `physicalCompactWindowLAN p b hb e` to the all-channel converse ([PhysicalCloningConverseUnconditional.lean:27](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/PhysicalCloningConverseUnconditional.lean#L27)). The exact produced-LAN application compiles. That chosen LAN object comes from the proved `nonempty_physicalCompactWindowLAN`, which constructs forward/reverse channel sequences and one cutoff before compact windows are supplied ([TensorLANEmbeddingCompactLAN.lean:19](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/TensorLANEmbeddingCompactLAN.lean#L19), line 50). Its `CompactWindowLAN` fields are forward, reverse, and actual compact-window approximation, not an assumed optimum ([PCTPhysicalFidelityLAN.lean:73](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/PCTPhysicalFidelityLAN.lean#L73)).
- The full mixed-LAN converse controls local spectral and orbital fluctuations and reduces to the hybrid all-channel bound ([PhysicalCloningConverseUnknown.lean:123](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/PhysicalCloningConverseUnknown.lean#L123)). The subsequent regular-closure step uses the proved continuity of the literal value ([PhysicalCloningConverseSpectrum.lean:52](https://github.com/JWang226/Cloning/blob/d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999/formalization/Cloning/PhysicalCloningConverseSpectrum.lean#L52), lines 60–79), preserving boundary spectra.

The LAN structure's dimension/frame/enumeration parameters are TYPING; its forward and reverse maps and compact-window approximation field are SOURCE argument ingredients. They are internal **produced witnesses**, not extra arguments of any audited export. The intermediate converse exposes a LAN premise, but its unconditional caller actually supplies the constructed witness. Importing that producer alone would not establish this connection; the exact application and compiled proof references provide the evidence here.

## Reproduction and binding

The reproducible [probe text](unknown-spectrum.lean.txt), [successful stdout](unknown-spectrum.log), [run metadata](unknown-spectrum-run.json), and [native timing log](unknown-spectrum.resources.log) accompany this review. The run metadata records the exact source SHA-256 manifest, HEAD, paper/probe hashes, current source-audit binding hashes, command, final exit code, and measured time/memory. The temporary .lean copy is outside the formal source inventory and is removed after the run.

From `formalization/`, copy the saved text to an ignored temporary .lean file and run:

```bash
set -e
mkdir -p .verify-work/semantic-pilot
cp verification/semantic-pilot/unknown-spectrum.lean.txt .verify-work/semantic-pilot/UnknownSpectrum.lean
lake env lean .verify-work/semantic-pilot/UnknownSpectrum.lean
rm .verify-work/semantic-pilot/UnknownSpectrum.lean
```

Reviewed HEAD: `d2ccb294f6a69d2cd65aa807cb9bfd1d9f829999`. Frozen paper SHA-256: `6f2453656031201968aef5cc9c043f7116bb7a1ed1cd2cebb2b905e3df94038d`. Toolchain: `leanprover/lean4:v4.29.0-rc6`, commit `00659f8e6071d7e46131ed643bf8003b99b044e9`. The final native run exited 0 in 20.58 seconds; maximum resident set size was 3,688,464,384 bytes, measured for the command by macOS /usr/bin/time -l. Proof-source hashes, binding files, and HEAD remained unchanged across the run. Each of the three actual exports reports exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or additional axiom appears.

The first native attempt had one probe-only namespace typo in an auxiliary constructor `#check`. A second attempt was stopped after adding auxiliary expansions that elaborated unexpectedly slowly. Their unsuccessful exits and log hashes are preserved in metadata. Neither is counted as a successful run; the final narrowed probe retains the endpoint, definition, singleton, application, binder, and axiom checks.

## Limits of this pilot

This review checks correspondence of the named endpoints, expanded carriers, literal normalization/formula/quantifier order, global prescribed witness, and selected actual producer-to-consumer proof applications. It does not independently rederive every theorem behind Schur decomposition, Cartan channels, local limits, mixed LAN, or the hybrid Gaussian optimum. The existing full source audit and independent checker records remain separate evidence, with their existing scope and trust limits. Construction correspondence was checked through literal definitions and named intermediate identities; this pilot does not supply a single full-operator equality certificate identifying every implementation choice with the manuscript's complete Q_n notation.

The scoped claim is Theorem 1.2's simple, full-rank, fixed-gain compact families. Part (a)'s singleton coverage is retained; part (b)'s full affine regular closure is retained. No conclusion about the paper's all-density minimax open problem, degenerate strata, or conjectural extensions is added.
