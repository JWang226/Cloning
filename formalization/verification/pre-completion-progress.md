# Progress on the remaining cloning proof obligations

**The latest integrated `lake build All` passed:** 941 implementation imports,
4,522 jobs. New modules continue to pass focused builds. The fresh full-library
axiom audit has not yet run; targeted endpoint checks use only `propext`,
`Classical.choice`, and `Quot.sound`. All work remains local.

The current working tree proves:

- The exhaustive physical Schur decomposition, multiplicities, character and
  dimension formulas, PBW frames, Cartan state/fidelity limits, physical Young
  local limits, and compact-window two-way LAN.
- Exact known-spectrum and compact regular-set unknown-spectrum minimax limits
  over all actual CPTP competitors.
- Exact compact-uniform two-sided fidelity convergence for both prescribed
  spectrum cloners, including singleton compact sets, and exact all-input
  unitary covariance.
- The flat-projector minimax limit over all literal Hermitian rank-r projectors,
  spectral orbit exhaustion, and uniform attainment by the constructed projector
  cloner.
- The physical full-environment PCT fidelity limit and the strict scalar
  comparison with the universal optimum.
- The smaller-environment PCT support factorization, unconditional internal
  count-measurement affinity bound, and strict projector comparison for the
  literal embedded purification output. The all-input rectangular purifier and
  Werner/trace channel are constructed. Exact physical Haar integration and
  downstream action are proved.

**All four main theorem families have unconditional compiled endpoints.** The
fixed rectangular purifier's action on every flat projector orbit is now proved.
`PhysicalFlatPCTTheorem` identifies the actual input-independent PCT channel and
proves its exact finite support factorization, uniform upper bound, and strict
suboptimality for rank greater than one. Independent semantic review passed.

Finite-sample prescribed-channel conventions, generic output sample-size adapters,
and the displayed PCT radical formula have compiled. The affine-hyperplane
regular-closure adapter has compiled, and the actual finite rank-one PCT channel
is exactly the pure Werner cloner. The corresponding rank-one projector-cloner
identity has now compiled and passed independent review.

The standalone joint-idler representation is now closed, including arbitrary
diagonal gains and correlated idlers. The proof constructs the regular Weyl GNS
representation, Gaussian vacuum projection, totality and full Fock decomposition,
then reconstructs the unique positive trace-one density operator. Targeted axiom
audits passed. The full arbitrary-input reduced squeezing dilation and exact
seeded-number-law identification are now proved. The general least-noise theorem
covers arbitrary nonnegative antitone product observables and actual covariant
CP/TNI maps, retaining the exact output trace. Its targeted axiom audit passed.

The general-rank physical dimension moments have proved O(1/N) bounds. The
actual flat minimax converse has a uniform finite bound for every m≥n with relative
error C/n, including m=γn+O(1). These are upper rates, not two-sided achievability
rates. The exact power-fidelity threshold inversion, its a/ε−(a+1)/2+O(ε)
expansion, and the actual finite rank-flat PCT sample certificate have compiled.

The full-rank squared-fidelity cubic expansions and strict coefficient comparison
have compiled. The physical projector Gaussian scaled-purity limit and internal
PCT error bound have compiled. Exact quadratic outer-envelope errors, the quartic
internal-error remainder, and scalar target-error brackets have compiled.
The physical envelope wrappers, literal liminf/limsup formulation, arbitrary-output-size adapter and actual target brackets have compiled and passed independent review.

Statement reconciliation identified additional auxiliary scope still being closed:

- Literal symmetric PBW inverse-Gram frames and the explicit fixed-height PBW
  and Cartan O(N^(-1/2)) rates.
- The fixed rank-bound PCT channel action and finite lower bound for every density
  of rank at most r, extending the already proved flat-projector and
  full-environment arbitrary-state guarantees.
- The actual all-density minimax lower/upper bounds and the accompanying scalar
  infimum, spectral ratio monotonicity, and large-gain discussion statements.
- Concrete full-rank target brackets and final integration of the projector
  purity envelopes and small-gain coefficient.

Convergence alone is not counted as a rate. These auxiliary additions do not
reopen the four main theorem families.

A final source freeze, integrated build, complete axiom audit, and manuscript
statement reconciliation are still required. The historical record below refers
only to the preserved twelfth-pass snapshot; its listed open tasks do not describe
the current working tree.

## Historical twelfth-pass record

**Twelfth pass verified.** All 46 new modules are integrated. The complete `lake build All` (3,932 jobs) and all three full-environment axiom-audit workers passed on `2026-10-03T17:34:00.781189+00:00`. The checked library contains **395 implementation modules, 3,353 source theorem/lemma declarations, and 7,391 unique compiled project constants**. Only `propext`, `Classical.choice` and `Quot.sound` occur; source/dependency and compiled-artifact hashes remained unchanged. See the [completion record](verification/twelfth-pass/run.json). All work remains local. **The full physical mixed-state cloning theorem remains conditional.**

This pass closes the actual cyclic-sector irreducibility and Cartan-channel construction, the all-input lifted-channel construction, the joint PCT comparison-state/fidelity calculation, and the exact physical local-chart step. It also proves dominated integration and the final two-sided fidelity squeeze from explicit mixed-state LAN approximations.

See the [semantic review](verification/twelfth-pass-review.md), [concrete next obligations](verification/twelfth-pass-next-obligations.md), [verification pointer](verification/latest.json), and [machine-readable status](../formalization.yaml).

## Newly established endpoints

| Component | Proved endpoint | Remaining scope |
|---|---|---|
| Actual cyclic irreducible sectors | [`partition_cyclicSector_irreducible`](Cloning/TensorCyclicSectorIrreducible.lean) and [restricted-generator scalarity](Cloning/TensorCyclicSectorOperators.lean) derive irreducibility from highest-line uniqueness in the actual lowering-word span. | One concrete copy per partition; the full tensor decomposition and multiplicities remain open. |
| Exact highest-weight Gram isometry | [Exact Gram equality](Cloning/TensorHighestGram.lean), [full quotient isometry](Cloning/TensorHighestGramIsometry.lean), and [literal tensor covariance](Cloning/TensorHighestGramCovariance.lean) identify any normalized highest tensors of the same weight. | This exact statement is distinct from fixed-cutoff asymptotic PBW estimates and does not supply complete retained weight frames. |
| Actual tensor-power sector action | [`cyclicUnitary`](Cloning/TensorCyclicSectorCovariance.lean) is the actual restricted unitary tensor power. Invariance and commutant transport hold for every complex matrix, including singular matrices. | Physical character and dimension formulas remain unidentified. |
| Constructed Cartan inclusion and channel | [Exact inclusion/intertwining/range](Cloning/TensorCartanIntertwiner.lean), [complete product coordinates](Cloning/TensorCartanCoordinates.lean), and [`physicalCartanChannel`](Cloning/TensorCartanChannel.lean) construct the actual sector CPTP map. Balance and the dimension ratio are proved internally. | Dimensions are actual sector finranks; no Weyl-formula identification or retained-state approximation is asserted. |
| All-input lifted channel | [`MatrixLiftedCPTP.channel`](Cloning/MatrixLiftedCPTP.lean) measures/discards/applies sector channels/samples/prepares on all complex inputs. [Canonical finite-channel Kraus construction](Cloning/MatrixLiftedCPTPKraus.lean) supplies the [actual trace-class protocol](Cloning/MatrixLiftedCPTPPhysical.lean), with the earlier exact state formula. | Physical Schur transformation and its block probability law remain to be constructed and identified. |
| Actual joint tangent law and whitening | [Joint pushforward law](Cloning/PCTJointGaussianLaw.lean), [whitened law](Cloning/PCTJointGaussianWhitenedLaw.lean), and [explicit score-chart inverse](Cloning/PCTJointGaussianChart.lean) derive independence and the nonsingular Gaussian coordinates. | The reference measure is explicitly pulled-back coordinate volume; an intrinsic-volume Jacobian is not asserted. |
| Actual joint PCT mixture and fidelity | [The genuine hybrid L1 integral](Cloning/PCTHybridMixtureGaussian.lean) equals `pctGaussianThermalPositive`. [`tangentMixtureChannel_fidelity_eq_pctValue`](Cloning/PCTHybridMixtureChannel.lean) concerns an actual CPTP translation-average channel. | This is the hybrid comparison output. Its identification with the finite-copy physical fidelity still needs mixed-state LAN. |
| Exact physical PCT local chart | [Actual inverse chart](Cloning/PCTLocalChartInverse.lean), [exact frame-particle chart and parameter limits](Cloning/PCTTangentChartFrame.lean), and [eventual admissibility](Cloning/PCTTangentChartAdmissible.lean) give the required scale 1/√L and a fixed compact trace-zero parameter window for each tangent. | No uniformity over the unbounded tangent support and no physical LAN map are claimed. |
| Mixed-mixture fidelity transfer | [`fidelity_tendsto_of_mixed_mixture`](Cloning/PCTMixedMixtureTransfer.lean) proves dominated forward/reverse integration and the actual fidelity limit from pointwise LAN and physical mixture errors. | Physical approximation premises remain explicit; the integration and squeeze no longer require separate application proofs. |
| Coordinate transport of all competitors | [`Channel.coordinateEquiv`](Cloning/HybridCoordinateTransport.lean) preserves all-input CP/TP and root fidelity under an actual measure-preserving equivalence. The [constructed score chart](Cloning/PCTJointGaussianChart.lean) instantiates it. | This supplies coordinate bookkeeping, not the physical LAN approximation. |

## Why the representation step is stronger now

The earlier physical PBW Gram limits established eventual independence for each fixed finite retained occupation family. The new exact Gram identity holds on all finite linear combinations of all lowering words. Equal kernels allow quotienting every linear relation and produce an isometry of complete cyclic sectors. No independent-basis or approximate-isometry premise is used.

Highest-line uniqueness gives scalar commutants and irreducibility under the actual generators. Diagonal occupancy and actual tensor-transvection differentiation transport commutation to every literal tensor power. Tensoring highest vectors therefore gives an exact physical Cartan inclusion, with its range identified.

For its coordinate matrix V, the reduced range operator Tr_environment(VV*) commutes with every first-factor generator. Scalarity forces it to be scalar; tracing determines dim(sum)/dim(first). The resulting channel has the exact formula

\[
X\longmapsto\frac{\dim H_\mu}{\dim H_{\mu+\nu}}\,
V^*(X\otimes I_{H_\nu})V.
\]

Isometry, intertwining, scalarity, balancing and Kraus normalization are all discharged for the constructed physical cyclic sectors. Complete Schur decomposition and the combinatorial formulas for these dimensions are subsequent tasks.

## What the PCT comparison now proves

For v=γ−1, the actual tangent law has classical covariance 2vΣ_p and orbital circular variances v(p_i+p_j)/(p_i−p_j). Testing every real linear functional proves the joint product law. Whitening is an actual invertible map on the trace-zero score space, with a stated reference measure.

A seed classical covariance I broadens to (2γ−1)I; the orbital modes become `Thermal.pct γ q`. The actual joint L1 translation integral, its all-input CPTP averaging channel and its exact fidelity `pctValue` are proved. This closes the former joint comparison-state calculation.

The exact physical chart is obtained from the inverse function theorem on Hermitian matrices. Its derivative is the identity, because the explicit skew generator's commutator recovers the off-diagonal tangent. At sample scale 1/√L, the chart is exactly the reduced physical `frameParticle`, with spectral parameters summing to zero and converging to the classical score, and orbital parameters converging to the displacement used in the joint-law theorem. Positive ordered eigenvalues and eventual membership in a fixed compact parameter set are proved for each fixed tangent. There is no extra factor √γ.

Dominated convergence applies to the scalar norm errors bounded by two, even when the physical Hilbert space changes with L. Thus pointwise two-way LAN on these chart states, seed approximations and the existing physical Gaussian-mixture approximation imply the physical fidelity limit. The missing input is the actual mixed-state LAN construction and its compact-window estimates.

## Established results retained

- **Physical local CCR/PBW estimates:** arbitrary-partition highest tensors, literal lowering-word filtration, occupancy/root bounds, actual normalized CCR defects, fixed finite Gram convergence and eventual independence. No polynomially growing cutoff is claimed.
- **Universal orbital and hybrid Gaussian optimal limits:** optimization over all actual CPTP competitors occurs before the expanding-prior/real-box limit. Actual amplifier/classical-dilation channels attain the value; γ>1, all 0≤q_i<1, vacuum and zero-dimensional mode spaces are covered.
- **General Young normalization:** reversible RSK/Pieri constructs the exact normalized tableau PMF. Concentration includes repeated/zero coordinates; fallback and moment statements retain their stated spectral hypotheses.
- **Global full-environment PCT:** an actual state-independent CPTP channel agrees with the literal physical formula on every input and has the proved Gaussian reduced-product mixture limit. Smaller rank-adapted environments remain separate.
- **Fidelity and transfer:** both actual mixed-channel data-processing directions, continuity/Jensen, sharp competitor-independent transfer, fixed-window Gaussian converse, channel averaging and compact-payoff transfer remain proved.

## Remaining steps for the physical main theorem

1. **Full physical Schur identification.** Decompose the tensor register into all irreducible copies; identify multiplicities, characters, dimensions and the physical tensor-state block law. Actual cyclic copies, exact Cartan isometries/channels and the all-input lifted assembly are now available.
2. **Retained-sector asymptotics.** Prove ordered lowering-monomial cutoff completeness, exact-weight common output frames, Cartan splitting limits and thermal tails. Independence alone is not completeness; individual-component convergence is not an exact mixture-fidelity theorem.
3. **Young local limits.** Identify the physical block probabilities with the normalized combinatorial PMF, then prove compact-spectrum uniform local central limits and the required rates.
4. **Physical two-way mixed-state LAN.** Construct the channels and compact-window errors, including the physical local-unitary-to-Weyl approximation. Exact coordinate charts and all-competitor coordinate transport are now proved.
5. **Global closure.** Apply those physical estimates to the converse and an actual global achievable protocol, and to the now proved PCT mixture/fidelity transfer. The smaller rank-adapted PCT construction remains separate.

The unknown-spectrum minimax theorem retains the nonempty regular-closure condition on the spectral set. Full joint-idler reconstruction and stronger observable-domination results are separate; the established Gaussian optima do not depend on them. The conditional assembly in `Cloning/Main.lean` is not relabeled as unconditional, and module counts are not a percentage of mathematical completion.

Earlier semantic reviews and next-obligation analyses remain preserved in `verification/`. The [new roadmap](verification/twelfth-pass-next-obligations.md) proposes projected-basis highest-vector extraction and an orthogonal finite-dimensional recursion for the next decomposition step; these proposals are not additional proved endpoints.
