# Lean formalization of mixed-state cloning

**Status: substantial partial formalization. The manuscript’s full quantum cloning theorems are not yet proved end to end in Lean.**

The project contains checked proofs of concrete matrix, probability, combinatorial, scalar, and limiting arguments from `cloning.tex`. The main theorem assembly is conditional: its remaining physical-model, representation-theoretic, LAN, and Gaussian estimates are visible theorem hypotheses. No unproved proposition is installed as a project axiom.

The latest pass constructs actual bosonic and occupation channels, proves their thermal/coherent output laws, and proves the exact thermal-fidelity optimum over arbitrary correlated idler states. It also constructs the randomized rounding kernel and its density-comparison bridge, and derives rank-two Young-law moments from an explicit combinatorial probability law. The seventh-pass section states these results and their precise boundaries.

## Concrete fidelity milestone

The second pass replaces previously assumed finite-matrix fidelity laws with proofs from the positive square root. In particular, for positive blocks and trace-one ancillary states it proves

\[
F\!\left(\bigoplus_i X_i\otimes\tau_i,\ \bigoplus_i p_i\rho_i\otimes\tau_i\right)
=\sum_i\sqrt{p_i}\,F(X_i,\rho_i).
\]

This is the matrix identity at the heart of the manuscript's lifted-kernel proposition. The implementation allows different sector and ancillary dimensions. It also proves canonical trace normalization, isometric invariance, the projector operator-domination step (including an actual Kraus-channel converse), and exact fidelities of concrete outputs assembled from CPTP sector channels. The new convergence theorem concerns actual density-matrix blocks and no longer assumes their fidelity factorization.

## The quantum deletion condition is now proved

The third pass proves the previously assumed `hquantum` estimate for concrete positive matrices, even when retained and discarded contributions overlap. The central new results are

\[
|F(G+B,T)-F(G,T)|\le\sqrt{\operatorname{Tr}B\,\operatorname{Tr}T},
\qquad
|F(A,T)-F(B,S)|\le\sqrt{\|A-B\|_1}+\sqrt{\|T-S\|_1}
\]

where the second inequality uses subnormalized positive matrices. These follow from proved square-root trace subadditivity, a dimension-independent trace bound, symmetry, and operator absolute-value majorization. Singular matrices are handled by positive-definite regularization; the final constants do not depend on dimension.

`MatrixLiftedTrimming` proves that filtering the actual input-output transition weights produces a positive discarded matrix whose trace is exactly the discarded probability mass. `MatrixFidelityAsymptotics` then proves the actual finite `η + 2√δ` factorization estimate and growing-dimension convergence **without an `hquantum` hypothesis**. The old generic `Main` theorem retains its parameter as a reusable abstract interface.

For achievability, there is a weaker sufficient hypothesis than two-sided retained-mixture approximation. Proved fidelity concavity passes **individual retained-channel output lower bounds** through their conditional mixtures. The resulting concrete estimate is

\[
F_{\rm actual}\ge c\,F_{\rm classical}-\eta-\sqrt{\delta}.
\]

The corresponding growing-dimension theorem gives eventual lower approximation to `c * l` when the individual error and discarded mass vanish and the classical affinity tends to `l`. It deliberately makes no upper bound or exact-mixture-limit claim.

## Channel data processing and contraction are now proved

The fourth pass removes two further finite-dimensional quantum-law assumptions. For every actual CPTP matrix channel `Φ` and positive matrices `A,B`, Lean proves

\[
F(A,B)\le F(\Phi(A),\Phi(B)),\qquad
\|\Phi(A)-\Phi(B)\|_1\le\|A-B\|_1.
\]

The statements allow singular inputs, unequal input/output dimensions, and arbitrary input traces. The norm is the concrete spectral trace norm already used by the continuity theorem. Data processing follows from an explicitly constructed optimal positive block witness, complete positivity, and trace preservation. Contraction follows from the spectral positive/negative decomposition and a proved minimal-decomposition bound.

`MatrixLANTransfer.fidelity_transfer` now proves the concrete matrix channel-composition estimate with only the approximation errors as hypotheses:

\[
F(M\rho,\sigma)\le F(TMS\phi,\psi)+\sqrt\delta+\sqrt\eta.
\]

Its minimax-to-Bayes corollary also proves channel closure under composition and supplies fidelity bounds automatically. These results concern finite-dimensional comparison experiments; the manuscript's infinite-dimensional Gaussian LAN channels and their approximation estimates still require construction.

A concrete CPTP map discarding a classical label gives **joint** and strong fidelity concavity for arbitrary finite positive mixtures, allowing independent weights on the two sides. No mixture concavity axiom is used.

`MatrixWeightedFidelity` also proves the noncommutative finite-matrix bound

\[
F(A,B)^2\le\operatorname{Tr}(AW)\operatorname{Tr}(BW^{-1})
\]

for every positive-definite weight `W`, without requiring it to commute with either input. The sixth pass extends this to trace-class operators and proves the regularized inverse-moment version required for a weight without bounded inverse.

The full cloning theorem remains conditional on the physical Schur/Cartan identification, uniform sector/PBW estimates, discarded-mass concentration, classical Young-label limits, LAN constructions, and Gaussian optimization. Fidelity concavity supplies mixture lower bounds; it does not by itself prove the two-sided sector-mixture approximation.

## Online resources and the fifth pass

The search found usable mathematics beyond finite matrices. The relevant versions and source-audit results are recorded in `EXTERNAL_RESOURCES.json`.

| Resource | What was found | Use in this project |
|---|---|---|
| [Pinned Mathlib](https://github.com/leanprover-community/mathlib4/tree/f156f7abd91ac67adb22bf999e5a71ba22e22e41) | Irreducible Schur lemma, Gaussian integrals, finite-product Fubini, Tannery dominated convergence | Direct imports used in the new proofs below |
| [Etingof representation theory](https://github.com/mathlib-initiative/Etingof-RepresentationTheory-draft1/tree/9587adb8833ebd14d6f3c586a39fac0241c9df63) | Concrete Schur–Weyl decomposition, literal intertwiner multiplicity spaces, Young-symmetrizer Schur modules, character/weight/dimension formulas | Relevant dependency closures inspected without finding proof placeholders; not locally rebuilt or imported. Targets Lean 4.32.2; reuse licensing was not established from the inspected draft repository |
| [PhyslibAlpha trace class](https://github.com/leanprover-community/physlib/tree/f6e446ca99fd83b3a60743a61900cb2acb98f531/PhyslibAlpha/ProbabilisticTheory/HilbertSpace/TraceClass) | Actual operators on arbitrary complete complex Hilbert spaces; trace class and trace-norm infrastructure | The analytic dependency chain across eight upstream files, through Banach completeness and trace algebra was adapted to our pinned Lean version and checked locally, with upstream authorship retained and Apache license included |
| [Spectra](https://github.com/adambornemann-glitch/Spectra) | Additional infinite-dimensional trace-class/fidelity and Fock-space infrastructure | Candidate source inspected and pinned in the inventory; not imported or locally rebuilt |

`MatrixPartialTraceCovariance` and `MatrixCovariantBalance` remove the former Cartan **balanced-partial-trace hypothesis**. For genuine unitary representations, an isometric intertwiner `V`, and irreducibility on the retained factor, Mathlib's proved Schur lemma gives

\[
\operatorname{Tr}_B(VV^\dagger)=\frac{\dim C}{\dim A}I_A.
\]

The resulting constructor proves the actual Cartan channel is CPTP. Constructing the manuscript's particular representations and intertwiner remains necessary; the theorem does not assume its balancing conclusion.

`GaussianAffinity` evaluates actual normalized Gaussian density integrals. One-dimensional integration and finite-product Fubini yield

\[
\int\sqrt{p(x)q(x)}\,dx
=\left(\frac{2\sqrt\gamma}{1+\gamma}\right)^{(d-1)/2}
\]

for product Gaussians related by variance dilation `gamma`. A common invertible measurable coordinate change preserves the result with the pushed-forward reference measure. This proves the Gaussian factor; it does not prove the Young-law local limit or identify the manuscript's covariance coordinates automatically.

`CountableScheffe` proves the pointwise-to-ℓ¹ upgrade for normalized laws on an infinite occupation lattice, countable Hellinger continuity/convergence, and square-root-amplitude convergence. The multimode geometric target is normalized by the existing `Thermal` proofs. The sixth pass below proves the Werner and Poisson coefficient limits and realizes them as actual trace-class operator limits.

The `InfiniteTraceClass*` and `InfiniteHilbertSchmidt` modules now supply genuine infinite-dimensional operator foundations: polar decomposition, Hilbert–Schmidt products, a two-sided trace-class ideal, basis-independent analytic trace and trace norm, trace linearity/cyclicity, trace-norm triangle and ideal inequalities, and completeness of the trace-class normed space. The finite-dimensional analytic trace agrees with the usual algebraic trace. These results are adapted from Physlib, not claimed as newly invented proofs.

`InfiniteDensityState` adds actual positive trace-class density operators, normalized using the analytic trace. Unit vectors give proved rank-one pure states with trace and trace norm equal to one. This avoids using the total algebraic `LinearMap.trace` as an infinite-dimensional state normalization. The sixth pass builds actual infinite-dimensional fidelity and channel laws on these foundations. Physical bosonic channels and the quantum LAN construction remain separate.

For the remaining analytical construction, [Kahn–Guţă, Theorem 4.3](https://arxiv.org/pdf/0804.3876) is the exact two-channel quantum LAN reference. [Lami–Sabapathy–Winter, Lemma 7](https://arxiv.org/pdf/1806.11042) supplies the exact arbitrary-idler dilation in the nondegenerate symplectic-defect regime. These are paper-level resources, not imported Lean theorems. No directly usable Lean proof of the required quantum LAN or uniform Young local limit was located in this search. The older Gaussian-cloning optimality results for trace-distance loss do not automatically establish this manuscript's fidelity converse.

## Sixth pass: proofs of infinite-dimensional and occupation inputs

This section records the sixth-pass checkpoint; several physical-construction boundaries below are advanced by the seventh pass. The proofs act on actual bounded operators on complete complex Hilbert spaces, with the analytic trace and trace norm. They do not replace the requested conclusions with structure fields.

- **Occupation limits.** `WernerNormalization` counts the occupation lattice by a proved stars-and-bars bijection. `WernerAsymptotics` proves the actual binomial-ratio limit and ℓ¹ convergence to the product-geometric law from `m_n/n → gamma > 1`. `InfiniteOccupationStates` turns this into trace-norm convergence of explicit positive trace-class occupation operators. `PoissonApproximation`, `CoherentCoefficients`, and `InfinitePureStateContinuity` prove binomial-to-Poisson coefficient convergence, convergence of the actual unit vectors in complex ℓ², and trace-norm convergence of their rank-one projectors. The physical Werner eigenvalue and symmetric-tensor embedding identifications remain separate.
- **Actual thermal fidelity.** `InfiniteDiagonalFidelity` proves that fidelity of arbitrary nonnegative summable Hilbert-basis mixtures is their countable Hellinger affinity. Constructed one-mode and multimode geometric density operators therefore satisfy the exact thermal fidelity formulas. No finite cutoff or operator-to-scalar identification is assumed.
- **Infinite fidelity continuity and deletion.** `InfinitePowersStormer` proves the Hilbert–Schmidt square-root estimate from positive Hilbert–Schmidt trace pairings and positive majorants. `InfiniteFidelityContinuity` derives the actual `sqrt(epsilon) + sqrt(delta)` trace-distance modulus for normalized states and the square-root discarded-trace bound. Neither estimate is assumed.
- **Infinite channel data processing and transfer.** `InfiniteFidelityWitness` constructs an attaining polar block witness for arbitrary positive trace-class inputs, including singular ones. `InfiniteFidelityBlockBound` proves the matching upper bound through actual finite corners and trace-norm limits. `InfiniteChannelFidelity` derives fidelity data processing for every actual CPTP map. `InfiniteLANTransfer` consequently proves the channel-composition error `sqrt(delta) + sqrt(eta)` and its minimax-to-Bayes corollary for Hilbert-space quantum experiments, assuming only the comparison errors and payoff integrability. The comparison channels themselves and their model-specific estimates remain to be constructed. Continuous classical–quantum registers require a separate operator-valued L¹ formalization.
- **Weighted fidelity.** `InfiniteFidelityWeighted` proves the noncommutative weighted bound for bounded strictly positive weights. `InfiniteFidelityRegularized` removes `epsilon I` under a uniform bound on regularized inverse moments. This permits a compact weight whose inverse is unbounded. Proving that bound for the manuscript’s particular Gaussian witness still requires the quantum model and its moment law.
- **Actual cutoff channels.** `InfiniteCompletelyPositive` tests positivity on every finite ancilla using the genuine operator quadratic form and proves complete positivity of projection compression plus replacement. `InfiniteCutoffChannels` constructs CPTP maps with an explicit finite output subspace and proves trace-norm convergence, uniform on every compact set of positive inputs. The underlying rank-one series and finite-dimensional approximation are proved.
- **Weak limits and normal parts.** `InfiniteTraceClassWeakLimit` proves trace-class membership and the upper trace bound for a positive weak-operator limit, without assuming the limit is trace class. An escaping basis-projector example verifies actual trace loss. `InfiniteTraceClassNormalPart` constructs the trace-class normal part of a bounded positive functional and proves agreement on every compact observable. `InfiniteChannelWeakLimit` proves CP and trace nonincrease from the actual coefficient limits of channels; it does not assume these closure laws. `InfiniteChannelTraceRepair` constructs the CPTP completion of a CP trace-nonincreasing map, proves operator domination, and identifies its trace-norm repair cost exactly with the lost trace. `InfiniteTraceClassSeparable` proves separability of the trace-class space from separability of the Hilbert space, using a proved dense span of rank-one projectors.
- **The compact CP limit lemma.** `InfiniteAsymptoticCPCompactness.exists_subsequence_covariant_cp_limit_of_limsup_trace_bound` now proves the manuscript’s complete compact-limit statement on separable Hilbert spaces. From actual CP maps with a uniform operator-norm bound and the stated `limsup` trace estimate, it constructs a complex-linear trace-class CP limit and **one common subsequence** converging for every input and every compact observable. Trace loss is allowed, the sharper limiting trace bound is proved, and vanishing trace-norm covariance defects give exact covariance for every parameter in an arbitrary, possibly uncountable set. Neither the limit map nor the subsequence is supplied as a hypothesis. The separately constructed fixed-state trace repair is not asserted to preserve covariance.
- **Projector dimension factors.** `YoungDimensionRatio` proves the explicit crossing-root product limit `gamma^(-r(d-r)/2)`. `YoungDimensionSecondOrder` proves cancellation of the first-order centered-row term and an explicit error of order `1/N + sum(row_i-N/r)^2/N^2`. Identification of the product with representation dimensions and the probabilistic Young-law estimates still need to be supplied.

The finite-corner realization in `InfiniteFiniteCorner` preserves multiplication, adjoint, positivity, square root, analytic trace, and fidelity, including the empty corner. This proves the compatibility needed to pass finite-matrix fidelity inequalities to the infinite-dimensional limit.

## Seventh pass: constructed bosonic channels and label bridges

These are proofs for concrete operators and probability laws. The constructions do not add the desired channel law, moment inequality, or convergence theorem as a structure field.

- **Actual countable Kraus channels.** `InfiniteKrausChannel`, `InfiniteIsometricChannel`, and `InfiniteRectangularKraus` prove trace-class membership, trace-norm summability, complex linearity, positivity at every finite ancilla, and trace preservation from the vector identity `HasSum (fun k => ‖K k x‖²) ‖x‖²`. Input and output Hilbert spaces may differ. Bounded rectangular conjugation and isometric channels are constructed from proved rank-one trace-class series.
- **Quantum-limited amplifier.** `BosonicAmplifier` constructs the coherent Fock-space isometry with coefficients `sqrt(choose(n+k,n)*(1-r)^(n+1)*r^k)`, proves orthonormality, and constructs its Kraus slices. `BosonicAmplifierChannel` bundles the actual CPTP map. `BosonicAmplifierThermal` proves that a geometric state with parameter `q` is sent to the geometric state with parameter `r+(1-r)*q`. At gain `g>1`, `r=1-1/g`, so the actual achieved fidelity is `Thermal.modeFactor g q`. The equality is an operator identity, not just equality of diagonal entries of potentially nondiagonal operators.
- **Arbitrary joint idlers.** `BosonicIdlerChannel` and `MultimodeIdler` construct the complementary seeded channels as coherent isometries followed by Kraus slices. For every trace-class idler operator, they prove its output number diagonal is the negative-binomial mixture of its input number diagonal. Off-diagonal input entries disappear from the number probabilities; the full output is not asserted to be diagonal. Correlated and coherent idlers are allowed. `BosonicStochasticOrder` and `BosonicMixtureStochasticOrder` prove the full nonnegative antitone product-test inequality from an exact negative-binomial convolution, not an assumed coupling. `MultimodeLeastNoise` constructs the corresponding bounded positive number observable and proves the actual channel trace-moment inequality for arbitrary positive trace-class seeds.
- **Actual compact witness and exact seed-state optimum.** `ThermalWitness` constructs the positive, injective, compact diagonal witness; computes its actual thermal trace moment; and proves the uniformly bounded regularized inverse moment. `ThermalIdlerFidelity` and `MultimodeThermalIdlerFidelity` combine it with the constructed channel law. The exact theorem `Cloning.MultimodeThermalIdlerFidelity.isGreatest_idler_stateFidelity` optimizes over every joint idler density operator, including entangled idlers. Vacuum attains the product thermal fidelity by an actual output-operator identity. The upper bound for a deficient positive trace-class seed has the exact trace factor. The regime is `0<q_i<x_i<1`; zero modes are included. `OrbitalSeededOptimum.isGreatest_payoff` instantiates the operator theorem at every pair ratio of a `SimpleSpectrum` and identifies the exact attained value with the manuscript’s `orbitalValue` formula.
- **Occupation channel and complex coherent products.** `SymmetricOccupation` constructs normalized symmetric occupation vectors by counting subsets of the finite computational tensor basis. `OccupationCompression` and `OccupationChannel` build a genuine rectangular CPTP channel on the whole Fock space: retain occupations up to `L` coherently, then replace the discarded mass by the finite vacuum. Its pure-input output is proved exactly. `ComplexCoherent` constructs the usual coherent vector for every complex `z`, including zero, and proves the actual channel output converges in trace norm to the normalized finite product with coefficients `(z/sqrt L)^|S| / sqrt(1+|z|²/L)^L`. This is a fixed-amplitude result in the explicit two-level computational tensor realization; it is not a uniform LAN theorem or an arbitrary physical symmetric-tensor identification.
- **Coherent kernels and Gaussian mixtures.** `CoherentKernel`, `CoherentContinuity`, and `MultimodeCoherent` prove the literal complex coherent-state overlap kernels, normalization, joint continuity, trace-one projectors, and Bochner integrability for every finite measure, including zero modes. `ComplexGaussianMoments` derives angular orthogonality and Gamma radial moments. `CoherentGaussianMixture` proves the actual one-mode trace-class operator identity `integral |coh(z)><coh(z)| dmu_s = tau_(s/(1+s))`, where the literal circular Gaussian density is `exp(-|z|^2/s)/(pi*s)` and its probability normalization is proved. `MultimodeCoherentGaussianMixture.integral_coherentProjector_gaussian_eq_productThermal` proves the finite product Gaussian version for arbitrary positive coordinate variances, with actual product-measure normalization and Fubini, including zero modes. This closes the coherent Gaussian-mixture identity in the canonical finite-mode Fock model.
- **Constructed randomized rounding.** `YoungRounding` proves a measurable half-open lattice partition with unit cell volume, constructs the uniform-dither rounding PMF, and proves its overlap formula, normalization, support bounds, and countable transport. It proves exact interpolation and Hellinger identities, L¹ contraction, the dilation Jacobian, the transport/interpolation intertwining identity, and shrinking-cell averaging convergence uniformly over lattice translations. Its final `roundedDensity_l1_of_local_limit` derives actual rescaled output convergence from explicit local density estimates against a fixed continuous normalized reference. This is the coordinate-lattice construction before Young compatibility fallback. The affine root-lattice identification with induced hyperplane measure, the physical fallback and its negligible mass, the local estimates for Young laws, and uniformity over a varying compact family of spectra remain separate tasks.
- **Concrete rank-two Young law.** `YoungTwoRowMoment` constructs the finite legal tableau-path law, proves its exact normalized shape marginal, and derives the Casimir expectation and centered-row second moment without a moment hypothesis. `YoungTwoRowAsymptotics` and `YoungTwoRowConcentration` prove `O(1/N)` relative errors for both the forward and reciprocal dimension-product expectations for every ambient `d=2+k`. The actual tail bound `(N+1)*(9/10)^N` is derived from the explicit path law, so no concentration or moment premise remains in these rank-two results. These are statements about a concrete two-row combinatorial law and explicit Weyl products. Their identification with the manuscript's physical representation dimensions, and the arbitrary-rank extension, remain separate.

The exact seeded-channel optimization does **not** prove that every displacement-covariant channel belongs to that family. Weyl displacement construction/covariance, the arbitrary-idler representation theorem, and the composite-gain reduction remain obligations for the universal Gaussian converse. Quantum LAN maps and their uniform errors, physical Schur/Cartan/PBW identifications, and the continuous classical–quantum integration/averaging model also remain. No general finite-sector PRV fidelity-optimality claim is made.

## Remaining end-to-end obligations

The main theorem is still conditional on the following concrete mathematical work. None is hidden as a project axiom.

| Manuscript obligation | What is now proved | What still needs a Lean proof |
|---|---|---|
| Uniform Schur/Cartan sector approximation | Concrete finite channel identities, irreducible-data balance, dimension-product estimates, infinite channel/fidelity laws | Actual physical representations/intertwiners; uniform fixed-height PBW/Gram estimates and common output frame |
| Young-label comparison | Constructed coordinate rounding PMF and analytic comparison bridge; explicit rank-two law, concentration and both dimension moments | General-rank Schur law identification, uniform local limit/concentration, root-hyperplane measure bridge, compatibility fallback and its negligible mass |
| Universal Gaussian quantum bound | Constructed one-/multimode seeded channels, full antitone least-noise moment, exact optimum over arbitrary joint idlers | Actual Weyl displacements/covariance and universal arbitrary-idler representation; composite-gain reduction for every competing covariant channel |
| Flat-prior converse | Compact CP subsequence with limiting covariance, actual weighted fidelity and witness bounds | Continuous classical–quantum operator-valued L¹ model; channel averaging, Gaussian-weighted maps and boundary estimates |
| LAN reduction | Actual quantum-channel transfer and minimax/Bayes inequalities | The physical forward/reverse LAN maps and uniform approximation errors; continuous classical register version |
| PCT physical comparison | Actual thermal occupation limits, complex occupation channel in the two-level tensor realization, and finite-mode Gaussian coherent-mixture identity | General physical symmetric-tensor occupation map, Werner-output eigenvalue identification, and the remaining model-specific PCT output/covariance connection |

## Verification

The clean build passed: **1348 lemmas/theorems in 136 modules (22144 Lean source lines)**. The exact compiler result and transitive axiom audit are recorded in `verification.json`, `BUILD.log`, and `AXIOMS.txt`. The compiled-environment audit checks all 2753 unique constants owned by project modules, including theorem proofs, definitions, instances and generated auxiliaries; `Audit.lean` reproduces that check. The allowed foundational axioms are only `propext`, `Classical.choice`, and `Quot.sound`; the audit rejects any other dependency, including `sorryAx`.

Pinned environment:

- Lean `v4.29.0-rc6`.
- Mathlib commit `f156f7abd91ac67adb22bf999e5a71ba22e22e41`.
- Transitive dependencies fixed in `lake-manifest.json`.

The sources were checked with `autoImplicit=false`, so misspelled identifiers cannot silently become extra assumptions. The final verification starts with an empty local build directory and respects dependency order. Independent modules can compile concurrently. Optional parallel axiom auditing loads the same complete environment in every worker, audits disjoint module groups using Lean’s standard `collectAxioms`, and checks the exact exported-constant inventory and successful completion of every worker. The serial `Audit.lean` remains a complete reproduction route.

## What is formalized

| Component | Checked content | Remaining input |
|---|---|---|
| `Channels`, `CartanChannel`, `MatrixPartialTraceCovariance`, `MatrixCovariantBalance` | Actual Kraus maps, complete positivity, trace preservation, Cartan formula, and balanced partial trace derived from genuine irreducible unitary representation data | Construction of the concrete Cartan inclusion/representations and physical Schur identification |
| `Compression` | Exact matrix rank compression, tensor embedding, dimension-ratio coefficient, maximally mixed output and partial-trace algebra | Representation-theoretic restriction/isometry identities |
| `BlockFidelity`, `ClassicalFidelity` | Classical Hellinger continuity, data processing, block summation, and the exact `η + 2√ε` factorization estimate | The uniform sector estimate and its representation-theoretic instantiation; concrete direct sums and quantum deletion are now proved |
| `MatrixFidelity`, `Scaling`, `Tensor`, `Blocks`, `Embedding`, `Normalization` | Actual spectral root fidelity; scalar, tensor and dependent direct-sum laws; isometric invariance; diagonal classical fidelity; canonical trace normalization and maximally mixed states | Application-specific representation identifications |
| `MatrixFidelityLifted`, `MatrixFidelityLimit`, `MatrixLiftedChannel` | Exact fidelity of lifted matrix blocks; quantitative sector-error propagation; concrete channel outputs and their trace laws; growing-dimension fidelity convergence without an assumed block formula | Physical Schur identification; global lifted channel on arbitrary inputs; sector/label limits |
| `MatrixFidelityProjector`, `MatrixFidelityBounds` | Actual operator-monotone fidelity domination and finite matrix projector converse; Hilbert–Schmidt trace bounds; qualitative continuity on the finite-dimensional positive cone | Physical invariant-output identification and dimension-moment asymptotics |
| `MatrixRegularization`, `MatrixTraceOrder`, `MatrixSqrtSubadditivity`, `MatrixFidelityTraceBound` | Positive regularization including singular limits; inverse-order trace comparison; square-root trace subadditivity; `F(A,B)² ≤ Tr A Tr B` and `F ≤ 1` | Application to the representation-theoretic sector approximations |
| `MatrixFidelitySymmetry`, `MatrixFidelityContinuity`, `MatrixFidelityDeletion`, `InfinitePowersStormer`, `InfiniteFidelityContinuity` | Finite and infinite symmetry, dimension-independent trace-norm continuity, and positive deletion; exact finite lifted `hquantum` estimate | Application-specific approximation estimates |
| Finite and infinite `FidelityWitness`, `FidelityBlockBound`, `ChannelFidelity` | Constructed attaining witnesses, positive block trace bounds, and fidelity data processing for actual CPTP channels, including singular inputs | Physical channel constructions |
| `MatrixTraceNormOrder`, `MatrixChannelTraceNorm`, `InfiniteTraceClassChannels` | Finite and infinite Jordan decomposition and trace-distance contraction; automatic continuity of actual positive trace-preserving trace-class maps | Construction of the application-specific channels |
| `MatrixDiscardLabel`, `MatrixFidelityJointConcavity` | Actual label-discarding CPTP channel on all matrix inputs; fidelity superadditivity, strong concavity, and joint concavity | Application-specific uniform mixture estimates |
| `MatrixWeightedFidelity`, `InfiniteFidelityWeighted`, `InfiniteFidelityRegularized` | Noncommutative finite and infinite weighted-fidelity inequalities, including removal of positive regularization under an inverse-moment bound | General covariant-channel representation; concrete seeded-family moment bounds are now proved |
| `MatrixFidelityAsymptotics`, `MatrixLiftedTrimming` | Actual pairwise transition filtering, deleted-mass trace identity, finite factorization, and growing-dimension limit without `hquantum` | Uniform sector approximation, concentration and label limits, physical Schur realization |
| `MatrixFidelityMixtures`, `MatrixFidelityAchievability`, `MatrixTransitionAchievability` | Operator concavity of square root; actual fidelity concavity; conditional mixtures of channel outputs; actual achievability with error `η + √δ` from individual retained-pair lower bounds | Uniform individual sector lower bounds and classical asymptotics; exact mixture limits require additional upper control |
| `Rounding`, `YoungRounding`, `GaussianAffinity` | Actual countable rounding PMF, cell volumes, interpolation/dilation identities, L¹ contraction and averaging convergence; actual Gaussian affinity integrals | Young root-chart/measure identification, compatibility fallback, local density estimates and compact-spectrum uniformity |
| `Occupation`, `CountableScheffe`, `WernerNormalization`, `WernerAsymptotics`, `PoissonApproximation` | Exact occupation normalization, stars-and-bars counting, actual Werner-to-geometric and binomial-to-Poisson limits in ℓ¹ | Identification with the manuscript’s physical representation/channel outputs |
| `InfiniteTraceClass*`, `InfiniteHilbertSchmidt`, `InfiniteDensityState` | Genuine trace-class Banach space; trace-norm rank-one series, analytic states, separability, positive weak limits with trace loss, and normal-part agreement on all compact observables | Physical bosonic constructions |
| `InfiniteCompletelyPositiveCompactness`, `InfiniteAsymptoticCPCompactness`, `InfiniteChannelCovariance` | Actual common-subsequence CP-map extraction, convergence on every compact observable, `limsup` trace bounds, and exact covariance of the same limit | Construction and estimates of the manuscript’s averaged/weighted Gaussian maps |
| `Thermal`, `InfiniteDiagonalFidelity`, `BosonicAmplifierThermal`, `ThermalWitness`, `MultimodeThermalIdlerFidelity` | Actual amplifier thermal outputs, compact witness identities, and exact fidelity optimum over all joint seeded idler states | Weyl-covariant representation and composite-gain reduction; physical PCT output identification |
| `Moments`, `InfiniteFidelityRegularized`, `InfiniteAsymptoticCPCompactness` | Random-idler scalar coupling, regularized infinite weighted fidelity, actual compact CP limits and final scalar bounds allowing trace loss | Universal Weyl-covariant dilation theorem; hybrid integration and averaging estimates |
| `Projector` | Finite scalar projector converse, dimension-ratio bounds, positive-root/Casimir polynomial identities, and the second-moment bound | Construction of the invariant matrix majorant, Schur–Weyl/Casimir trace identity and dimension-moment asymptotics |
| `LAN`, `MatrixLANTransfer`, `InfiniteLANTransfer` | Abstract, finite-matrix, and genuine Hilbert-space quantum fidelity transfer; minimax/Bayes reduction with proved channel laws and correct order of limits | Physical LAN maps and uniform errors, continuous classical–quantum register model, and Gaussian optimization |
| `Main` | Strictly ordered spectra, correct pair/product formulas, positivity and bounds, strict PCT formula comparison, lifted convergence, conditional known/unknown-spectrum minimax assembly | Instantiation of the remaining inputs with concrete quantum experiments |

In particular, `Cloning.pctValue_lt_universalValue` proves the strict comparison of the explicit limiting formulas for every `d ≥ 2`, `γ > 1`, and simple positive spectrum. It does not establish that PCT’s finite-sample output converges to that formula.

## Reading the main results

The newest entry points are `WernerAsymptotics.lean`, `InfiniteOccupationStates.lean`, `InfiniteDiagonalFidelity.lean`, `InfiniteChannelFidelity.lean`, `InfiniteLANTransfer.lean`, `InfiniteFidelityRegularized.lean`, `InfiniteCutoffChannels.lean`, and `InfiniteAsymptoticCPCompactness.lean`. The resource inventory records external candidates separately from locally checked adaptations.

Start with `Cloning/MultimodeThermalIdlerFidelity.lean`, `Cloning/BosonicAmplifierThermal.lean`, `Cloning/OccupationChannel.lean`, `Cloning/ComplexCoherent.lean`, and `Cloning/YoungRounding.lean` for the new concrete constructions. See `Cloning/InfiniteChannelFidelity.lean`, `Cloning/InfiniteLANTransfer.lean`, and `Cloning/InfiniteAsymptoticCPCompactness.lean` for the latest removal of quantum-law and compactness assumptions; `Cloning/MatrixFidelityAsymptotics.lean` removes `hquantum`. `Cloning/Main.lean` contains the remaining conditional minimax assembly. The main entry points are:

- `InfiniteTraceClass.exists_subsequence_covariant_cp_limit_of_limsup_trace_bound`: the actual common-subsequence compact CP lemma, with asymptotic trace bounds and covariance.
- `InfiniteFidelity.fidelity_data_processing`: actual infinite-dimensional channel fidelity monotonicity.
- `InfiniteLANTransfer.fidelity_transfer`: Hilbert-space comparison with only approximation errors as quantum hypotheses.
- `InfiniteDiagonalFidelity.stateFidelity_productGeometric`: exact multimode thermal fidelity of constructed density operators.
- `InfiniteOccupationStates.occupation_traceNorm_tendsto`: actual Werner occupation-operator trace-norm convergence.
- `MatrixCovariantBalance.cartanChannel_of_irreducible_intertwiner`: actual CPTP Cartan channel with its balancing identity derived by Schur's lemma.
- `GaussianAffinity.integral_product_dilation_eq_classicalValue`: actual Gaussian integral equal to the manuscript's classical factor.
- `CountableScheffe.discrete_scheffe` and `sqrt_amplitudes_tendsto_of_pointwise`: normalized pointwise convergence upgraded to ℓ¹ and amplitude convergence.
- `InfiniteTraceClass.TraceClass.instCompleteSpace` and `InfiniteTraceClass.trace_mul_cycle`: genuine trace-class completeness and cyclicity.
- `InfiniteTraceClass.DensityState.pure`: a positive trace-class pure state with analytic trace one.
- `MatrixFidelity.fidelity_data_processing`: actual finite-channel fidelity data processing for all PSD inputs.
- `Channels.MatrixChannel.traceNorm_contract_sub`: actual trace-distance contraction.
- `MatrixLANTransfer.fidelity_transfer` and `minimax_le_bayesValue`: concrete finite-experiment transfer with all finite quantum laws proved.
- `MatrixFidelity.fidelity_strong_concavity` and `fidelity_joint_concavity`: finite simultaneous mixtures of both arguments.
- `MatrixFidelity.fidelity_sq_le_weighted_trace_product`: finite noncommutative weighted-fidelity bound.

- `MatrixTransitionAchievability.transition_achievability_bound`: actual-channel lower bound from individual retained-pair fidelity estimates, with error `η + √δ`.
- `MatrixFidelity.lifted_matrix_eventual_achievability`: eventual lower approximation with growing dimensions, requiring only one-sided sector estimates.
- `MatrixFidelity.lifted_matrix_fidelity_converges`: the growing-dimension matrix theorem with the quantum deletion hypothesis discharged.
- `MatrixLiftedTrimming.lifted_transition_factorization_bound`: the quantitative result for concrete masked channel transitions.
- `MatrixFidelity.fidelity_continuity_of_traceNorm_le`: the dimension-independent `√ε + √η` perturbation bound.
- `MatrixFidelity.fidelity_lifted_blocks`: the exact concrete block formula displayed above.
- `MatrixFidelity.weighted_lifted_fidelity_converges`: actual matrix-fidelity convergence from sector and classical-label estimates, when every positive-weight sector satisfies the approximation.
- `MatrixLiftedChannel.liftedOutput_fidelity`: the exact formula for outputs assembled from concrete sector channels.
- `MatrixFidelity.finite_matrix_projector_converse`: derives the scalar converse from a concrete matrix majorant, removing the former abstract fidelity-domination premise.
- `lifted_fidelity_converges`: proves convergence from the finite block estimates, allowing label spaces to grow with sample size.
- `known_spectrum_optimum_of_bounds` and `unknown_spectrum_optimum_of_bounds`: conditional minimax completion. Their assumptions include the substantive asymptotic bounds, and are not a proof of those bounds.
- `LAN.lan_minimax_le_bayesValue`: integrates the actual channel-composition transfer with minimax/Bayes optimization.
- `CartanChannel.cartanChannel`: a concrete CPTP matrix channel under the explicit balanced-partial-trace identity.

`PROOF_AUDIT.md` maps the manuscript’s theorem labels to the missing mathematics and reviews the code’s semantic scope. Failure to formalize an input is not evidence that the manuscript claim is false. The audit did not establish a definite mathematical error in the reviewed manuscript arguments.

## Reproducing

With Elan installed and network access for the pinned dependencies:

```sh
lake exe cache get
lake build
lake env lean -DautoImplicit=false Audit.lean
```

For an existing compiled Mathlib dependency tree, use the optional local checker:

```sh
CLONING_LEAN=/absolute/path/to/lean \
CLONING_PACKAGES=/absolute/path/to/.lake/packages \
python3 check_local.py --jobs 3

CLONING_LEAN=/absolute/path/to/lean \
CLONING_PACKAGES=/absolute/path/to/.lake/packages \
python3 audit.py --jobs 3
```

For local iteration with unchanged external dependencies, `check_local.py --incremental` skips unchanged local imports; the recorded final build starts with an empty output tree, compiles every module and the umbrella, and checks every build-input source hash. The helper’s defaults describe the installation used for this run; override them on another machine. It does not change the external dependency checkout. Its default target is the umbrella `Cloning.lean`, and it sorts all local imports before checking. The ordinary Lake build is the portable project configuration; this session verified directly against the installed pinned libraries.

## Source provenance

The attachment download failed. The working manuscript was a local `cloning.tex` with the same filename and exact byte count as the attachment metadata. The SHA-256 and this limitation are recorded in `SOURCE.json`; attachment identity was not verified byte for byte. The original and synced manuscript files were not modified.
