# Concrete proof obligations after the eleventh pass

This is a read-only proof analysis, not a collection of additional Lean theorems. Proposed declaration names below describe work still to be formalized. The eleventh-pass constructions and their precise proved scopes are recorded in [PROGRESS.md](../PROGRESS.md) and the [semantic review](eleventh-pass-review.md).

## 1. Cyclic-sector scalarity before full Schur decomposition

For the actual normalized highest tensor Ω, define the full cyclic sector as the span of all `TensorLie.loweringWord Ω w`. The existing `generator_mem_cyclicCutoff` already controls each generator on every finite lowering word, so invariance of the full span should be immediate from span induction. The generator adjoint formula gives closure under adjoints.

A minimal next chain is:

```text
cyclicSector_generator_invariant
cyclicSector_raising_kernel_eq_span_highest
cyclicSector_commutant_scalar
cyclicSector_irreducible
```

To prove the joint raising kernel is the highest-vector line, move the first lowering operator in each nonempty word across the inner product. Its adjoint is a raising operator and annihilates the tested vector. Subtract the scalar multiple of Ω determined by the empty word; the remainder is orthogonal to the entire cyclic span and belongs to it, hence vanishes. This avoids a classification theorem or root-height descent argument.

An operator commuting with every generator sends Ω to this line and therefore acts by the same scalar on every lowering word. If a subspace is invariant under all generators, adjoint closure makes its orthogonal projector commute with them. Scalarity and idempotence then yield irreducibility.

This produces one concrete irreducible cyclic copy. It does not produce every multiplicity copy in the physical tensor power.

## 2. Exact Cartan inclusion and complete weight frames

`tensorJoin_norm_one`, `tensorJoin_raising_zero`, and `tensorJoin_cartan` already give a normalized highest tensor of weight μ+ω in the tensor product of the two cyclic sectors. It need not equal the separately chosen `partitionHighestTensor (μ+ω)`, since the tensors can lie in different ambient multiplicity copies.

Construct an exact isometry by proving that all inner products of unnormalized lowering words depend only on the highest weight and unit normalization. Commuting raising generators through lowering words with the literal Lie relations gives a recursive candidate proof. Equality of the Gram forms then gives a well-defined isometry between the spans. Proposed endpoints are `loweringWord_inner_eq_of_same_highest_weight`, `cyclicHighestEquiv`, `cartanEmbedding_highest`, and `cartanEmbedding_generator`.

The asymptotic PBW Gram theorem cannot replace this exact Gram identity: an exact finite-sample channel needs an exact intertwining isometry. Once suitable unitary representation data are packaged, `MatrixCovariantBalance.balanced_partialTrace_of_intertwining` and `cartanChannel_of_irreducible_intertwiner` already supply balance and CPTP. A direct Lie-generator partial-trace commutator identity plus cyclic scalarity is another route to balance before group representation packaging.

The current finite-word Gram limits and eventual independence do not prove complete cutoff spanning. The full cyclic cutoff spans every lowering word, whereas the new Gram matrix theorem tests a fixed family of distinct occupations. Next prove ordered-monomial spanning by swapping lowering generators and controlling the commutator term, preserving total root height. Establish exact Cartan eigenvalues of those monomials, then orthogonalize within each exact-weight block. The resulting frame must stay a weight frame.

For the mixture argument, the output frame J_(ν,L) must depend on the output sector ν and cutoff L, and be independent of the incoming sector μ. Prove exact Cartan binomial splitting, its fixed-cutoff approximation in these frames, and uniform tail bounds. Individual sector fidelity convergence only supplies a mixture lower bound through concavity; it does not imply exact fidelity convergence of arbitrary retained mixtures.

When roots inside zero-gap blocks are omitted, retained-root independence alone does not establish full sector completeness. The regular-spectrum case retains all roots and is the natural first target.

## 3. Physical Schur identity, Young law, and lifted CPTP map

The normalized tableau PMF is combinatorial. Its concentration uses a polynomial domination bound that deliberately avoids hook and Weyl formulas. Neither RSK normalization nor that concentration proves the physical character/dimension identities or a local central limit theorem.

The required physical decomposition has the exact form

\[
U_N\rho^{\otimes N}U_N^*
=\bigoplus_\mu\pi_\mu(\rho)\otimes I_{M_\mu},
\qquad\dim M_\mu=f_\mu.
\]

It needs a complete orthogonal tensor decomposition, not just one cyclic copy per partition. Concrete targets are physical character equality with `schurPolynomial`, cyclic-sector dimension equality with the Weyl formula, multiplicity equality with `standardCount`, and the exact tensor-state block formula. Only then does physical Schur measurement have the already-constructed `tableauPMF` law.

Independently, the general uniform Young local limit needs exact finite formulas plus compact-uniform Stirling/Taylor control and cell normalization. `YoungRounding.roundedDensity_l1_of_local_limit` still assumes the decisive local density estimate; concentration controls tails but cannot discharge it.

An additional all-input channel construction must also be supplied. `MatrixLiftedChannel` defines output states and their formulas, not a global CPTP map implementing all the stages. A `liftedKernelChannel` can use explicit block Kraus operators to measure the input label, discard its multiplicity, apply the sector channel, sample the output label, and prepare the output multiplicity state. Its completeness identity must hold on the entire input matrix space. `FiniteKrausLift` converts such a constructed matrix channel to the actual trace-class channel; it does not construct the block Kraus family itself.

## 4. Actual mixed-state LAN

The new mixed CP/TP interfaces, both fidelity monotonicity directions and sharp transfer solve the cross-type channel bookkeeping. They do not produce physical LAN channels or approximation estimates.

For each fixed simple full-rank base spectrum, construct S_N and T_N independently of the local window. Prove uniform approximation on every fixed compact local window in the actual trace norm and operator-valued L1 norm. The local-unitary action must converge to Weyl displacement; PBW Gram convergence alone does not prove this action approximation. The classical coordinate law must be connected to the product-Gaussian model by an actual measure/channel equivalence or by building LAN directly in whitened coordinates.

For the converse, fix a local window, take n→∞ uniformly over all competitors, then enlarge the window. Target scaling at m_n must keep the same base-spectrum chart denominators and fit eventually into a common compact set. The unknown-spectrum minimax extension retains the nonempty regular-closure condition on the spectral set. Singleton or lower-dimensional sets do not automatically incur the full unknown-spectrum classical cost.

For achievability, a local Gaussian channel plus one LAN chart is insufficient to give a global cloner. Either construct and prove localization/globalization or complete the explicit Schur–Cartan channel route.

## 5. Joint hybrid PCT comparison state

The new tangent characteristic gives all classical/orbital tests simultaneously. The new orbital theorem identifies the actual quantum displacement integral without a pushforward-law premise. To identify the full classical–quantum comparison state, one further joint argument is necessary.

A concrete route is:

1. Prove the root fidelity of the literal product field with classical precision a/(2γ−1) and thermal parameters `Thermal.pct γ q`, against the seed with precision a and q. Existing product-field fidelity, Gaussian dilation affinity and product-geometric fidelity give classical factor `classicalBase(2γ−1)^(k/2)` times the PCT quantum factors. Reindexing gives the scalar `pctValue`. This calculation alone does not identify the tangent mixture.
2. Construct a real whitening map on the trace-zero hyperplane with WΣ_pWᵀ=I. Define the joint map J(Z) from actual tangent classical coordinates through W and actual orbital coordinates through the proved mode indexing.
3. Use `jointCoordinate_characteristic` and characteristic-function uniqueness to prove the actual joint pushforward law. It should be a centered real Gaussian of covariance 2(γ−1)I times the circular orbital Gaussian with variance (γ−1)(1+q)/(1−q). The test family must be shown to cover all real linear functionals; factorization alone must not be silently promoted to independence.
4. Prove the operator-valued L1 identity for the Bochner integral of `hybridTranslation (J Z)` applied to the Gaussian seed. Strong continuity and norm preservation give integrability. Rewrite using the actual joint law, then use product Fubini, classical Gaussian convolution and the already-proved quantum displacement integral. The classical covariance becomes (2γ−1)I.
5. Apply the product-field fidelity result to this actual joint integral.

Translation averaging is already available as an actual hybrid CPTP channel, so positivity and normalization can be obtained globally rather than only on the comparison state.

## 6. Exact local-chart control for the PCT mixture

The most direct next route uses an inverse function theorem and does not require an explicit eigenvector selection. Write P=diag(p), and consider the unscaled chart

\[
C_p(h,z)=e^{Y_p(z)}\operatorname{diag}(p+h)e^{-Y_p(z)}-P.
\]

Initially allow all real diagonal h, with target the real space of Hermitian matrices. Domain and codomain have real dimension d². The derivative at zero is the explicit real linear equivalence

\[
L_p(h,z)=\operatorname{diag}(h)+[Y_p(z),P],
\qquad h_i=M_{ii},\quad z_{ij}=M_{ji}/\sqrt{p_i-p_j}.
\]

Strict gaps make it invertible. Mathlib's noncommutative exponential strict derivative at zero and `HasStrictFDerivAt.localInverse` provide the analytic route. Exact trace equality afterward forces Σh_i=0, avoiding a traceless-subspace setup at the outset.

For the genuinely normalized tangent state σ_t(Z), the proved exact remainder gives σ_t−P=tD_p(Z)+O_Z(t²). Differentiability of the local inverse then gives exact eventually valid coordinates θ_t=t⁻¹C_p⁻¹(σ_t−P) tending to the actual (h(Z),β(Z)). Strict differentiability suffices for convergence; the stronger O_Z(t) scaled-coordinate rate would require a quadratic inverse remainder and is unnecessary for the limit.

Set t=L^(-1/2). For each fixed Z, the convergent coordinates eventually lie in a fixed compact parameter ball. Uniform LAN on that ball, the exact chart identity and continuity of actual hybrid translations give the forward/reverse limits. Small coordinates preserve spectral positivity and ordering. There is no need to integrate an eigenvector choice: the original continuous physical state family is the integrand, and the inverse-chart coordinates are only used to prove its pointwise approximation.

An alternative is a full-rank tensor-stability estimate. With both states bounded below by δI, a square-root Hilbert–Schmidt bound and canonical purifications can give

\[
\|\rho^{\otimes L}-\sigma^{\otimes L}\|_1
\le\sqrt{L/\delta}\,\|\rho-\sigma\|_{\rm HS}.
\]

Then an O(L⁻¹) single-copy remainder is sufficient. Bare O(L⁻¹) trace distance without the interior lower bound is insufficient: tensoring `diag(1,0)` and `diag(1−1/L,1/L)` leaves a nonvanishing distance. Neither the full-rank stability bound nor the inverse-chart theorem is yet formalized.

The PCT mixture already uses **L=m_n**, scale **1/√L**, and perturbation variance **γ−1**. Its limit coordinates are directly (h(Z),β(Z)). Adding a further √γ would double-count the target-size scaling.

Finally, integrate scalar error norms bounded by two. This handles reverse errors even though the quantum register changes with L. Pointwise fixed-Z convergence and dominated convergence suffice; no uniform LAN bound over the unbounded Gaussian support is needed. Combine the two integrated LAN approximations with the actual global PCT Gaussian product-mixture theorem, then both mixed data-processing inequalities and fidelity continuity squeeze the physical fidelity to the comparison value. The smaller rank-adapted purification construction remains separate.
