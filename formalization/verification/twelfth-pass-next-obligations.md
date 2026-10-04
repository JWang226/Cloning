# Concrete obligations after the twelfth-pass constructions

This is a read-only mathematical roadmap. Proposed endpoints are not additional Lean proofs. The new completed components and their quantifier boundaries are recorded in the accompanying semantic review and current progress report.

## 1. Complete physical tensor decomposition

The actual cyclic irreducible copy, exact highest-weight Gram isometry, literal tensor covariance and Cartan channel remove the former representation-interface assumptions. A full physical decomposition still needs every copy, not one chosen copy per partition.

A direct route avoids introducing simultaneous diagonalization machinery. Let W be any nonzero subspace invariant under all actual collective generators and let P be its orthogonal projection. The proved `invariant_starProjection_commutes` gives

E_aa(P e_w) = occupancy(w,a) P e_w

for each computational word w. Some P e_w is nonzero, since the computational basis spans and P is nonzero. Choose such a word minimizing the finite integer height

H(w) = sum_a a.val * occupancy(w,a).

If a raising operator E_ab with a<b did not annihilate P e_w, its nonzero computational coefficients would have height H(w)+a−b. The raised vector remains in W. Self-adjointness of P shows that a nonzero coefficient at a word v forces P e_v to be nonzero, contradicting minimality. The resulting vector has a natural occupancy weight and is annihilated by every raise.

Normalize it. The exact commutator and adjoint identities then give

||E_ba Ω||² = μ_a−μ_b ≥ 0,

so μ is a partition. The total occupancy is n. A concrete next endpoint is `exists_partitionHighest_in_invariant`, with conclusions Antitone μ, sum μ=n, Ω∈W, norm Ω=1, and the exact raising/Cartan identities.

Available APIs include `collectiveGenerator_diagonal_basis`, `collectiveGenerator_commutator`, `collectiveGenerator_diagonal`, `Submodule.inner_starProjection_left_eq_right`, `Cloning.PCT.register_operator_ext`, `root_diagonal_commutator`, `collectiveGenerator_inner_adjoint`, and `sum_occupancy`.

Lowering-word induction puts the entire cyclic sector in W. Split it off orthogonally. The residual W∩S⊥ is still generator invariant because the generator family is closed under adjoints, and its dimension is strictly smaller. Finrank induction yields a finite orthogonal direct sum spanning the full register. Each summand is exactly isometric to its chosen partition sector by `highestCyclicIsometry`, with literal tensor covariance already proved.

This gives a decomposition with repeated partition labels. It does not yet identify multiplicities, characters, or dimensions with their combinatorial formulas. Those are the subsequent obligations:

- sector character = `YoungGeneral.schurPolynomial`;
- multiplicity = `YoungGeneral.standardCount`;
- the physical tensor-state block formula;
- physical Schur measurement probability = the constructed `tableauPMF`.

A one-box tensor branching proof could identify multiplicities before the full character formula. For a highest vector v=sum_j v_j⊗e_j in S_μ⊗C^d, choose the largest r with v_r nonzero. The raising equations E_ab v_j+δ_ja v_b=0 imply that v_r is a highest vector of S_μ, hence a scalar multiple of Ω_μ. The total weight is therefore μ+e_r. On each fixed highest-weight space this r-component map is injective, giving multiplicity at most one and excluding other labels.

Existence of each addable branch can use explicit wedge contraction. For addable row r, let η=μ−1_(a<r). Then μ=η+column(r) and μ+e_r=η+column(r+1). Project Ω_η⊗col_(r+1), reassociated into N factors and one factor, onto cyclicSector(Ω_η⊗col_r)⊗C^d. The projection commutes with every total generator and preserves highest/weight data. Contracting the last wedge factor with e_r gives a nonzero multiple of col_r, proving the projected vector is nonzero. Transport through the already proved exact Gram isometry to the canonical S_μ. The new concrete lemmas would be the wedge last-slice identity, reassociation and tensoring the sector isometry. Iterating this branching from the vacuum gives the predecessor recurrence for physical highest-space multiplicities. The existing exact `YoungGeneral.standardCount_succ` theorem then identifies them with standardCount, from the empty-tensor base case. The physical character formula is still separate: matching Pieri recurrences only identifies sums of successor characters, not individual characters. A remaining precise bridge is equality between each actual Cartan weight-space dimension and the semistandard-tableau count for that content.

A conversion from hypotheses phrased solely as U(d)-invariance to Lie-generator invariance is optional for this construction: start with the full register and maintain generator invariance in the orthogonal recursion.

## 2. Complete retained weight frames and Cartan approximation

The exact cyclic isometry is defined on the full sector, but the asymptotic oscillator identification still uses fixed finite words. Prove ordered-monomial spanning of each lowering-word cutoff by adjacent swaps. The swapped commutator replaces two generators by a shorter word of the same total root height. An induction on length and inversions should terminate while preserving the cutoff.

Use an explicit ascending root key rank(i,j)=d*i+j; the current PositiveRoot subtype has no linear order. For lowering roots α=(i,j), β=(k,l),

[L_α,L_β] = 1_(i=l) L_(k,j) − 1_(k=j) L_(i,l).

Both possible merged roots are positive, preserve the sum of root heights and preserve the full Cartan shift. For an adjacent inversion in the stated lexicographic key, the negative case k=j is impossible. Swapping reduces inversion count at unchanged length; merging reduces length. The lexicographic measure (word length, inversion count) therefore proves termination. Define canonicalWord(k) by repeated roots in this order, and index the cutoff by occupations with sum_α height(α)*k_α≤R. Positive root heights bound every occupation by R, making this a finite index. Exact straightening gives equality of this span with the whole cyclic cutoff; the earlier all-root eventual independence then gives a genuine basis for fixed R when all gaps diverge.

Prove exact Cartan weights of ordered monomials, then choose orthonormal frames separately within each weight block. The earlier Gram convergence gives eventual independence for a fixed retained family; it is not by itself a spanning theorem. For simple spectra all positive roots are retained. Repeated-spectrum blocks require additional care because omitted-root words remain in the full cyclic sector.

The output frame at sector ν and cutoff L must be chosen independently of the incoming label μ. Prove exact Cartan splitting in lowering words, the fixed-cutoff binomial limit in these common frames, and tail bounds for the physical sector states. Only then can the actual all-input lifted channel be combined with the earlier fidelity-mixture estimates to prove retained-mixture convergence.

For thermal tails, ordered spanning bounds the actual height-h spectral multiplicity by (h+1)^s, where s is the number of positive roots. In a fixed neighborhood of a positive strictly decreasing p, bound all adjacent ratios by q̄<1. Every lowering root i<j then contributes at most q̄^(j−i), so the height-h Gibbs eigenvalue relative to the highest one is at most q̄^h. The normalized partition function is at least one. Consequently the tail outside the height-R cutoff is bounded uniformly in the partition by sum_(h>R) (h+1)^s q̄^h, which tends to zero. Use actual spectral multiplicities; summing nonorthogonal PBW projectors would not justify this trace bound. `summable_pow_mul_geometric_of_norm_lt_one` and binomial expansion cover the scalar summability.

If exact flat weight blocks are present, omitted Levi lowerings annihilate the highest vector by the raw-root estimate at height zero. Ordering retained roots before Levi roots and straightening can then put a vanishing Levi suffix on the right. Small but nonzero omitted gaps cannot be removed by this argument; the strict-spectrum all-root case remains the direct first target.

The Cartan channel uses actual finite dimensions. Weyl dimension formulas and their asymptotics still need identification with these dimensions; they are not supplied by the channel's trace-preserving proof.

## 3. Uniform Young local limits

The normalized tableau PMF and its concentration are already constructed. Physical identification follows the decomposition/character/multiplicity chain above. A uniform local central limit still needs exact finite formulas plus compact-uniform Stirling and Taylor bounds, with the correct hyperplane cells and normalization. Existing tail concentration does not imply a local density estimate. `roundedDensity_l1_of_local_limit` continues to require that decisive estimate.

The explicit whitening chart now provides a valid coordinate measure and a bijection of all hybrid competitors. If a proof uses intrinsic hyperplane volume instead, its density/Jacobian conversion must be proved explicitly. Alternatively, build the LAN output directly in the whitened coordinates already used by the Gaussian theorem.

## 4. Physical mixed-state LAN

Construct actual forward and reverse mixed CPTP channels, fixed at each sample size before choosing a local window. Prove their trace-norm/L1 approximations uniformly on every fixed compact window. Two distinct analytic tasks remain: retained-sector state approximation and convergence of the physical local-unitary action to Weyl displacement. Gram convergence alone does not prove the latter.

For the converse, use the already proved sharp mixed transfer at a fixed local window, take sample size to infinity uniformly over competitors, and only then enlarge the window. The target sample rescaling must stay in a common compact set. The unknown-spectrum theorem retains the nonempty regular-closure hypothesis; lower-dimensional spectral families do not automatically incur the full classical Gaussian cost.

For global achievability, either finish the explicit physical Schur–Cartan implementation using the now constructed sector and lifted channels, or prove a genuine localization/globalization protocol. A local Gaussian channel by itself is not a global cloner.

## 5. Physical PCT fidelity

The joint Gaussian law, exact hybrid tangent mixture, comparison fidelity `pctValue`, exact local chart and dominated mixture-transfer steps are now proved. The remaining substantive application input is the physical two-way mixed-state LAN approximation from the preceding section.

For each fixed tangent z, the actual frame particle eventually has exact local parameters converging to the proved classical/orbital tangent coordinates. These parameters lie eventually in a fixed compact window. Apply compact-uniform LAN there and continuity of hybrid translation. Integrate the resulting scalar error norms using the proved bound by two. No uniform approximation over the unbounded Gaussian support is required.

Combine these two integrated approximation limits with `PCTGlobal.channel_gaussian_product_mixture`, the seed approximations and `fidelity_tendsto_of_mixed_mixture`. The target size is L=m_n and the tangent variance is γ−1. There is no additional factor sqrt(γ) in the local displacement.

The required channel quantifiers matter: the same T_L,S_L must work on every fixed compact parameter window. A theorem of the form “for every K there exist channels depending on K” needs another diagonalization/truncation argument before it can handle all tangent z in the mixture. A merely pointwise fixed-parameter LAN theorem also does not directly handle the moving exact chart parameters θ_L(z). Compact-window uniformity implies the required sequential statement by the proved continuity of hybrid translation.

The physical approximation is at output size L=m_n=n+r_n, including the reference state p^⊗m_n. LAN at zero supplies the two seed limits. The existing reduced-product-mixture integrability and translation norm conservation supply integrability of both physical and hybrid components. Several small adapters remain to be packaged: the diagonal canonical purification equals the Schmidt vector, literal tensor powers have the normalized positive-state wrappers, and the all-complex tensor lift agrees with the matrix tensor-power notation.

For a non-diagonal base ρ=U diag(p) U*, transport the already proved physical Gaussian mixture by U* on each system factor and the purification coefficient frame by M↦U* M U. The resulting frame-particle and reduced-state identities connect it to the diagonal chart. Existing square-root equivariance, partial-trace covariance and tensor-power multiplication/star formulas support this step. It does not require proving PCT-channel covariance first. This transport adapter is still separate from the current diagonal Schmidt-coordinate chart.

The smaller rank-adapted purification environment remains a separate construction. The current physical channel uses the full environment.
