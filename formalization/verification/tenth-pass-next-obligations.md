# Reviewed plan, not completed proofs

This document records a read-only review of the remaining physical mixed-state
LAN and cloning obligations after the tenth-pass Gaussian optimum and Young
normalization results. It is a proof plan and scope analysis, not a declaration
that the missing constructions or approximation estimates have been proved.
No conclusion supplied as a premise to a conditional theorem is counted as closed.

The reviewed sources are the current `Cloning/LAN.lean`,
`Cloning/InfiniteLANTransfer.lean`, `Cloning/MatrixLANTransfer.lean`,
`Cloning/Main.lean`, the hybrid channel/fidelity modules, the Young and
Schur-sector interfaces, and `reference/cloning.tex`, especially the sections on
achievability, two-way LAN, minimax completion, the Young local limit, and PCT.

## 1. Minimum physical converse chain

For each fixed simple full-rank base spectrum `p`, construct actual channels

\[
T_N:\mathcal T_1((\mathbb C^d)^{\otimes N})
  \longrightarrow L^1(\mathsf H;\mathcal T_1(\mathcal F)),
\qquad
S_N:L^1(\mathsf H;\mathcal T_1(\mathcal F))
  \longrightarrow\mathcal T_1((\mathbb C^d)^{\otimes N}).
\]

Here `H` is the real sum-zero hyperplane and the Fock space has one mode for
each pair `i < j`. The channels must be completely positive and trace preserving
on their entire operator spaces. They may depend on `p` and `N`, but must be
chosen independently of the unknown local parameter and before choosing a compact
parameter window.

For every fixed compact `C`, prove forward and reverse approximations, uniform
over `(h,z) ∈ C`, for the actual local family

\[
\rho_{p+h/\sqrt n,\exp(Y_p(z)/\sqrt n)}^{\otimes n}
\quad\leftrightarrow\quad
\mathsf N_{h,\Sigma_p}\otimes D(z)\tau_pD(z)^*.
\]

The error is the full trace norm on quantum operators and the actual
operator-valued `L1` norm on hybrid fields. Neither the mixed-state channel
construction nor these quantitative estimates is supplied by the current LAN
interfaces. The compact-uniform channels in
`GeneralCoherent.exists_twoWay_coherent_product_channels` handle the explicit
pure-product model; they do not establish mixed-state LAN.

For the minimax upper bound alone, the required approximations are narrower:
reverse approximation of the input by `S_n`, and forward approximation of the
target by `T_(m_n)`. The forward approximation at general sample size is a route
to the latter, rather than an extra independent converse premise.

## 2. Exact missing mixed CP/TP interfaces

`InfiniteLANTransfer` handles Hilbert-space trace-class channels, and
`MatrixLANTransfer` handles finite matrix channels. `Hybrid.Channel H K μ`
currently handles `L1(μ; TraceClass H) → L1(μ; TraceClass K)` with the same
classical reference measure. Full LAN needs both cross-type directions.

A minimal quantum-to-hybrid structure would contain a bounded complex-linear map

```text
T : TraceClass H →L[ℂ] Lp (TraceClass K) 1 μ
```

with these exact laws:

- For every natural number `n` and every block
  `A : Fin n → Fin n → TraceClass H`, `BlockPositive A` implies
  `∀ᵐ y ∂μ, BlockPositive (fun i j => T (A i j) y)`.
- For every complex trace-class input `A`,
  `∫ y, traceCLM (T A y) ∂μ = traceCLM A`.

A minimal hybrid-to-quantum structure would contain

```text
S : Lp (TraceClass H) 1 μ →L[ℂ] TraceClass K
```

with these laws:

- For every `n` and block `A : Fin n → Fin n → Lp (TraceClass H) 1 μ`,
  `∀ᵐ y ∂μ, BlockPositive (fun i j => A i j y)` implies
  `BlockPositive (fun i j => S (A i j))`.
- For every complex `L1` input `A`,
  `traceCLM (S A) = ∫ y, traceCLM (A y) ∂μ`.

These laws concern all inputs, not merely the model states. Composition must
produce an actual `Hybrid.Channel` for `T ∘ M ∘ S`, where `M` is any physical
quantum competitor, and an actual quantum channel for compositions in the other
direction. Preparation by a normalized scalar density and unweighted integration
already have useful positivity, trace, and norm lemmas in the weighted-map modules;
those special operations do not by themselves establish arbitrary mixed channels.

The essential additional data-processing theorem for the upper bound is

\[
F_Q(A,B)\le F_{CQ}(T A,T B).
\]

There is a direct proof route using the existing quantum fidelity block theorem:
choose the single attaining trace-class witness from
`InfiniteFidelity.exists_fidelityBlock_witness`, transport its positive `2 × 2`
block by mixed CP, apply `trace_re_le_fidelity_of_block` almost everywhere, and
integrate. Mixed TP retains the witness objective. This direction needs no
measurable choice of pointwise attaining witnesses. Adjoint preservation must also
be derived so that the transported block has the correct off-diagonal entries.

The reverse inequality

\[
F_{CQ}(R,Q)\le F_Q(SR,SQ)
\]

is needed for the reverse PCT comparison and suitable achievability transfers.
It needs a further proof, for example by positive simple-field approximation and
finite block witnesses, or directly for the structured reverse LAN maps.
`Hybrid.PositiveField.rootFidelity_map_le` proves only the fibrewise quantum-channel
case. It must not be used as if it established arbitrary mixed-channel monotonicity.

Trace-norm contraction on differences of positive inputs should accompany these
interfaces. For quantum-to-hybrid maps, the ordinary quantum Jordan decomposition
and mixed positivity/TP provide a direct route. A uniform boundedness constant
would suffice to obtain a vanishing transfer error, but the exact manuscript
modulus uses contraction with constant one.

## 3. Required uniformity, target scaling, and order of limits

For a fixed local window `C`, the transfer hypotheses are

\[
\delta_n=\sup_{\theta\in C}\|S_n\Phi_\theta-\rho_{n,\theta}\|_1\to0,
\qquad
\eta_n=\sup_{\theta\in C}\|T_{m_n}\sigma_{n,\theta}-\Psi_\theta\|_1\to0.
\]

They imply a fidelity error `sqrt δ_n + sqrt η_n`, uniformly over the window and
every competing channel. The norms have no extra factor `1/2`.

Target-sample scaling must keep the same base spectrum in the chart denominators.
Writing `γ_n = m_n / n → γ > 1`, prove the exact local-state identity

\[
\rho_{p+h/\sqrt n,g_{n,z}^{(p)}}
=\rho_{p+\sqrt{\gamma_n}h/\sqrt{m_n},
         g_{m_n,\sqrt{\gamma_n}z}^{(p)}}.
\]

Then apply forward LAN at sample size `m_n` on a common compact set containing
the eventually rescaled parameters, and use uniform trace-norm continuity of
Gaussian translations and Weyl conjugation. Local spectra must be shown admissible
throughout each fixed window for all sufficiently large `n`.

The converse limit order is:

1. Fix an interior base spectrum and a finite local window `L`.
2. Take the supremum over all finite-sample competitors, using a transfer error
   independent of the competitor.
3. Let `n → ∞` with `L` fixed.
4. Let `L → ∞`, applying the proved optimized Gaussian limit, whose channel
   supremum is already before the window limit.
5. For the unknown-spectrum problem, bound at each interior base spectrum and
   then extend by continuity and density to the infimum over the compact set.

No diagonal growing-window LAN statement is needed. The upper bound also does not
require LAN uniform over all base spectra in `K`; fixed-base estimates suffice.
Uniformity over compact spectral sets is required for the manuscript's candidate
achievability statement. The unknown-spectrum minimax theorem must retain
`K = closure (relativeInterior K)` and nonemptiness. Singleton and lower-dimensional
spectral sets do not automatically incur the full unknown-spectrum classical cost.

## 4. Coordinate transport to the proved Gaussian model

The formal hybrid optimum uses a product classical Gaussian density on
`Fin k → ℝ`. The manuscript uses covariance `Σ_p = diag(p) - p pᵀ` on the root
hyperplane. `YoungHyperplaneCovariance` supplies positivity, determinant, and inverse
quadratic identities. `GaussianAffinity.integral_product_dilation_map_equiv`
supplies scalar affinity invariance under a common coordinate change. It does not
yet transport arbitrary competing channels or their CP/TP laws.

A genuine measure/channel coordinate equivalence, with fidelity and trace-norm
preservation, remains necessary. One efficient choice is to state the new LAN
construction directly in whitened coordinates. The local chart can then use compact
boxes in those coordinates; the abstract minimax restriction accepts such a chart.
This avoids proving that the manuscript's literal boxes remain boxes after
whitening. Mode reindexing and identification of `q_ij = p_j / p_i` with the product
Gaussian seed are also finite-dimensional assembly tasks, not new Gaussian bounds.

The vacuum-mode extension of the Gaussian optimum does not establish physical LAN
at degenerate or rank-deficient spectra. The full-rank local chart still requires
positive spectral coordinates and positive adjacent gaps.

## 5. Physical achievability remains a separate branch

The physical Gaussian amplifier attains the limiting Gaussian value. Combining it
with LAN on one fixed local chart does not alone construct a global finite-copy
cloner with a uniform orbit/spectrum guarantee. Such a route would additionally
need a proved localization/globalization procedure. The manuscript instead uses
explicit Schur–Cartan channels.

For that route, construct arbitrary-partition irreducible sectors and normalized
highest vectors, the physical Schur decomposition, the exact tensor-power block
state formula, and normalized Cartan intertwining isometries. The theorem
`MatrixCovariantBalance.cartanChannel_of_irreducible_intertwiner` derives an actual
CPTP map from supplied irreducible unitary representations and an intertwining
isometry; it does not construct those data for the physical sectors.

The current literal `TensorLie` highest vector has weight `(n,0,...,0)` only.
Applying the proved PBW estimates to typical mixed-state sectors still requires
normalized local CCR defects `O_L(n^(-1/2))`, exact-weight spanning and
orthonormalization, and the Cartan splitting estimates. In particular,
`PBW.normalized_gram_error_le_of_root_filtration` assumes the cutoff commutator
defect bound; it does not derive it from the physical highest weights.

For exact fidelity convergence of arbitrary retained mixtures, the manuscript
requires a common output-sector frame independent of the input label, uniform
fixed-cutoff trace-norm approximation of both sector output and target, and a
uniformly vanishing thermal tail. First let `n → ∞` at fixed cutoff, then remove
the cutoff. Individual transition fidelity convergence is insufficient to conclude
the same fidelity for arbitrary mixtures.

There is a weaker route when only a lower bound is needed:
`MatrixTransitionAchievability.transition_achievability_bound` uses a uniform lower
fidelity bound on retained transitions and supplies the mixture lower bound by
concavity. The stronger exact candidate-fidelity statement needs the common-frame
approximation described above.

## 6. Young probability law versus its local Gaussian approximation

`YoungGeneral.tableauPMF` now constructs the normalized tableau law without a
normalization or exact-law premise. Its concentration, fallback, and dimension
moment consequences apply to that constructed law. Identification with the actual
physical Schur measurement remains a representation-theoretic obligation.

Independently, the compact-spectrum uniform Young local limit remains to be proved:

\[
\sup_{p\in K}\|\mathcal I_{N,p}P_{N,p}-\varphi_{0,\Sigma_p}\|_1\to0.
\]

`YoungRounding.roundedDensity_l1_of_local_limit` explicitly assumes `hlocal`, the
local density estimate on every fixed ball. Normalization and concentration do not
discharge it. The manuscript obtains it from character normalization, dimension
formulas, uniform Stirling/Taylor estimates, cell geometry, and Gaussian tails.
The generic local-to-`L1` and rounding estimates are already available once the
paper-specific uniform local estimates are supplied.

## 7. Assembly that is already available

After the physical inputs above are proved, the following are available:

- Actual quantum trace-norm contraction, fidelity continuity, and data processing.
- The quantum-to-quantum transfer estimates in `InfiniteLANTransfer` and
  `MatrixLANTransfer`.
- Orbital and hybrid Gaussian optimal limits over all actual competitors,
  including physical attainment and nonnegative thermal parameters below one.
- Classical randomized rounding, fallback transport, normalized Young laws, and
  block-fidelity/deletion estimates.
- `LAN.two_scale_limsup_le`, `LAN.minimax_converges_of_candidates`, and the
  dense-interior extension for the final limit bookkeeping.

`Main.known_spectrum_optimum_of_bounds` still assumes candidate convergence and the
finite-sample converse estimate. `Main.unknown_spectrum_optimum_of_bounds` still
assumes uniform candidate fidelity convergence and the converse estimate. These
premises contain the remaining physical conclusions and are not discharged merely
by applying the assembly theorem.

## 8. Additional PCT use of mixed-state LAN

The new full-environment physical Gaussian product-mixture limit supplies an output
approximation to which LAN could be applied. Remaining LAN-related work includes
exact local coordinates for reduced perturbed states, the diagonal/orbital Gaussian
covariance and independence calculation, and both mixed-channel data-processing
inequalities. The global downstream CPTP extension and rank-adapted purification
also remain separate protocol obligations.

For integrating the PCT approximations, the manuscript needs convergence for each
fixed Gaussian perturbation and an integrable bound (trace-distance bounds by two
for states suffice). Uniform LAN over unbounded perturbations is unnecessary.
The actual PCT fidelity limit must then be squeezed using the forward and reverse
approximations. The proved scalar comparison with `pctValue` cannot substitute for
this physical fidelity identification.
