# Tenth-pass next obligation: PCT tangent Gaussian covariance

**Status: mathematical derivation and implementation plan; not a Lean theorem.**
This note records a read-only analysis after the tenth-pass checkpoint. It does
not extend the audited Lean proof, assert constructed mixed-state LAN channels,
or identify the finite-sample PCT fidelity with `Cloning.pctValue`.

The relevant existing sources are `Cloning/PCTReducedGaussian.lean`,
`Cloning/PCTPurificationFrame.lean`, `Cloning/PCTPurificationChannelPhysical.lean`,
and `reference/cloning.tex`, especially the simple full-rank PCT subsection.
The frozen physical endpoint proves trace-norm approximation by an actual
mixture of reduced tensor powers. Its downstream `physicalCloneTraceCLM` is a
continuous linear map; a global CPTP composition adapter remains a separate
obligation. The environment in that endpoint has dimension `d`, so the
purification space has dimension `d²`, even for a rank-deficient input state.

## 1. Exact normalization and reduced-state expansion

Assume `p_i ≥ 0` and `∑ᵢ p_i = 1`, and write

\[
P=\operatorname{diag}(p),\qquad S=\operatorname{diag}(\sqrt p),\qquad
\psi=\operatorname{vec}(S).
\]

Let `Z` be a coefficient matrix with complex Hilbert–Schmidt orthogonality
`⟨S,Z⟩ = 0`, and set

\[
e=\|Z\|_{\mathrm{HS}}^2=\sum_{i,j}|Z_{ij}|^2.
\]

For real `t`, orthogonality and normalization give

\[
\|\psi+t\operatorname{vec}(Z)\|^2=1+t^2e.
\]

Thus the normalized purification has reduced density

\[
\sigma_t(Z)
=\frac{(S+tZ)(S+tZ)^*}{1+t^2e}
=\frac{P+tD_p(Z)+t^2ZZ^*}{1+t^2e},\qquad
D_p(Z)=ZS+SZ^*.
\]

This matrix is positive and has trace one. Its exact remainder is

\[
\sigma_t(Z)-P-tD_p(Z)
=\frac{t^2}{1+t^2e}\bigl(ZZ^*-eP-teD_p(Z)\bigr).
\]

For fixed `Z`, this is `O_Z(t²)` in every finite-dimensional matrix norm. For
example, for `|t| ≤ 1`, the trace norm is at most
`t² (2e + e ‖D_p(Z)‖₁)`, because `‖ZZ*‖₁=e`, `‖P‖₁=1`, and the denominator is
at least one. At `t=L⁻¹ᐟ²` this is `O_Z(L⁻¹)`.

**Existing-lemma distinction.** `normalizedTangent_reduced_exact` permits an
arbitrary `e ≥ 0`: it proves the displayed algebraic expression but does not
prove normalization. The conditions `∑p=1`, tangent orthogonality, and
`e=‖Z‖²` must be supplied for that conclusion. For the actual mixture vectors,
`frameParticle_norm` already proves normalization. The additional bridge is
the coefficient-matrix identification and
`‖frameTangent u z‖² = GeneralCoherent.energy z`.

## 2. Gaussian law on the purification tangent space

Put `v=γ−1>0`. The convention is a circular complex Gaussian coordinate of
density

\[
(\pi v)^{-1}e^{-|z|^2/v},\qquad
\mathbb E|z|^2=v,\quad
\operatorname{Var}(\Re z)=\operatorname{Var}(\Im z)=v/2.
\]

Take independent coordinates of this law in any orthonormal complex frame of
`ψ⊥`. Equivalently, project an iid Gaussian coefficient matrix orthogonally
away from `ψ`. Completeness of the frame gives

\[
\begin{aligned}
\mathbb E Z_{ab}&=0,\\
\mathbb E[Z_{ab}\overline{Z_{cd}}]
&=v\left(\delta_{ac}\delta_{bd}
-\delta_{ab}\delta_{cd}\sqrt{p_a p_c}\right),\\
\mathbb E[Z_{ab}Z_{cd}]&=0.
\end{aligned}
\]

In particular, the diagonal complex vector has covariance
`v(I−√p√pᵀ)`; its real part has covariance **half** that matrix. All
off-diagonal coefficients remain independent circular Gaussians of variance
`v`, independently of the diagonal block.

These conclusions can be established directly from the frame expansion,
without first constructing a basis-independent Gaussian measure on a
subspace. Second moments alone do not establish independence: the joint real
Gaussian law, or the characteristic identity below, must also be proved.

## 3. Classical and quantum coordinates, with exact factors

For the simple full-rank case assume `p₁>⋯>p_d>0`. Define

\[
\Sigma_p=\operatorname{diag}(p)-pp^{\mathsf T},\qquad
\mathsf H=\{h\in\mathbb R^d:\sum_i h_i=0\}.
\]

The classical coordinates of the differential are

\[
h_i(Z)=D_p(Z)_{ii}=2\sqrt{p_i}\Re Z_{ii}.
\]

Tangent orthogonality gives `∑h_i=0` exactly. Multiplying the real diagonal
covariance by `2 diag(√p)` on both sides yields

\[
\operatorname{Cov}(h)
=4\operatorname{diag}(\sqrt p)\frac v2
 (I-\sqrt p\sqrt p^{\mathsf T})\operatorname{diag}(\sqrt p)
=2v\Sigma_p.
\]

For `i<j`, put `Δ_ij=p_i−p_j>0`. The orbital coordinate in the manuscript's
Weyl convention is

\[
\beta_{ij}(Z)
=\frac{D_p(Z)_{ji}}{\sqrt{\Delta_{ij}}}
=\frac{\sqrt{p_i}Z_{ji}+\sqrt{p_j}\overline{Z_{ij}}}
       {\sqrt{\Delta_{ij}}}.
\]

Its real part uses a plus sign and its imaginary part a minus sign:

\[
\begin{aligned}
\Re\beta_{ij}&=
\frac{\sqrt{p_i}\Re Z_{ji}+\sqrt{p_j}\Re Z_{ij}}{\sqrt\Delta},\\
\Im\beta_{ij}&=
\frac{\sqrt{p_i}\Im Z_{ji}-\sqrt{p_j}\Im Z_{ij}}{\sqrt\Delta}.
\end{aligned}
\]

Both variances equal `v(p_i+p_j)/(2Δ_ij)`, and their covariance vanishes.
Therefore

\[
\mathbb E|\beta_{ij}|^2=\frac{v(p_i+p_j)}{\Delta_{ij}},\qquad
\mathbb E\beta_{ij}^2=0.
\]

Different unordered pairs are independent, and independent of `h`, because
these are disjoint blocks of the joint real Gaussian vector.

A useful single formal target, proving the full distribution and these
independences together, is: for real `t_i` and complex `ξ_ij`,

\[
\mathbb E\exp\left(i\sum_i t_i h_i+
 \sum_{i<j}(\xi_{ij}\overline{\beta_{ij}}-
                 \overline{\xi_{ij}}\beta_{ij})\right)
=\exp\left(-v\,t^{\mathsf T}\Sigma_p t
-\sum_{i<j}\frac{v(p_i+p_j)}{\Delta_{ij}}|\xi_{ij}|^2\right).
\]

This follows by the existing complex Gaussian linear integral in each
independent frame coordinate. The squared norm of the projected classical
test vector is
`∑p_i t_i²−(∑p_i t_i)²`. Each pair's test vector has squared norm
`(p_i+p_j)|ξ_ij|²/Δ_ij`, and is orthogonal to the diagonal test vector and to
other pairs.

## 4. Averaging the Gaussian comparison state

This section is a statement about an explicitly specified Gaussian model;
it does not assert that finite tensor experiments have already been mapped
to that model.

Let `q_ij=p_j/p_i`. The thermal Weyl characteristic uses

\[
\alpha(q)=\frac{1+q}{2(1-q)},\qquad
\chi_{\tau_q}(\xi)=e^{-\alpha(q)|\xi|^2}.
\]

Conjugating by the actual displacement `D(β)` contributes
`exp(ξ conjugate(β)−conjugate(ξ)β)`. If `β` is circular with
`E|β|²=b`, the averaged multiplier is exactly `exp(−b|ξ|²)`. Hence the
thermal width increases from `α(q)` to `α(q)+b`. This is an equality of
actual trace-class operators once Bochner integrability and characteristic
injectivity are invoked.

For the tangent displacement,

\[
\alpha(q_{ij})=\frac{p_i+p_j}{2\Delta_{ij}},\qquad
b_{ij}=2v\alpha(q_{ij}),\qquad
\alpha_{\rm out}=(2\gamma-1)\alpha(q_{ij}).
\]

Solving this width equation gives

\[
q_{ij}^{\rm out}
=\frac{\gamma-1+\gamma q_{ij}}{\gamma+(\gamma-1)q_{ij}}
=\operatorname{Thermal.pct}(\gamma,q_{ij}).
\]

Equivalently, the output mean photon number is

\[
\frac{p_j}{\Delta_{ij}}+
\frac{(\gamma-1)(p_i+p_j)}{\Delta_{ij}}
=\frac{(\gamma-1)p_i+\gamma p_j}{\Delta_{ij}}.
\]

Classically, convolving the base Gaussian covariance `Σ_p` with the tangent
shift covariance `2vΣ_p` gives `(2γ−1)Σ_p`. Independence thus yields the
candidate comparison output

\[
\overline\Theta_p=
\mathsf N_{0,(2\gamma-1)\Sigma_p}
\otimes\bigotimes_{i<j}\tau_{\operatorname{Thermal.pct}(\gamma,q_{ij})}.
\]

Its root fidelity with the centered target is obtained by whitening the
common classical covariance on `H`, then applying Gaussian affinity and
thermal fidelity product formulas:

\[
F(\overline\Theta_p,\Theta_p)
=\left(\frac{\sqrt{2\gamma-1}}\gamma\right)^{(d-1)/2}
\prod_{i<j}F\left(\tau_{q_{ij}},
                  \tau_{\operatorname{Thermal.pct}(\gamma,q_{ij})}\right).
\]

This evaluates the Gaussian comparison states and matches the definition of
`Cloning.pctValue`; it does not identify that definition with a finite-sample
channel limit. Existing reusable tools include Gaussian affinity,
`PositiveField.rootFidelity_product`, actual thermal fidelity, Gaussian phase
integration, and Weyl characteristic injectivity.

## 5. Exact remaining formal obligations

The following are proposed lemma tasks, not names of completed theorems.

1. **Normalized tangent bridge:** frame tangent norm/energy, coefficient
   identification, positivity and trace one under the stated normalization
   hypotheses, and the exact remainder bound from Section 1.
2. **Tangent Gaussian pushforward:** frame completeness and circular Gaussian
   linear characteristic imply the joint characteristic in Section 3. Derive
   the product law for `h` and the `β_ij`, with the real-versus-complex variance
   convention explicit.
3. **Actual comparison-state integral:** prove Gaussian displacement averaging
   of a thermal operator, classical Gaussian convolution, and their joint
   hybrid Bochner integral. Integrability follows from normalized positive
   state norm one and a probability measure. Characteristic injectivity can
   identify the quantum factors; no idler reconstruction is needed.
4. **Comparison-state fidelity:** transport/whiten the Gaussian on the
   trace-zero hyperplane, then use existing classical and thermal product
   fidelity formulas. These first four tasks are finite algebra and Gaussian
   analysis; they do not require mixed-state LAN.
5. **Local chart analysis:** prove the derivative of
   `exp(Y_p(z)) diag(p+h) exp(−Y_p(z))` is
   `diag(h)+[Y_p(z),P]`, with inverse coordinates from Section 3. For simple
   full-rank `p`, the inverse-function theorem gives exact coordinates for
   `σ_{1/√L}(Z)` converging to `(h(Z),β(Z))`. Alternatively a sufficiently sharp
   full-rank fidelity perturbation estimate can replace the exact-chart step.
   The one-particle `O(1/L)` remainder is **not** enough under the naive tensor
   telescoping bound, which only gives `O(1)`.
6. **Genuine mixed-state LAN:** construct forward and reverse CPTP maps between
   finite tensor registers and the actual hybrid operator-valued `L1` model,
   and prove bounded-parameter trace-norm approximation estimates. Supply the
   cross-model channel/data-processing interface. Existing abstract LAN
   transfer lemmas and Hilbert trace-class transfer lemmas do not construct
   these hybrid channels or estimates.
7. **Integrated two-sided transfer:** for each fixed `Z`, use exact local
   coordinates plus Gaussian-shift continuity to obtain forward/reverse LAN
   convergence. Integrate scalar error norms by dominated convergence, using
   the bound `2`; no uniform estimate over unbounded `Z` is required. Combine
   this with the frozen PCT product-mixture approximation and the target LAN
   approximation. Forward data processing gives the fidelity upper bound;
   reverse data processing plus continuity gives the lower bound.
8. **Operational PCT scope:** separately finish the global finite Kraus /
   symmetric-sector / Werner / register / partial-trace composition adapter.
   A normalized-state sequence can have its fidelity analyzed before this
   adapter is finished, but it cannot yet be advertised as a constructed
   globally admissible PCT channel.

No audited Lean source was edited and no Lean build was run to create this
note. All new covariance and comparison-state identifications above remain
mathematical derivations pending formalization.
