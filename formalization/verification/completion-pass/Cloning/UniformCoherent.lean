import Cloning.CoherentContinuity
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Sequences

/-! Compact-uniform coherent-product limits from moving-parameter probability limits.
No equicontinuity premise is assumed. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.ComplexCoherent
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem moving_exponential (L : ℕ → ℕ) (hL : Tendsto L atTop atTop)
    (t : ℕ → ℝ) {a : ℝ} (ht : Tendsto t atTop (𝓝 a)) (ht0 : ∀ n, 0 ≤ t n) :
    Tendsto (fun n => (1 + t n / L n) ^ L n) atTop (𝓝 (Real.exp a)) := by
  let ratio : ℝ → ℝ := Function.update (fun x => Real.log (1 + x) / x) 0 1
  have hd : HasDerivAt (fun x : ℝ => Real.log (1 + x)) 1 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_add 1).log (by norm_num) using 1
    norm_num
  have hc : ContinuousAt ratio 0 := by
    simpa only [ratio, add_zero, Real.log_one, sub_zero] using hd.continuousAt_div
  have hz : Tendsto (fun n => t n / L n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, one_div, one_mul, mul_zero] using
      ht.mul (tendsto_one_div_atTop_nhds_zero_nat.comp hL)
  have hr : Tendsto (fun n => t n * ratio (t n / L n)) atTop (𝓝 a) := by
    simpa only [Function.comp_def, ratio, Function.update_self, mul_one] using ht.mul (hc.tendsto.comp hz)
  have heq : (fun n => t n * ratio (t n / L n)) =ᶠ[atTop]
      (fun n => (L n : ℝ) * Real.log (1 + t n / L n)) := by
    filter_upwards [hL.eventually (eventually_ge_atTop 1)] with n hn
    have hn0 : (L n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    by_cases htn : t n = 0
    · simp [htn, ratio]
    · dsimp only [ratio]
      rw [Function.update_of_ne (div_ne_zero htn hn0)]
      field_simp
  have he := (Real.continuous_exp.tendsto a).comp (hr.congr' heq)
  convert he using 1
  funext n
  simp only [Function.comp_def]
  rw [Real.exp_nat_mul, Real.exp_log (by have := ht0 n; positivity : 0 < 1 + t n / L n)]

private theorem moving_binomialWeight (L : ℕ → ℕ) (hL : Tendsto L atTop atTop)
    (t : ℕ → ℝ) {a : ℝ} (ht : Tendsto t atTop (𝓝 a)) (ht0 : ∀ n, 0 ≤ t n)
    (j : ℕ) : Tendsto (fun n => PoissonApproximation.binomialWeight (t n) (L n) j)
      atTop (𝓝 (PoissonApproximation.poissonWeight a j)) := by
  have hn := (PoissonApproximation.tendsto_binomial_numerator 1 j).comp hL
  simp only [one_pow] at hn
  have hnum := hn.mul (ht.pow j)
  have hden := moving_exponential L hL t ht ht0
  have h := hnum.div hden (Real.exp_ne_zero a)
  convert h using 1
  · funext n
    simp only [PoissonApproximation.binomialWeight, Function.comp_def, Pi.div_apply]
    ring_nf
  · unfold PoissonApproximation.poissonWeight
    rw [Real.exp_neg]
    ring_nf

/-- Binomial number-amplitude vectors converge also when the amplitude changes
with the sample size, provided it converges to a finite limit. -/
theorem radial_productVector_moving_tendsto (L : ℕ → ℕ) (hL : Tendsto L atTop atTop)
    (t : ℕ → ℝ) {a : ℝ} (ht : Tendsto t atTop (𝓝 a)) (ht0 : ∀ n, 0 ≤ t n)
    (ha : 0 ≤ a) :
    Tendsto (fun n => CoherentCoefficients.productVector (t n) (ht0 n) (L n)) atTop
      (𝓝 (CoherentCoefficients.coherentVector a ha)) := by
  exact CoherentCoefficients.amplitudeVector_tendsto _ _
    (fun n => PoissonApproximation.binomialWeight_nonneg (ht0 n) (L n))
    (PoissonApproximation.poissonWeight_nonneg ha)
    (fun n => PoissonApproximation.binomialWeight_hasSum (ht0 n) (L n))
    (PoissonApproximation.poissonWeight_hasSum ha)
    (moving_binomialWeight L hL t ht ht0)

/-- Continuity of the normalized nonnegative Poisson square-root amplitudes. -/
theorem radial_coherentVector_moving_tendsto
    (t : ℕ → ℝ) {a : ℝ} (ht : Tendsto t atTop (𝓝 a)) (ht0 : ∀ n, 0 ≤ t n)
    (ha : 0 ≤ a) :
    Tendsto (fun n => CoherentCoefficients.coherentVector (t n) (ht0 n)) atTop
      (𝓝 (CoherentCoefficients.coherentVector a ha)) := by
  apply CoherentCoefficients.amplitudeVector_tendsto _ _
    (fun n => PoissonApproximation.poissonWeight_nonneg (ht0 n))
    (PoissonApproximation.poissonWeight_nonneg ha)
    (fun n => PoissonApproximation.poissonWeight_hasSum (ht0 n))
    (PoissonApproximation.poissonWeight_hasSum ha)
  intro j
  exact ((Real.continuous_exp.tendsto _).comp ht.neg |>.mul (ht.pow j)).div_const _

/-- The phase isometry removes all phase dependence from the approximation
error, even at zero amplitude. -/
theorem productVector_coherentVector_norm_eq_radial (z : ℂ) (L : ℕ) :
    ‖productVector z L - coherentVector z‖ =
      ‖CoherentCoefficients.productVector (‖z‖ ^ 2) (sq_nonneg _) L -
        CoherentCoefficients.coherentVector (‖z‖ ^ 2) (sq_nonneg _)‖ := by
  rw [productVector, coherentVector, ← map_sub, LinearIsometry.norm_map]

/-- Uniform radial approximation on every bounded interval. This is derived
from the moving-parameter limit and sequential compactness, rather than an
assumed uniform approximation theorem. -/
theorem radial_productVector_uniform (R : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L in atTop, ∀ (t : ℝ) (ht : 0 ≤ t), t ≤ R →
      ‖CoherentCoefficients.productVector t ht L -
        CoherentCoefficients.coherentVector t ht‖ < ε := by
  classical
  by_contra h
  rw [eventually_atTop] at h
  push_neg at h
  choose L hL t ht0 htR hbad using h
  have hLtop : Tendsto L atTop atTop := tendsto_atTop_mono hL tendsto_id
  obtain ⟨a, ha, φ, hφ, ht⟩ := isCompact_Icc.tendsto_subseq
    (fun n => (show t n ∈ Set.Icc 0 R from ⟨ht0 n, htR n⟩))
  have hp := radial_productVector_moving_tendsto (L ∘ φ)
    (hLtop.comp hφ.tendsto_atTop) (t ∘ φ) ht (fun n => ht0 (φ n)) ha.1
  have hc := radial_coherentVector_moving_tendsto (t ∘ φ) ht (fun n => ht0 (φ n)) ha.1
  have hz : Tendsto (fun n => ‖CoherentCoefficients.productVector (t (φ n))
      (ht0 (φ n)) (L (φ n)) -
        CoherentCoefficients.coherentVector (t (φ n)) (ht0 (φ n))‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, norm_zero] using (hp.sub hc).norm
  obtain ⟨n, hn⟩ := (hz.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge (hbad (φ n))) hn

/-- Uniform convergence for every bounded complex amplitude window. -/
theorem productVector_coherentVector_uniform_on_closedBall
    (R : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L in atTop, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖productVector z L - coherentVector z‖ < ε := by
  filter_upwards [radial_productVector_uniform (R ^ 2) ε hε] with L hL z hz
  rw [productVector_coherentVector_norm_eq_radial]
  exact hL (‖z‖ ^ 2) (sq_nonneg _) (sq_le_sq₀ (norm_nonneg z) (le_trans (norm_nonneg z) hz) |>.mpr hz)

/-- The actual complex binomial vectors converge uniformly on every bounded
set of coherent amplitudes in Hilbert norm. -/
theorem productVector_tendstoUniformlyOn {K : Set ℂ} (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun L z => productVector z L) coherentVector atTop K := by
  obtain ⟨R, hR⟩ := hK.exists_norm_le
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [productVector_coherentVector_uniform_on_closedBall R ε hε] with L hL z hz
  simpa only [dist_eq_norm, norm_sub_rev] using hL z (hR z hz)

/-- Compact-amplitude uniform convergence, in the standard uniform-convergence
API and including the zero amplitude. -/
theorem productVector_tendstoUniformlyOn_compact {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun L z => productVector z L) coherentVector atTop K :=
  productVector_tendstoUniformlyOn hK.isBounded

/-- The pure-state trace-norm error is bounded by twice the Hilbert error. -/
theorem product_projector_distance_le (z : ℂ) (L : ℕ) :
    ‖InfiniteTraceClass.vectorProjector (productVector z L) -
      InfiniteTraceClass.vectorProjector (coherentVector z)‖ ≤
        2 * ‖productVector z L - coherentVector z‖ := by
  simpa only [productVector_norm, coherentVector_norm, show (1 : ℝ) + 1 = 2 by norm_num] using
    InfiniteTraceClass.norm_vectorProjector_sub_le (productVector z L) (coherentVector z)

/-- Uniform convergence holds for the actual trace-class pure states. -/
theorem product_projector_tendstoUniformlyOn {K : Set ℂ} (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun L z => InfiniteTraceClass.vectorProjector (productVector z L))
      (fun z => InfiniteTraceClass.vectorProjector (coherentVector z)) atTop K := by
  obtain ⟨R, hR⟩ := hK.exists_norm_le
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [productVector_coherentVector_uniform_on_closedBall R (ε / 2) (by positivity)]
    with L hL z hz
  rw [dist_comm, dist_eq_norm]
  exact lt_of_le_of_lt (product_projector_distance_le z L) (by linarith [hL z (hR z hz)])

/-- Uniform error bound for the concrete CPTP occupation channel. The output
spaces vary with the sample size, so the statement uses their genuine trace
norms directly. -/
theorem occupationChannel_coherent_product_distance_le (z : ℂ) (L : ℕ) :
    ‖(SymmetricOccupation.occupationChannel L).toLinearMap
      (InfiniteTraceClass.vectorProjector (coherentVector z)) -
        InfiniteTraceClass.vectorProjector (productTensor z L)‖ ≤
      2 * ‖productVector z L - coherentVector z‖ := by
  have h := SymmetricOccupation.occupationChannel_pure_distance_le L
    (coherentVector z) (productVector z L)
    (SymmetricOccupation.restrict_norm_eq_of_support L (productVector z L)
      (fun j hj => productVector_eq_zero_of_lt z L j hj))
  simpa only [coherentVector_norm, productVector_norm, show (1 : ℝ) + 1 = 2 by norm_num,
    SymmetricOccupation.compression_apply, restrict_productVector, productTensor, norm_sub_rev]
    using h

/-- The actual occupation channel approximates the normalized tensor product
states uniformly on every fixed complex amplitude ball. -/
theorem occupationChannel_coherent_product_uniform_on_closedBall
    (R : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L in atTop, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖(SymmetricOccupation.occupationChannel L).toLinearMap
        (InfiniteTraceClass.vectorProjector (coherentVector z)) -
          InfiniteTraceClass.vectorProjector (productTensor z L)‖ < ε := by
  filter_upwards [productVector_coherentVector_uniform_on_closedBall R (ε / 2) (by positivity)]
    with L hL z hz
  exact lt_of_le_of_lt (occupationChannel_coherent_product_distance_le z L)
    (by linarith [hL z hz])

/-- The corresponding compact-window quantum approximation statement. -/
theorem occupationChannel_coherent_product_uniform_on_compact
    {K : Set ℂ} (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L in atTop, ∀ z ∈ K,
      ‖(SymmetricOccupation.occupationChannel L).toLinearMap
        (InfiniteTraceClass.vectorProjector (coherentVector z)) -
          InfiniteTraceClass.vectorProjector (productTensor z L)‖ < ε := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  filter_upwards [occupationChannel_coherent_product_uniform_on_closedBall R ε hε] with L hL z hz
  exact hL z (hR z hz)

end Cloning.ComplexCoherent
