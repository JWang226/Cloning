import Cloning.PCTLocalChartCoordinates

/-! Exact LAN-chart parameters at sample scale `1 / sqrt L`. This provides the
physical local-chart input needed by LAN, without asserting existence of the
LAN channels or their error estimates. -/
noncomputable section
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator InnerProductSpace Topology BigOperators
open Matrix NormedSpace Filter
namespace Cloning.PCTLocalChart
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A : Type*} [Fintype A] [LinearOrder A]

def sampleScale (L : ℕ) : ℝ := (Real.sqrt (L : ℝ))⁻¹

lemma sampleScale_ne_zero {L : ℕ} (hL : 0 < L) : sampleScale L ≠ 0 := by
  exact inv_ne_zero (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hL)).ne'

lemma sampleScale_tendsto : Tendsto sampleScale atTop (𝓝 (0 : ℝ)) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

lemma sampleScale_tendsto_punctured : Tendsto sampleScale atTop (𝓝[≠] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨sampleScale_tendsto, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with L hL
  exact sampleScale_ne_zero hL

/-- The scaled Hermitian tangent at the actual sample size. -/
def sampleTangent (p : A → ℝ) (hp : Function.Injective p) (Z : Matrix A A ℂ) (L : ℕ) :
    Hermitian A := (sampleScale L)⁻¹ • tangentCoordinates p hp Z (sampleScale L)

theorem sampleTangent_tendsto (p : A → ℝ) (hp : Function.Injective p) (Z : Matrix A A ℂ) :
    Tendsto (sampleTangent p hp Z) atTop (𝓝 (tangentDifferential p Z)) :=
  (scaledTangentCoordinates_tendsto p hp Z).comp sampleScale_tendsto_punctured

theorem sampleSpectralCoordinates_tendsto (p : A → ℝ) (hp : Function.Injective p)
    (Z : Matrix A A ℂ) :
    Tendsto (fun L => spectralCoordinates (sampleTangent p hp Z L)) atTop
      (𝓝 (classicalCoordinate p Z)) :=
  (scaledSpectralCoordinates_tendsto p hp Z).comp sampleScale_tendsto_punctured

theorem sampleOrbitalCoordinates_tendsto (p : A → ℝ) (hp : Function.Injective p)
    (Z : Matrix A A ℂ) :
    Tendsto (fun L => orbitalCoordinates p (sampleTangent p hp Z L)) atTop
      (𝓝 (fun ij : OrbitalPair A => orbitalCoordinate p Z ij.1.1 ij.1.2)) :=
  (scaledOrbitalCoordinates_tendsto p hp Z).comp sampleScale_tendsto_punctured

lemma chart_scale_in_coordinates (p : A → ℝ)
    (hgap : ∀ i j, i < j → 0 < p i - p j) (t : ℝ) (H : Hermitian A) :
    (chart p (t • H) : Matrix A A ℂ) + base p =
      NormedSpace.exp (t • orbitalGenerator p (orbitalCoordinates p H)) *
        Matrix.diagonal (fun i => ((p i + t * spectralCoordinates H i : ℝ) : ℂ)) *
          NormedSpace.exp (-(t • orbitalGenerator p (orbitalCoordinates p H))) := by
  rw [chart_coe, rawChart, sub_add_cancel]
  have hsmul : ((t • H : Hermitian A) : Matrix A A ℂ) = t • (H : Matrix A A ℂ) := rfl
  rw [hsmul, map_smul, generator_eq_orbitalGenerator p hgap H]
  congr 2
  rw [map_smul, diagonalPart_eq_spectralCoordinates]
  ext a b
  by_cases hab : a = b <;> simp [base, Matrix.diagonal_apply, hab, Complex.real_smul]

/-- For each fixed physical tangent, all sufficiently large sample sizes have
exact manuscript chart coordinates, with the proved convergent parameters. -/
theorem eventually_sample_exact_chart (p : A → ℝ) (hp : Function.Injective p)
    (hp0 : ∀ a, 0 ≤ p a) (hgap : ∀ i j, i < j → 0 < p i - p j)
    (Z : Matrix A A ℂ) :
    ∀ᶠ L : ℕ in atTop,
      NormedSpace.exp (sampleScale L • orbitalGenerator p
        (orbitalCoordinates p (sampleTangent p hp Z L))) *
        Matrix.diagonal (fun i => ((p i + sampleScale L *
          spectralCoordinates (sampleTangent p hp Z L) i : ℝ) : ℂ)) *
        NormedSpace.exp (-(sampleScale L • orbitalGenerator p
          (orbitalCoordinates p (sampleTangent p hp Z L)))) =
        reducedDensityMatrix (normalizedTangentVector p Z (‖coefficientVector Z‖ ^ 2)
          (sampleScale L)) := by
  have hc : Tendsto (tangentCurve p Z) (𝓝 0) (𝓝 0) := by
    simpa only [tangentCurve_zero] using (tangentCurve_hasDerivAt_zero p Z).continuousAt.tendsto
  have he := (hc.comp sampleScale_tendsto).eventually (eventually_chart_localInverse p hp)
  filter_upwards [he, eventually_gt_atTop 0] with L hL hpos
  have hr : sampleScale L • sampleTangent p hp Z L =
      tangentCoordinates p hp Z (sampleScale L) := by
    rw [sampleTangent, smul_smul, mul_inv_cancel₀ (sampleScale_ne_zero hpos), one_smul]
  have hchart := chart_scale_in_coordinates p hgap (sampleScale L) (sampleTangent p hp Z L)
  rw [hr] at hchart
  rw [← hchart]
  change ((chart p (localInverse p hp (tangentCurve p Z (sampleScale L)))) : Matrix A A ℂ) + _ = _
  dsimp only [Function.comp_def] at hL
  rw [hL, tangentCurve_coe p hp0, sub_add_cancel]

/-- The trace of a reduced pure state is its vector norm squared. -/
lemma trace_reduced_eq_norm_sq (ψ : Register (A × A)) :
    Matrix.trace (reducedDensityMatrix ψ) = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  calc
    _ = ⟪ψ,ψ⟫_ℂ := by
      simp only [reducedDensityMatrix, Matrix.trace, Matrix.diag, lp.inner_eq_tsum,
        tsum_fintype, Fintype.sum_prod_type, RCLike.inner_apply, Complex.star_def]
    _ = _ := by rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl

/-- Normalized, orthogonal purification tangents remain on the trace-one
physical state hyperplane at every scale. -/
lemma tangentCurve_trace_zero (p : A → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1)
    (Z : Matrix A A ℂ)
    (horth : ⟪coefficientVector (schmidtCoefficients p), coefficientVector Z⟫_ℂ = 0) (t : ℝ) :
    Matrix.trace (tangentCurve p Z t : Matrix A A ℂ) = 0 := by
  rw [tangentCurve_coe p hp0, Matrix.trace_sub, trace_reduced_eq_norm_sq,
    normalizedTangentVector_norm p hp0 hs Z horth t]
  simp only [one_pow, Complex.ofReal_one, base, Matrix.trace_diagonal]
  rw [← Complex.ofReal_sum, hs, Complex.ofReal_one, sub_self]

/-- The exact spectral coordinates lie in the required trace-zero parameter
hyperplane for all sufficiently large sample sizes. -/
theorem eventually_sample_spectral_sum_zero (p : A → ℝ) (hp : Function.Injective p)
    (hp0 : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (Z : Matrix A A ℂ)
    (horth : ⟪coefficientVector (schmidtCoefficients p), coefficientVector Z⟫_ℂ = 0) :
    ∀ᶠ L : ℕ in atTop, ∑ i, spectralCoordinates (sampleTangent p hp Z L) i = 0 := by
  have hc : Tendsto (tangentCurve p Z) (𝓝 0) (𝓝 0) := by
    simpa only [tangentCurve_zero] using (tangentCurve_hasDerivAt_zero p Z).continuousAt.tendsto
  filter_upwards [(hc.comp sampleScale_tendsto).eventually (eventually_chart_localInverse p hp)] with L hL
  have he := congrArg (fun H : Hermitian A => Matrix.trace (H : Matrix A A ℂ)) hL
  dsimp only [Function.comp_def] at he
  rw [chart_trace, tangentCurve_trace_zero p hp0 hs Z horth] at he
  have he' := congrArg Complex.re he
  have hsmul (r : ℝ) (H : Hermitian A) :
      ((r • H : Hermitian A) : Matrix A A ℂ) = r • (H : Matrix A A ℂ) := rfl
  simp only [spectralCoordinates, sampleTangent, hsmul, Matrix.smul_apply,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← Finset.mul_sum]
  have hz : (∑ i, ((tangentCoordinates p hp Z (sampleScale L)).val i i).re) = 0 := by
    simpa only [Matrix.trace, Matrix.diag, Complex.re_sum, Complex.zero_re] using he'
  rw [hz, mul_zero]

end Cloning.PCTLocalChart
