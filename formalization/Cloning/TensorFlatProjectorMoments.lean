import Cloning.TensorFlatProjectorLaw

/-! Actual physical flat Young laws have the required forward and reciprocal
crossing-dimension moments, derived from physical concentration. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.TensorLie
open Cloning.YoungGeneral Cloning.YoungDimensionRatio
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Forward relative error under the literal physical flat-spectrum law. -/
theorem tensorFlatYoungPMF_mean_dimension_error (r k : ℕ) (hr : 0 < r) :
    Tendsto (fun N => ∑ mu, (tensorFlatYoungPMF N r hr mu).toReal *
      |normalizedDimension r k N mu - 1|) atTop (𝓝 0) := by
  have htail := tensorYoungPMF_tail_tendsto_zero (fun _ => flatSpectrum r)
    (fun _ _ => by unfold flatSpectrum; positivity) (fun _ => flatSpectrum_sum r hr)
    (fun _ => antitone_const)
  have hbound := (dimensionErrorEnvelope_tendsto_zero r k).add
    (htail.const_mul (dimensionUniformBound r k))
  simp only [mul_zero, add_zero] at hbound
  apply squeeze_zero' (Eventually.of_forall (fun N =>
    Finset.sum_nonneg (fun mu _ => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)))) ?_ hbound
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  exact mean_error_le (tensorFlatYoungPMF N r hr) (flatSpectrum r) (shrinkingRadius N)
    (dimensionErrorEnvelope r k N) (dimensionUniformBound r k)
    (dimensionErrorEnvelope_nonneg r k N) (normalizedDimension r k N)
    (normalizedDimension_global_error r k N hr hN) (normalizedDimension_typical_error r k N hr hN)

/-- Reciprocal relative error, including all atypical physical labels. -/
theorem tensorFlatYoungPMF_mean_inverse_dimension_error (r k : ℕ) (hr : 0 < r) :
    Tendsto (fun N => ∑ mu, (tensorFlatYoungPMF N r hr mu).toReal *
      |inverseNormalizedDimension r k N mu - 1|) atTop (𝓝 0) := by
  let c := leadingConstant r k
  let a := r * k
  let s := Fintype.card (PositiveRoot r)
  let C := ((r : ℝ) + 1) ^ s
  have hc : 0 ≤ c := (leadingConstant_pos r k hr).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have htail := (polynomial_concentrationEnvelope_tendsto_zero r (a+s)).const_mul ((c+1)*C)
  have hbound := ((dimensionErrorEnvelope_tendsto_zero r k).const_mul 2).add htail
  simp only [mul_zero, add_zero] at hbound
  apply squeeze_zero' (Eventually.of_forall (fun N =>
    Finset.sum_nonneg (fun mu _ => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)))) ?_ hbound
  have hsmall : ∀ᶠ N in atTop, dimensionErrorEnvelope r k N ≤ 1 / 2 :=
    (dimensionErrorEnvelope_tendsto_zero r k).eventually (eventually_le_nhds (by norm_num))
  filter_upwards [Filter.eventually_ge_atTop 1, hsmall] with N hN heN
  have hmean := mean_error_le (tensorFlatYoungPMF N r hr) (flatSpectrum r) (shrinkingRadius N)
    (2 * dimensionErrorEnvelope r k N) (c * (N : ℝ) ^ a + 1)
    (mul_nonneg (by norm_num) (dimensionErrorEnvelope_nonneg r k N))
    (inverseNormalizedDimension r k N)
    (inverseNormalizedDimension_global_error r k N hr)
    (inverseNormalizedDimension_typical_error r k N hr hN heN)
  have ht := tensorYoungPMF_tail_shrinking_le N hN (flatSpectrum r)
    (fun _ => by unfold flatSpectrum; positivity) (flatSpectrum_sum r hr) antitone_const
  have hpw : (N : ℝ) ^ a ≤ ((N : ℝ) + 1) ^ a := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hpw1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ a := one_le_pow₀ (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
  have hcoeff : c * (N : ℝ) ^ a + 1 ≤ (c+1) * ((N : ℝ)+1)^a := by
    nlinarith [mul_le_mul_of_nonneg_left hpw hc]
  have ht0 : 0 ≤ tailProbability (tensorFlatYoungPMF N r hr) (flatSpectrum r) (shrinkingRadius N) :=
    tensorYoungPMF_tail_nonneg _ _ _ _
  have hh := mul_le_mul hcoeff ht ht0 (by positivity : 0 ≤ (c+1)*((N:ℝ)+1)^a)
  have htailbound : (c * (N : ℝ)^a+1) *
      tailProbability (tensorFlatYoungPMF N r hr) (flatSpectrum r) (shrinkingRadius N) ≤
      ((c+1)*C) * (((N:ℝ)+1)^(a+s)*concentrationEnvelope r N) := by
    convert hh using 1 <;> dsimp only [C, s] <;> rw [pow_add] <;> ring
  exact hmean.trans (by linarith)

/-- Both moments are proved for the constructed physical measurement law. -/
theorem tensorFlatYoungPMF_dimension_moments (r k : ℕ) (hr : 0 < r) :
    Tendsto (fun N => ∑ mu, (tensorFlatYoungPMF N r hr mu).toReal *
      normalizedDimension r k N mu) atTop (𝓝 1) ∧
    Tendsto (fun N => ∑ mu, (tensorFlatYoungPMF N r hr mu).toReal *
      inverseNormalizedDimension r k N mu) atTop (𝓝 1) :=
  ⟨mean_tendsto_one_of_mean_absolute_error (fun N => tensorFlatYoungPMF N r hr) _
      (tensorFlatYoungPMF_mean_dimension_error r k hr),
    mean_tendsto_one_of_mean_absolute_error (fun N => tensorFlatYoungPMF N r hr) _
      (tensorFlatYoungPMF_mean_inverse_dimension_error r k hr)⟩

end Cloning.TensorLie
