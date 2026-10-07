import Cloning.YoungDimensionMomentRate

/-! Big-O endpoints for the derived physical dimension moments. -/
noncomputable section
open scoped BigOperators Classical Topology
open Filter Asymptotics
namespace Cloning.TensorLie
open Cloning.YoungGeneral
set_option maxHeartbeats 1000000

private theorem mean_sub_one_abs_le {ι : Type*} [Fintype ι] (P : PMF ι) (f : ι→ℝ) :
    |(∑i,(P i).toReal*f i)-1|≤∑i,(P i).toReal*|f i-1| := by
  have hs : ∑i,(P i).toReal=1 := by
    simpa only [tsum_fintype,Cloning.YoungCompatibility.probability] using
      Cloning.YoungCompatibility.tsum_probability P
  have he : (∑i,(P i).toReal*f i)-1=∑i,(P i).toReal*(f i-1) := by
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib,hs]
  rw [he]
  exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_mul,abs_of_nonneg ENNReal.toReal_nonneg])

/-- Both physical dimension moments have relative rate O(1/N). -/
theorem tensorFlatYoungPMF_dimension_moments_isBigO (r k : ℕ) (hr : 0<r) :
    (fun N : ℕ => (∑mu,(tensorFlatYoungPMF N r hr mu).toReal*
      normalizedDimension r k N mu)-1) =O[atTop] (fun N : ℕ=>1/(N:ℝ)) ∧
    (fun N : ℕ => (∑mu,(tensorFlatYoungPMF N r hr mu).toReal*
      inverseNormalizedDimension r k N mu)-1) =O[atTop] (fun N : ℕ=>1/(N:ℝ)) := by
  constructor
  · apply IsBigO.of_bound (dimensionMomentRateConstant r k)
    filter_upwards [eventually_ge_atTop 1] with N hN
    have h := (mean_sub_one_abs_le (tensorFlatYoungPMF N r hr)
      (normalizedDimension r k N)).trans (tensorFlatYoungPMF_mean_dimension_error_le r k N hr hN)
    simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤1/(N:ℝ)),mul_one_div] using h
  · apply IsBigO.of_bound (2*dimensionMomentRateConstant r k+1)
    filter_upwards [tensorFlatYoungPMF_mean_inverse_dimension_error_le r k hr] with N hN
    have h := (mean_sub_one_abs_le (tensorFlatYoungPMF N r hr)
      (inverseNormalizedDimension r k N)).trans hN
    simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤1/(N:ℝ)),mul_one_div] using h

end Cloning.TensorLie
