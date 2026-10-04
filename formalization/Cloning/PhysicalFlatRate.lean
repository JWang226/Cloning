import Cloning.YoungDimensionMomentRate
import Cloning.PhysicalFlatConverseFinite

/-! The actual finite rank-flat converse has relative error O(1/n), uniformly
for every larger output sample size. -/
noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace Cloning.PhysicalFlatConverse
open Cloning.TensorLie Cloning.YoungGeneral Cloning.YoungDimensionRatio
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

def flatConverseRateConstant (r k : ℕ) : ℝ := 2*dimensionMomentRateConstant r k+1

theorem flatConverseRateConstant_nonneg (r k : ℕ) : 0≤flatConverseRateConstant r k := by
  have := dimensionMomentRateConstant_nonneg r k
  unfold flatConverseRateConstant
  positivity

private theorem pmf_mean_le_one_add_error {ι : Type*} [Fintype ι]
    (P : PMF ι) (f : ι→ℝ) :
    (∑i,(P i).toReal*f i)≤1+∑i,(P i).toReal*|f i-1| := by
  have hmass : ∑i,(P i).toReal=1 := by
    simpa only [tsum_fintype,Cloning.YoungCompatibility.probability] using
      Cloning.YoungCompatibility.tsum_probability P
  have hp (i : ι) : (P i).toReal*f i≤(P i).toReal+(P i).toReal*|f i-1| := by
    have h := mul_le_mul_of_nonneg_left (le_abs_self (f i-1))
      (show 0≤(P i).toReal from ENNReal.toReal_nonneg)
    nlinarith
  simpa only [Finset.sum_add_distrib,hmass] using
    Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>hp i)

/-- The actual Schur-dimension upper bound has a finite relative rate,
uniformly in all output lengths m≥n once n is large enough. -/
theorem eventually_flatConverseBound_rate (r k : ℕ) (hr : 0<r) :
    ∀ᶠ (n : ℕ) in atTop, ∀ m : ℕ, n≤m →
      flatConverseBound r k hr n m≤
        ((m:ℝ)/(n:ℝ))^(-(((r*k:ℕ):ℝ)/2))*(1+flatConverseRateConstant r k/(n:ℝ)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (tensorFlatYoungPMF_mean_inverse_dimension_error_le r k hr)
  filter_upwards [Filter.eventually_ge_atTop (max N 1)] with n hn m hmn
  have hn1 : 1≤n := (le_max_right N 1).trans hn
  have hn0 : 0<n := by omega
  have hm0 : 0<m := by omega
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn0
  have hmR : (0:ℝ)<m := Nat.cast_pos.mpr hm0
  have hnm : (n:ℝ)≤m := Nat.cast_le.mpr hmn
  let A := ∑mu,(tensorFlatYoungPMF n r hr mu).toReal*normalizedDimension r k n mu
  let B := ∑mu,(tensorFlatYoungPMF m r hr mu).toReal*inverseNormalizedDimension r k m mu
  let C := flatConverseRateConstant r k
  have hC : 0≤C := flatConverseRateConstant_nonneg r k
  have hA0 : 0≤A := Finset.sum_nonneg (fun mu _=>mul_nonneg ENNReal.toReal_nonneg
    (div_nonneg (dimensionRatio_pos r k (shapeRows mu) (shapeRows_nonneg mu)).le
      (mul_nonneg (leadingConstant_pos r k hr).le (pow_nonneg (Nat.cast_nonneg _) _))))
  have hB0 : 0≤B := Finset.sum_nonneg (fun mu _=>mul_nonneg ENNReal.toReal_nonneg
    (div_nonneg (mul_nonneg (leadingConstant_pos r k hr).le (pow_nonneg (Nat.cast_nonneg _) _))
      (dimensionRatio_pos r k (shapeRows mu) (shapeRows_nonneg mu)).le))
  have hA : A≤1+C/(n:ℝ) := by
    have h := (pmf_mean_le_one_add_error (tensorFlatYoungPMF n r hr)
      (normalizedDimension r k n)).trans (add_le_add le_rfl
        (tensorFlatYoungPMF_mean_dimension_error_le r k n hr hn1))
    apply h.trans
    apply add_le_add le_rfl
    exact div_le_div_of_nonneg_right (by
      dsimp [C,flatConverseRateConstant]
      have := dimensionMomentRateConstant_nonneg r k
      linarith) hnR.le
  have hB : B≤1+C/(n:ℝ) := by
    have hmN : N≤m := (le_max_left N 1).trans (hn.trans hmn)
    have h := (pmf_mean_le_one_add_error (tensorFlatYoungPMF m r hr)
      (inverseNormalizedDimension r k m)).trans (add_le_add le_rfl (hN m hmN))
    exact h.trans (add_le_add le_rfl (div_le_div_of_nonneg_left hC hnR hnm))
  have hu : 0≤1+C/(n:ℝ) := by positivity
  have hsqrt : Real.sqrt (A*B)≤1+C/(n:ℝ) := by
    rw [Real.sqrt_le_iff]
    exact ⟨hu,by simpa only [pow_two] using mul_le_mul hA hB hB0 hu⟩
  rw [flatConverseBound_factorization r k hr n m hn0 hm0]
  change Real.sqrt ((((n:ℝ)/(m:ℝ))^(r*k)*A)*B)≤_
  rw [mul_assoc,Real.sqrt_mul (pow_nonneg (div_nonneg hnR.le hmR.le) _)]
  have hroot : Real.sqrt (((n:ℝ)/(m:ℝ))^(r*k))=
      ((m:ℝ)/(n:ℝ))^(-(((r*k:ℕ):ℝ)/2)) := by
    have he := Cloning.YoungFlat.sqrt_inv_nat_pow ((m:ℝ)/(n:ℝ)) (div_pos hmR hnR) (r*k)
    simpa only [inv_div] using he
  rw [hroot]
  exact mul_le_mul_of_nonneg_left hsqrt (Real.rpow_nonneg (div_nonneg hmR.le hnR.le) _)

/-- The rate applies to the optimization over every actual input-output
quantum channel, not just to a selected protocol. -/
theorem eventually_minimaxValue_rate (r k : ℕ) (hr : 0<r) :
    ∀ᶠ (n : ℕ) in atTop, ∀ m : ℕ, n≤m →
      minimaxValue r k hr n m≤
        ((m:ℝ)/(n:ℝ))^(-(((r*k:ℕ):ℝ)/2))*(1+flatConverseRateConstant r k/(n:ℝ)) := by
  filter_upwards [eventually_flatConverseBound_rate r k hr] with n hn m hmn
  exact (minimaxValue_le_flatConverseBound r k hr n m).trans (hn m hmn)

end Cloning.PhysicalFlatConverse
