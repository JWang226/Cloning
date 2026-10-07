import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-! Exact inversion of the power-fidelity sample threshold and its finite
binomial sufficient bound. The quantity here is the input/additional-copy ratio. -/
noncomputable section
open scoped BigOperators
namespace Cloning.SampleRatio

def threshold (a ε : ℝ) : ℝ := 1 / ((1-ε)^(-1/a)-1)

theorem threshold_denominator_pos {a ε : ℝ} (ha : 0<a) (hε : 0<ε) (hε1 : ε<1) :
    0 < (1-ε)^(-1/a)-1 := by
  have he : 1 < (1-ε)^(-1/a) := by
    have h := Real.rpow_lt_rpow_of_neg (sub_pos.mpr hε1)
      (show 1-ε<1 by linarith)
      (show (-1:ℝ)/a<0 from div_neg_of_neg_of_pos (by norm_num) ha)
    simpa using h
  linarith

theorem threshold_pos {a ε : ℝ} (ha : 0<a) (hε : 0<ε) (hε1 : ε<1) :
    0 < threshold a ε := one_div_pos.mpr (threshold_denominator_pos ha hε hε1)

/-- Exact threshold, before taking any small-error limit. -/
theorem power_fidelity_iff {a ε R : ℝ} (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (hR : 0<R) :
    1-ε ≤ (1+R⁻¹)^(-a) ↔ threshold a ε ≤ R := by
  have hbase : 0 < 1+R⁻¹ := by positivity
  have hpow := Real.le_rpow_inv_iff_of_neg hbase (sub_pos.mpr hε1) (neg_neg_of_pos ha)
  have hexp : (-a)⁻¹ = -1/a := by simp [div_eq_mul_inv]
  rw [hexp] at hpow
  rw [← hpow]
  unfold threshold
  rw [div_le_iff₀ (threshold_denominator_pos ha hε hε1)]
  constructor
  · intro h
    have hh := mul_le_mul_of_nonneg_left h hR.le
    rw [mul_add, mul_inv_cancel₀ hR.ne'] at hh
    nlinarith
  · intro h
    have hh : 1/R ≤ (1-ε)^(-1/a)-1 := (div_le_iff₀ hR).mpr (by nlinarith)
    simpa only [one_div] using (show 1+1/R ≤ (1-ε)^(-1/a) by linarith)

/-- Each finite symmetric-dimension factor is at least its unshifted value. -/
theorem shifted_ratio_lower {N M j : ℝ} (hN : 0<N) (hM : 0≤M) (hj : 0≤j) :
    N/(N+M) ≤ (N+j)/(N+M+j) := by
  rw [div_le_div_iff₀ (by linarith : 0<N+M) (by linarith : 0<N+M+j)]
  nlinarith [mul_nonneg hM hj]

theorem finite_product_lower (a N M : ℕ) (hN : 0<N) :
    ((N:ℝ)/(N+M))^a ≤ ∏ j ∈ Finset.range a,
      ((N:ℝ)+j+1)/((N:ℝ)+M+j+1) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  calc
    ((N:ℝ)/(N+M))^a = ∏ _j ∈ Finset.range a, (N:ℝ)/(N+M) := by simp [div_pow]
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => by positivity) (fun j _ => by
      convert shifted_ratio_lower hn (Nat.cast_nonneg M)
        (show (0:ℝ)≤j+1 by positivity) using 1 <;> ring_nf)

end Cloning.SampleRatio
