import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Scalar normalization estimates for physical root commutators. -/
noncomputable section
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000

/-- Uniform off-diagonal coefficient after normalizing two positive gaps. -/
theorem normalized_root_scalar_bound {g h δ : ℝ} (hδ : 0 < δ)
    (hg : δ ≤ g) (hh : δ ≤ h) (r : ℕ) :
    (Real.sqrt g)⁻¹ * (Real.sqrt h)⁻¹ *
      Real.sqrt (((r : ℝ) + 1) * (|g - h| + 2 * r)) ≤
    Real.sqrt (((r : ℝ) + 1) / δ + 2 * r * ((r : ℝ) + 1) / δ ^ 2) := by
  have hg0 : 0 < g := hδ.trans_le hg
  have hh0 : 0 < h := hδ.trans_le hh
  have hprod : 0 < g * h := mul_pos hg0 hh0
  have hsq : δ ^ 2 ≤ g * h := by nlinarith
  have habs : δ * |g - h| ≤ g * h := by
    rcases le_total g h with hgh | hhg
    · rw [abs_of_nonpos (sub_nonpos.mpr hgh)]
      nlinarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hhg)]
      nlinarith
  have hratio : |g - h| / (g * h) ≤ 1 / δ := by
    apply (div_le_div_iff₀ hprod hδ).mpr
    nlinarith
  have hinv : 1 / (g * h) ≤ 1 / δ ^ 2 := by
    exact one_div_le_one_div_of_le (sq_pos_of_pos hδ) hsq
  have hnum : (((r : ℝ) + 1) * (|g - h| + 2 * r)) / (g * h) ≤
      ((r : ℝ) + 1) / δ + 2 * r * ((r : ℝ) + 1) / δ ^ 2 := by
    calc
      _ = ((r : ℝ) + 1) * (|g - h| / (g * h)) +
          (2 * r * ((r : ℝ) + 1)) * (1 / (g * h)) := by ring
      _ ≤ ((r : ℝ) + 1) * (1 / δ) +
          (2 * r * ((r : ℝ) + 1)) * (1 / δ ^ 2) := by gcongr
      _ = _ := by ring
  have hleftsq : ((Real.sqrt g)⁻¹ * (Real.sqrt h)⁻¹ *
      Real.sqrt (((r : ℝ) + 1) * (|g - h| + 2 * r))) ^ 2 =
      (((r : ℝ) + 1) * (|g - h| + 2 * r)) / (g * h) := by
    rw [mul_pow, mul_pow, inv_pow, inv_pow, Real.sq_sqrt hg0.le,
      Real.sq_sqrt hh0.le, Real.sq_sqrt (by positivity)]
    ring
  have hrightsq := Real.sq_sqrt (by positivity :
    0 ≤ ((r : ℝ) + 1) / δ + 2 * r * ((r : ℝ) + 1) / δ ^ 2)
  nlinarith [Real.sqrt_nonneg (((r : ℝ) + 1) / δ + 2 * r * ((r : ℝ) + 1) / δ ^ 2)]

end Cloning.TensorLie
