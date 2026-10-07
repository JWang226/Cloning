import Cloning.TensorRootBounds

/-! Quantitative physical-root errors and their fixed-cutoff asymptotics. -/
noncomputable section
open scoped Topology
open Filter
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def rootError (r : ℕ) (δ : ℝ) : ℝ :=
  max (2 * r / δ) (Real.sqrt (((r : ℝ) + 1) / δ + 2 * r * ((r : ℝ) + 1) / δ ^ 2))

theorem rootError_nonneg (r : ℕ) (δ : ℝ) : 0 ≤ rootError r δ :=
  (Real.sqrt_nonneg _).trans (le_max_right _ _)

theorem rootError_le_one (r : ℕ) {δ : ℝ} (hδ : 2 * ((r : ℝ) + 1) ≤ δ) :
    rootError r δ ≤ 1 := by
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hδpos : 0 < δ := by linarith
  apply max_le
  · exact (div_le_iff₀ hδpos).mpr (by linarith)
  · apply Real.sqrt_le_one.mpr
    have hfirst : ((r : ℝ) + 1) / δ ≤ 1 / 2 :=
      (div_le_iff₀ hδpos).mpr (by linarith)
    have hsecond : 2 * (r : ℝ) * ((r : ℝ) + 1) / δ ^ 2 ≤ 1 / 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hδpos)).mpr
      have hs : (2 * ((r : ℝ) + 1)) ^ 2 ≤ δ ^ 2 := by nlinarith
      nlinarith [sq_nonneg (r : ℝ)]
    linarith

theorem rootError_mono {r s : ℕ} (hrs : r ≤ s) {δ : ℝ} (hδ : 0 ≤ δ) :
    rootError r δ ≤ rootError s δ := by
  apply max_le_max
  · gcongr
  · apply Real.sqrt_le_sqrt
    gcongr

theorem rootError_tendsto_zero (r : ℕ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop) :
    Tendsto (fun n => rootError r (δ n)) atTop (𝓝 0) := by
  have hi : Tendsto (fun n => (δ n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hδ
  have hfirst : Tendsto (fun n => ((r : ℝ) + 1) / δ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul ((r : ℝ) + 1)
  have hsecond : Tendsto (fun n => 2 * (r : ℝ) * ((r : ℝ) + 1) / δ n ^ 2)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by omega : 2 ≠ 0), mul_zero]
      using (hi.pow 2).const_mul (2 * (r : ℝ) * ((r : ℝ) + 1))
  have hsqrt := (hfirst.add hsecond).sqrt
  have hdiag := hi.const_mul (2 * (r : ℝ))
  simpa only [rootError, div_eq_mul_inv, mul_zero, zero_add, Real.sqrt_zero, max_self]
    using hdiag.max hsqrt

end Cloning.TensorLie
