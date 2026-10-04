import Cloning.TensorLocalUnitaryFockPolynomial

/-! Reverse vector control for the actual adjoint cutoff transport. -/
noncomputable section
open scoped InnerProductSpace
namespace Cloning.TensorLocalUnitary
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem adjoint_contraction (V : H →L[ℂ] K) (hV : ∀ x, ‖V x‖ ≤ ‖x‖) (y : K) :
    ‖V.adjoint y‖ ≤ ‖y‖ := by
  have hop : ‖V‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (fun x => by simpa only [one_mul] using hV x)
  calc
    ‖V.adjoint y‖ ≤ ‖V.adjoint‖ * ‖y‖ := V.adjoint.le_opNorm y
    _ ≤ 1 * ‖y‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_mul_of_nonneg_right hop (norm_nonneg _)
    _ = ‖y‖ := one_mul _

/-- Forward approximation between almost-normalized physical and unit target
vectors forces reverse approximation by the genuine adjoint contraction. -/
theorem reverse_vector_norm_sq_le (V : H →L[ℂ] K) (hV : ∀ x, ‖V x‖ ≤ ‖x‖)
    (x : H) (y : K) (hy : ‖y‖ = 1) :
    ‖V.adjoint y - x‖^2 ≤ ‖x‖^2 - 1 + 2*‖V x-y‖ := by
  have hnorm := adjoint_contraction V hV y
  rw [hy] at hnorm
  have hinner : 1 - (⟪y, V x⟫_ℂ).re ≤ ‖V x-y‖ := by
    have h := (Complex.re_le_norm ⟪y, y-V x⟫_ℂ).trans (norm_inner_le_norm _ _)
    have hyy : (⟪y,y⟫_ℂ).re = 1 := by
      change RCLike.re (⟪y,y⟫_ℂ) = 1
      rw [← norm_sq_eq_re_inner (𝕜 := ℂ), hy, one_pow]
    rw [inner_sub_right, Complex.sub_re, hyy, hy, one_mul, norm_sub_rev] at h
    exact h
  rw [norm_sub_sq (𝕜 := ℂ), V.adjoint_inner_left]
  change ‖V.adjoint y‖^2 - 2*(⟪y,V x⟫_ℂ).re + ‖x‖^2 ≤ _
  nlinarith [norm_nonneg (V.adjoint y)]

theorem reverse_unit_vector_norm_sq_le (V : H →L[ℂ] K) (hV : ∀ x, ‖V x‖ ≤ ‖x‖)
    (x : H) (y : K) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖V.adjoint y-x‖^2 ≤ 2*‖V x-y‖ := by
  simpa only [hx, one_pow, sub_self, zero_add] using reverse_vector_norm_sq_le V hV x y hy

end Cloning.TensorLocalUnitary
