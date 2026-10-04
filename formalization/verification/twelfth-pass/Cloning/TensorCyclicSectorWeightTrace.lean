import Cloning.TensorLieRelations

/-! The total Cartan weight determines the literal tensor length. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
variable {n m d : ℕ}

theorem highest_weight_sum (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω) (hΩ : Ω ≠ 0) :
    (∑ a, mu a) = (n : ℂ) := by
  have h := congrArg (fun T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) => T Ω)
    (sum_collectiveGenerator_diagonal (n := n) (A := Fin d))
  simp only [ContinuousLinearMap.sum_apply, hweight, ← Finset.sum_smul,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at h
  exact smul_left_injective ℂ hΩ h

/-- Equal Cartan eigenvalues of normalized physical tensors force the same
tensor length. Raising annihilation is not needed. -/
theorem highest_tensorLength_eq (Ω : TensorRegister n (Fin d)) (Ψ : TensorRegister m (Fin d))
    (mu : Fin d → ℂ)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hΨweight : ∀ a, collectiveGenerator m a a Ψ = mu a • Ψ)
    (hΩnorm : ‖Ω‖ = 1) (hΨnorm : ‖Ψ‖ = 1) : n = m := by
  have hΩ : Ω ≠ 0 := by intro h; simp [h] at hΩnorm
  have hΨ : Ψ ≠ 0 := by intro h; simp [h] at hΨnorm
  have h : (n : ℂ) = (m : ℂ) :=
    (highest_weight_sum Ω mu hΩweight hΩ).symm.trans (highest_weight_sum Ψ mu hΨweight hΨ)
  exact_mod_cast h

end Cloning.TensorLie
