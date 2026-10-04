import Cloning.TensorHighestGramAction
import Cloning.TensorRootBounds

/-! Exact lowering-word Gram equality for physical normalized highest tensors
of equal weight. This is finite algebra, independent of asymptotic CCR bounds. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n m d : ℕ}

theorem inner_formalRealization_eq
    (Ω : TensorRegister n (Fin d)) (Ψ : TensorRegister m (Fin d))
    (x : TensorRegister n (Fin d)) (y : TensorRegister m (Fin d))
    (h : ∀ w, ⟪x, loweringWord Ω w⟫_ℂ = ⟪y, loweringWord Ψ w⟫_ℂ)
    (f : FormalLowering d) :
    ⟪x, formalRealization Ω f⟫_ℂ = ⟪y, formalRealization Ψ f⟫_ℂ := by
  simp only [formalRealization, Finsupp.linearCombination_apply, Finsupp.sum,
    inner_sum, inner_smul_right, h]

theorem highest_inner_loweringWord_cons_zero
    (Ω : TensorRegister n (Fin d))
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (c : PositiveRoot d) (w : List (PositiveRoot d)) :
    ⟪Ω, loweringWord Ω (c :: w)⟫_ℂ = 0 := by
  rw [loweringWord, ← collectiveGenerator_inner_adjoint c.val.2 c.val.1,
    hraise c.val.1 c.val.2 c.property, inner_zero_left]

/-- Normalized actual highest tensors of equal weight have exactly the same
Gram matrix on every pair of lowering words, regardless of their ambient
tensor lengths. No intertwiner or independence property is assumed. -/
theorem highest_loweringWord_gram_eq
    (Ω : TensorRegister n (Fin d)) (Ψ : TensorRegister m (Fin d))
    (mu : Fin d → ℂ)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hΨweight : ∀ a, collectiveGenerator m a a Ψ = mu a • Ψ)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (hΨraise : ∀ a b, a < b → collectiveGenerator m a b Ψ = 0)
    (hΩnorm : ‖Ω‖ = 1) (hΨnorm : ‖Ψ‖ = 1)
    (u v : List (PositiveRoot d)) :
    ⟪loweringWord Ω u, loweringWord Ω v⟫_ℂ =
      ⟪loweringWord Ψ u, loweringWord Ψ v⟫_ℂ := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => simp [loweringWord, inner_self_eq_norm_sq_to_K, hΩnorm, hΨnorm]
      | cons c w =>
          simp only [loweringWord] at *
          exact (highest_inner_loweringWord_cons_zero Ω hΩraise c w).trans
            (highest_inner_loweringWord_cons_zero Ψ hΨraise c w).symm
  | cons c u ih =>
      simp only [loweringWord, collectiveGenerator_inner_adjoint]
      rw [← formalRealization_highestAction Ω mu hΩweight hΩraise,
        ← formalRealization_highestAction Ψ mu hΨweight hΨraise]
      exact inner_formalRealization_eq Ω Ψ (loweringWord Ω u) (loweringWord Ψ u) ih _

/-- Equal highest weights preserve inner products for arbitrary finite linear
combinations, including every linear relation among lowering words. -/
theorem highest_formalRealization_inner_eq
    (Ω : TensorRegister n (Fin d)) (Ψ : TensorRegister m (Fin d))
    (mu : Fin d → ℂ)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hΨweight : ∀ a, collectiveGenerator m a a Ψ = mu a • Ψ)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (hΨraise : ∀ a b, a < b → collectiveGenerator m a b Ψ = 0)
    (hΩnorm : ‖Ω‖ = 1) (hΨnorm : ‖Ψ‖ = 1)
    (f g : FormalLowering d) :
    ⟪formalRealization Ω f, formalRealization Ω g⟫_ℂ =
      ⟪formalRealization Ψ f, formalRealization Ψ g⟫_ℂ := by
  simp only [formalRealization, Finsupp.linearCombination_apply, Finsupp.sum,
    sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  simp_rw [highest_loweringWord_gram_eq Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm]

theorem highest_formalRealization_norm_eq
    (Ω : TensorRegister n (Fin d)) (Ψ : TensorRegister m (Fin d))
    (mu : Fin d → ℂ)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hΨweight : ∀ a, collectiveGenerator m a a Ψ = mu a • Ψ)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (hΨraise : ∀ a b, a < b → collectiveGenerator m a b Ψ = 0)
    (hΩnorm : ‖Ω‖ = 1) (hΨnorm : ‖Ψ‖ = 1)
    (f : FormalLowering d) : ‖formalRealization Ω f‖ = ‖formalRealization Ψ f‖ := by
  have he := congrArg Complex.re
    (highest_formalRealization_inner_eq Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm f f)
  change (RCLike.re : ℂ → ℝ) ⟪formalRealization Ω f, formalRealization Ω f⟫_ℂ =
    (RCLike.re : ℂ → ℝ) ⟪formalRealization Ψ f, formalRealization Ψ f⟫_ℂ at he
  simp only [inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg (formalRealization Ω f), norm_nonneg (formalRealization Ψ f)]

end Cloning.TensorLie
