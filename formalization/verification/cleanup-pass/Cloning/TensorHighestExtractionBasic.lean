import Cloning.TensorCyclicSectorCovariance
import Cloning.TensorRootBounds

/-! Computational support of projected Cartan weight vectors. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def physicalWordHeight (w : Fin n → Fin d) : ℕ := ∑ t, (w t).val

theorem physicalWordHeight_update (w : Fin n → Fin d) (t : Fin n) (a : Fin d) :
    physicalWordHeight (Function.update w t a) + (w t).val = physicalWordHeight w + a.val := by
  have he := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl
    (fun u _ => show (Function.update w t a u).val + (if u = t then (w t).val else 0) =
      (w u).val + (if u = t then a.val else 0) from by
        by_cases h : u = t
        · subst u; simp [Nat.add_comm]
        · simp [h])
  simpa only [physicalWordHeight, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] using he

theorem physicalWordHeight_eq_occupancy (w : Fin n → Fin d) :
    physicalWordHeight w = ∑ a : Fin d, a.val * occupancy w a := by
  simp only [occupancy, Finset.card_filter, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp [physicalWordHeight]

theorem cartan_weight_coefficient (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (w : Fin n → Fin d) (hw : Ω w ≠ 0) (a : Fin d) : occupancy w a = mu a := by
  have he := congrArg (fun x : TensorRegister n (Fin d) => x w) (hweight a)
  simp only [collectiveGenerator_diagonal, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at he
  have hc : (occupancy w a : ℂ) = (mu a : ℂ) := mul_right_cancel₀ hw he
  exact_mod_cast hc

theorem invariant_projection_basis_cartan
    (W : Submodule ℂ (TensorRegister n (Fin d)))
    (hW : ∀ a b x, x ∈ W → collectiveGenerator n a b x ∈ W)
    (w : Fin n → Fin d) (a : Fin d) :
    collectiveGenerator n a a (W.starProjection (registerBasis _ w)) =
      (occupancy w a : ℂ) • W.starProjection (registerBasis _ w) := by
  rw [← invariant_starProjection_commutes W hW, collectiveGenerator_diagonal_basis, map_smul]

theorem invariant_exists_projection_basis_ne_zero
    (W : Submodule ℂ (TensorRegister n (Fin d))) (hWne : W ≠ ⊥) :
    ∃ w : Fin n → Fin d, W.starProjection (registerBasis _ w) ≠ 0 := by
  by_contra! hz
  have hP : W.starProjection = 0 := by
    apply register_operator_ext
    intro a c
    simpa only [registerBasis_apply, ContinuousLinearMap.zero_apply] using
      congrArg (fun x : TensorRegister n (Fin d) => x a) (hz c)
  obtain ⟨x, hx, hxne⟩ := W.ne_bot_iff.mp hWne
  have he := Submodule.starProjection_eq_self_iff.mpr hx
  rw [hP, ContinuousLinearMap.zero_apply] at he
  exact hxne he.symm

/-- A nonzero coordinate of a vector in a subspace forces the corresponding
projected computational basis vector to be nonzero. -/
theorem projection_basis_ne_zero_of_coefficient
    (W : Submodule ℂ (TensorRegister n (Fin d)))
    {x : TensorRegister n (Fin d)} (hx : x ∈ W) (w : Fin n → Fin d) (hw : x w ≠ 0) :
    W.starProjection (registerBasis _ w) ≠ 0 := by
  intro hz
  have he := W.inner_starProjection_left_eq_right (registerBasis _ w) x
  rw [hz, Submodule.starProjection_eq_self_iff.mpr hx, inner_zero_left,
    registerBasis_apply, register_inner_single] at he
  exact hw he.symm

/-- Positivity of the actual root norm forces every highest Cartan weight to
be weakly decreasing. -/
theorem highest_weight_antitone (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (hΩ : ‖Ω‖ = 1) : Antitone mu := by
  intro a b hab
  rcases eq_or_lt_of_le hab with rfl | hab
  · rfl
  · have hc := root_diagonal_commutator a b Ω
    rw [hraise a b hab, map_zero, sub_zero, hweight a, hweight b, ← sub_smul] at hc
    have hi : ⟪collectiveGenerator n b a Ω, collectiveGenerator n b a Ω⟫_ℂ =
        (mu a : ℂ) - mu b := by
      rw [collectiveGenerator_inner_adjoint, hc, inner_smul_right,
        inner_self_eq_norm_sq_to_K, hΩ]
      norm_num
    have hp : 0 ≤ ((mu a : ℂ) - mu b).re := by
      rw [← hi]
      exact inner_self_nonneg (𝕜 := ℂ)
    simp only [Complex.sub_re, Complex.natCast_re] at hp
    exact_mod_cast (sub_nonneg.mp hp)

end Cloning.TensorLie
