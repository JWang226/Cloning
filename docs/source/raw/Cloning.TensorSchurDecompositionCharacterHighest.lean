import Cloning.TensorSchurDecompositionCharacter
import Cloning.TensorPBWHighestLine

/-! The actual highest character coefficient is one. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT MvPolynomial
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem physicalCharacterPolynomial_highest_coeff
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (hΩ : ‖Ω‖ = 1)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0) :
    coeff (Finsupp.equivFunOnFinite.symm mu) (physicalCharacterPolynomial Ω) = 1 := by
  classical
  let S := cyclicSector Ω
  have hInv := cyclicSector_generator_invariant Ω (fun a => (mu a : ℂ)) hweight hraise
  have hp (v : Fin n → Fin d) (hv : occupancy v = mu) :
      S.starProjection (registerBasis _ v) = ⟪Ω, registerBasis _ v⟫_ℂ • Ω := by
    have he := cyclicSector_cartanWeight_eq_highest_line Ω mu hΩ hweight
      (Submodule.starProjection_apply_mem S (registerBasis _ v)) (by
        intro a
        simpa only [← hv] using invariant_projection_basis_cartan S hInv v a)
    have hh := Submodule.inner_starProjection_left_eq_right S Ω (registerBasis _ v)
    rw [Submodule.starProjection_eq_self_iff.mpr (highest_mem_cyclicSector Ω)] at hh
    rw [← hh] at he
    exact he
  have hterm (v : Fin n → Fin d) :
      coeff (Finsupp.equivFunOnFinite.symm mu)
        (monomial (occupancyExponent v) (S.starProjection (registerBasis _ v) v)) =
      star (Ω v) * Ω v := by
    by_cases hv : occupancy v = mu
    · have hexp : occupancyExponent v = Finsupp.equivFunOnFinite.symm mu := by
        unfold occupancyExponent
        rw [hv]
      rw [coeff_monomial, if_pos hexp, hp v hv]
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      congr 1
      rw [← inner_conj_symm, registerBasis_apply, register_inner_single]
      rfl
    · have hexp : occupancyExponent v ≠ Finsupp.equivFunOnFinite.symm mu := by
        intro he
        apply hv
        exact congrArg (fun f : Fin d →₀ ℕ => fun a => f a) he
      rw [coeff_monomial, if_neg hexp]
      have hz : Ω v = 0 := by
        by_contra hn
        exact hv (funext (cartan_weight_coefficient Ω mu hweight v hn))
      simp [hz]
  simp only [physicalCharacterPolynomial, tensorWeightTrace_apply, coeff_sum]
  change (∑ v : Fin n → Fin d,
    coeff (Finsupp.equivFunOnFinite.symm mu)
      (monomial (occupancyExponent v) (S.starProjection (registerBasis _ v) v))) = 1
  simp_rw [hterm]
  have hi : ⟪Ω, Ω⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hΩ]
    norm_num
  rw [lp.inner_eq_tsum, tsum_fintype] at hi
  simpa only [RCLike.inner_apply, mul_comm] using hi

end Cloning.TensorLie
