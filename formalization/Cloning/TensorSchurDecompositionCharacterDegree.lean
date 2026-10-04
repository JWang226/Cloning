import Cloning.TensorSchurDecompositionCharacter

/-! The actual physical character is homogeneous of the tensor degree. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT MvPolynomial
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

theorem tensorWeightTrace_totalEuler
    (T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d)) :
    (∑ a : Fin d, X a * pderiv a (tensorWeightTrace T)) = (n : ℂ) • tensorWeightTrace T := by
  simp only [tensorWeightTrace_apply, map_sum, Finset.mul_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp only [X_mul_pderiv_monomial, occupancyExponent_apply, ← Finset.sum_smul, sum_occupancy]
  simp only [smul_monomial, nsmul_eq_mul, smul_eq_mul]

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem physicalCharacterPolynomial_totalEuler (Ω : TensorRegister n (Fin d)) :
    (∑ a : Fin d, X a * pderiv a (physicalCharacterPolynomial Ω)) =
      (n : ℂ) • physicalCharacterPolynomial Ω :=
  tensorWeightTrace_totalEuler _

theorem physicalCharacterPolynomial_support_total
    (Ω : TensorRegister n (Fin d)) (m : Fin d →₀ ℕ)
    (hm : coeff m (physicalCharacterPolynomial Ω) ≠ 0) : ∑ a, m a = n := by
  classical
  have hv : ∃ v : Fin n → Fin d, occupancyExponent v = m ∧
      (cyclicSector Ω).starProjection (registerBasis _ v) v ≠ 0 := by
    by_contra! hh
    apply hm
    simp only [physicalCharacterPolynomial, tensorWeightTrace_apply, coeff_sum]
    apply Finset.sum_eq_zero
    intro v _
    by_cases hvm : occupancyExponent v = m
    · simp only [coeff_monomial, hvm, if_true]
      exact hh v hvm
    · simp [coeff_monomial, hvm]
  obtain ⟨v, rfl, _⟩ := hv
  exact sum_occupancy v

end Cloning.TensorLie
