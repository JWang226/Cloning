import Cloning.TensorSchurDecompositionRadial
import Cloning.TensorSchurDecompositionRootSum
import Cloning.TensorSchurDecompositionCharacterDegree
import Cloning.WeylCharacterAlternantDenominator

/-! Assembly of the actual physical radial character equation. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT MvPolynomial
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Each Cartan coordinate occurs in precisely d-1 unordered root pairs. -/
theorem sum_positiveRoot_endpoints (f : Fin d → MvPolynomial (Fin d) ℂ) :
    (∑ r : PositiveRoot d, (f r.val.1 + f r.val.2)) =
      ((d : ℂ) - 1) • (∑ a, f a) := by
  have hs := sum_matrix_eq_diagonal_add_roots (fun a (_ : Fin d) => f a)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Finset.smul_sum] at hs
  have hc : (d : ℕ) • (∑ a, f a) = (d : ℂ) • (∑ a, f a) := by
    simp [Algebra.smul_def]
  rw [hc] at hs
  rw [sub_smul, one_smul]
  exact eq_sub_of_add_eq' hs.symm

theorem weylDenominator_euler_cross_radial (f : MvPolynomial (Fin d) ℂ) :
    2 * (∑ a : Fin d, (X a * pderiv a (weylDenominator d)) * (X a * pderiv a f)) =
      (∑ r : PositiveRoot d, weylDenominatorErase r * (X r.val.1 + X r.val.2) *
        (X r.val.1 * pderiv r.val.1 f - X r.val.2 * pderiv r.val.2 f)) +
      weylDenominator d * (((d : ℂ) - 1) • (∑ a : Fin d, X a * pderiv a f)) := by
  rw [weylDenominator_euler_cross, Finset.mul_sum, ← sum_positiveRoot_endpoints,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [← weylDenominator_factor r]
  ring

theorem eulerLaplacian_mul (f g : MvPolynomial (Fin d) ℂ) :
    (∑ a : Fin d, X a * pderiv a (X a * pderiv a (f * g))) =
      (∑ a : Fin d, X a * pderiv a (X a * pderiv a f)) * g +
      2 * (∑ a : Fin d, (X a * pderiv a f) * (X a * pderiv a g)) +
      f * (∑ a : Fin d, X a * pderiv a (X a * pderiv a g)) := by
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [pderiv_mul, map_add, pderiv_X, Pi.single_eq_same]
  ring

/-- The denominator times the non-Cartan Casimir contribution equals the
sum of the genuine root radial terms. -/
theorem physicalCharacterPolynomial_radial_sum
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0) :
    (∑ r : PositiveRoot d, weylDenominatorErase r * (X r.val.1 + X r.val.2) *
      (X r.val.1 * pderiv r.val.1 (physicalCharacterPolynomial Ω) -
        X r.val.2 * pderiv r.val.2 (physicalCharacterPolynomial Ω))) =
      weylDenominator d * (casimirEigenvalue mu • physicalCharacterPolynomial Ω -
        ∑ a : Fin d, X a * pderiv a (X a * pderiv a (physicalCharacterPolynomial Ω))) := by
  let P := (cyclicSector Ω).starProjection
  have hP (a b : Fin d) : P * collectiveGenerator n a b = collectiveGenerator n a b * P :=
    ContinuousLinearMap.ext (invariant_starProjection_commutes (cyclicSector Ω)
      (cyclicSector_generator_invariant Ω mu hweight hraise) a b)
  have he := tensorWeightTrace_casimir_decomposition P
  rw [tensorWeightTrace_casimir Ω mu hweight hraise] at he
  have hr := eq_sub_of_add_eq' he.symm
  simp only [show tensorWeightTrace P = physicalCharacterPolynomial Ω from rfl] at hr
  change (∑ r : PositiveRoot d, weylDenominatorErase r * (X r.val.1 + X r.val.2) *
      (X r.val.1 * pderiv r.val.1 (tensorWeightTrace P) -
        X r.val.2 * pderiv r.val.2 (tensorWeightTrace P))) = _
  rw [← hr, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [mul_assoc, ← tensorWeightTrace_root_pair P r.val.1 r.val.2 (hP _ _)]
  rw [← mul_assoc, mul_comm (weylDenominatorErase r), weylDenominator_factor]

/-- The physical Casimir equation after multiplication by the Weyl
 denominator. Only the separately explicit denominator Laplacian remains. -/
theorem physicalCharacterPolynomial_denominator_laplacian
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0) :
    (∑ a : Fin d, X a * pderiv a (X a * pderiv a
      (weylDenominator d * physicalCharacterPolynomial Ω))) =
      (∑ a : Fin d, X a * pderiv a (X a * pderiv a (weylDenominator d))) *
        physicalCharacterPolynomial Ω +
      (casimirEigenvalue mu + ((d : ℂ) - 1) * n) •
        (weylDenominator d * physicalCharacterPolynomial Ω) := by
  rw [eulerLaplacian_mul, weylDenominator_euler_cross_radial,
    physicalCharacterPolynomial_radial_sum Ω mu hweight hraise,
    physicalCharacterPolynomial_totalEuler]
  simp only [Algebra.smul_def, map_add, map_mul]
  ring

/-- Exact Euler-square eigenvalue of the actual denominator-character product. -/
theorem physicalCharacterPolynomial_eulerSquares
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0) :
    Cloning.WeylCharacter.eulerSquares (weylDenominator d * physicalCharacterPolynomial Ω) =
      ((∑ a : Fin d, (Cloning.WeylCharacter.staircase a : ℂ)^2) +
        casimirEigenvalue mu + ((d : ℂ) - 1) * n) •
        (weylDenominator d * physicalCharacterPolynomial Ω) := by
  rw [Cloning.WeylCharacter.eulerSquares_apply,
    physicalCharacterPolynomial_denominator_laplacian Ω mu hweight hraise]
  have hd : (∑ a : Fin d, X a * pderiv a (X a * pderiv a (weylDenominator d))) =
      (∑ a : Fin d, (Cloning.WeylCharacter.staircase a : ℂ)^2) • weylDenominator d :=
    by simpa only [Cloning.WeylCharacter.eulerSquares_apply, weylDenominator,
      Cloning.WeylCharacter.denominator] using Cloning.WeylCharacter.eulerSquares_denominator d
  rw [hd]
  simp only [Algebra.smul_def, map_add, map_mul]
  ring

end Cloning.TensorLie
