import Cloning.WeylCharacterDimension
import Cloning.TensorSchurDecompositionWeylCharacter

/-! Exact Weyl dimensions for actual physical cyclic tensor sectors.
The character identity and its value at one are derived from physical operators. -/
noncomputable section
open scoped BigOperators Classical InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT MvPolynomial Cloning.WeylCharacter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- The Weyl product is the dimension of the actual physical cyclic sector. -/
theorem physicalSector_finrank_eq_dimensionProduct
    (Ω : TensorRegister n (Fin d)) (μ : Fin d → ℕ) (hΩ : ‖Ω‖ = 1)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (μ a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0) :
    (Module.finrank ℂ (cyclicSector Ω) : ℝ) = dimensionProduct μ := by
  have hμ := highest_weight_antitone Ω μ hweight hraise hΩ
  have hχ : physicalCharacterPolynomial Ω * denominator d =
      alternant (fun i ↦ μ i + staircase i) := by
    rw [mul_comm]
    exact physicalCharacterPolynomial_weyl Ω μ hΩ hweight hraise
  have he := eval_one_eq_dimensionProduct (physicalCharacterPolynomial Ω) μ hμ hχ
  rw [physicalCharacterPolynomial_eval_one Ω (fun a ↦ (μ a : ℂ)) hweight hraise] at he
  exact_mod_cast he

/-- No representation-classification premise is needed for the canonical sector. -/
theorem partitionDimension_eq_dimensionProduct (μ : Fin d → ℕ) (hμ : Antitone μ) :
    (partitionDimension μ hμ : ℝ) = dimensionProduct μ :=
  physicalSector_finrank_eq_dimensionProduct (partitionHighestTensor μ hμ) μ
    (partitionHighestTensor_norm μ hμ) (partitionHighestTensor_cartan μ hμ)
    (partitionHighestTensor_raising_zero μ hμ)

/-- The conventional ordered-pair form of the exact physical dimension formula. -/
theorem partitionDimension_eq_weylProduct (μ : Fin d → ℕ) (hμ : Antitone μ) :
    (partitionDimension μ hμ : ℝ) = ∏ i : Fin d, ∏ j ∈ Finset.Ioi i,
      (((μ i : ℝ) - μ j + j.val - i.val) / ((j.val : ℝ) - i.val)) := by
  rw [partitionDimension_eq_dimensionProduct μ hμ, dimensionProduct_eq_pairProduct]

end Cloning.TensorLie
