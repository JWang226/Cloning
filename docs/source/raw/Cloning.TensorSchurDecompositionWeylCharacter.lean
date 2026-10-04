import Cloning.TensorSchurDecompositionCharacterLeading
import Cloning.TensorSchurDecompositionCharacterSpectrum
import Cloning.TensorSchurDecompositionCharacterSymmetry
import Cloning.WeylCharacterAlternantProduct

/-! The Weyl character identity for the actual physical cyclic tensor sector.
Every algebraic hypothesis is derived from literal tensor operators. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT Cloning.WeylCharacter MvPolynomial
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem physicalCharacterPolynomial_support_DominatedBy
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (hsum : ∑ a, mu a = n)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (m : Fin d →₀ ℕ) (hm : coeff m (physicalCharacterPolynomial Ω) ≠ 0) :
    DominatedBy (fun a => (m a : ℝ)) (fun a => (mu a : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro k hk
    rw [← sum_finPrefix _ hk, ← sum_finPrefix _ hk]
    have h := physicalCharacterPolynomial_support_dominated Ω mu hweight m hm k
    unfold weightPrefix at h
    unfold finPrefix
    dsimp only at h ⊢
    exact_mod_cast h
  · have h := (physicalCharacterPolynomial_support_total Ω m hm).trans hsum.symm
    dsimp only
    exact_mod_cast h

/-- Exact physical Weyl character formula. Normalization, Cartan eigenvalues,
and raising annihilation refer to the actual tensor generator action. -/
theorem physicalCharacterPolynomial_weyl
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (hΩ : ‖Ω‖ = 1)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0) :
    denominator d * physicalCharacterPolynomial Ω =
      alternant (fun a => mu a + staircase a) := by
  have hΩ0 : Ω ≠ 0 := by intro h; simp [h] at hΩ
  have hsum : ∑ a, mu a = n := by
    exact_mod_cast highest_weight_sum Ω (fun a => (mu a : ℂ)) hweight hΩ0
  have hmu : Antitone mu := highest_weight_antitone Ω mu hweight hraise hΩ
  have hstrict : StrictAnti (fun a => mu a + staircase a) := by
    intro a b hab
    exact Nat.add_lt_add_of_le_of_lt (hmu hab.le) (staircase_strictAnti d hab)
  have hsym := physicalCharacterPolynomial_symmetric Ω (fun a => (mu a : ℂ)) hweight hraise
  apply eq_alternant_of_spectral_data _ _ hstrict
  · exact denominator_mul_alternating _ hsym
  · exact physicalCharacterPolynomial_eulerSquares_shifted Ω mu hsum hweight hraise
  · apply denominator_mul_support_dominance
    exact symmetric_subset_dominance _ _ hsym
      (physicalCharacterPolynomial_support_DominatedBy Ω mu hsum hweight)
  · exact physicalCharacterPolynomial_denominator_highest_coeff Ω mu hΩ hweight hraise

/-- The canonical constructed partition tensor satisfies the exact character
identity without any highest-vector or representation-classification premise. -/
theorem partitionCharacterPolynomial_weyl (mu : Fin d → ℕ) (hmu : Antitone mu) :
    denominator d * physicalCharacterPolynomial (partitionHighestTensor mu hmu) =
      alternant (fun a => mu a + staircase a) :=
  physicalCharacterPolynomial_weyl _ mu (partitionHighestTensor_norm mu hmu)
    (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu)

/-- Evaluation at the identity is the actual Hilbert-space dimension. -/
theorem physicalCharacterPolynomial_eval_one
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0) :
    eval (fun _ => (1 : ℂ)) (physicalCharacterPolynomial Ω) =
      (Module.finrank ℂ (cyclicSector Ω) : ℂ) := by
  rw [eval_physicalCharacterPolynomial Ω mu hweight hraise]
  have hd : Matrix.diagonal (fun _ : Fin d => (1 : ℂ)) = 1 := Matrix.diagonal_one
  rw [hd, cyclicTensorOperator_one]
  change LinearMap.trace ℂ _ (LinearMap.id : cyclicSector Ω →ₗ[ℂ] cyclicSector Ω) = _
  exact LinearMap.trace_id ℂ (cyclicSector Ω)

/-- Coordinate-free dimension adapter for the explicitly constructed sector. -/
theorem partitionCharacterPolynomial_eval_one (mu : Fin d → ℕ) (hmu : Antitone mu) :
    eval (fun _ => (1 : ℂ)) (physicalCharacterPolynomial (partitionHighestTensor mu hmu)) =
      (partitionDimension mu hmu : ℂ) :=
  physicalCharacterPolynomial_eval_one _ (fun a => (mu a : ℂ))
    (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu)

end Cloning.TensorLie
