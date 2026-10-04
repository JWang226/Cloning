import Cloning.TensorSchurDecompositionCharacter
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! Weyl symmetry of the actual physical character, derived from tensor
permutation matrices and trace conjugacy. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT MvPolynomial
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem diagonal_permutation_conjugate (D : Fin d → ℂ) (σ : Equiv.Perm (Fin d)) :
    Matrix.diagonal (D ∘ σ) = σ.permMatrix ℂ * Matrix.diagonal D * σ⁻¹.permMatrix ℂ := by
  ext a b
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, Equiv.Perm.inv_def, Equiv.symm_symm]
  simp [Matrix.diagonal_apply, σ.injective.eq_iff, Function.comp_def]

/-- Full permutation symmetry follows from the actual invariant tensor
representation, rather than a supplied symmetric-character law. -/
theorem physicalCharacterPolynomial_symmetric
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (σ : Equiv.Perm (Fin d)) :
    rename σ (physicalCharacterPolynomial Ω) = physicalCharacterPolynomial Ω := by
  apply MvPolynomial.funext
  intro D
  rw [eval_rename, eval_physicalCharacterPolynomial Ω mu hweight hraise,
    eval_physicalCharacterPolynomial Ω mu hweight hraise,
    diagonal_permutation_conjugate, cyclicTensorOperator_mul, cyclicTensorOperator_mul]
  let A := cyclicTensorOperator Ω mu hweight hraise (σ.permMatrix ℂ)
  let B := cyclicTensorOperator Ω mu hweight hraise (Matrix.diagonal D)
  let C := cyclicTensorOperator Ω mu hweight hraise (σ⁻¹.permMatrix ℂ)
  have he : C * A = 1 := by
    dsimp only [C, A]
    rw [← cyclicTensorOperator_mul, ← Matrix.permMatrix_mul, mul_inv_cancel,
      Matrix.permMatrix_one, cyclicTensorOperator_one]
  change LinearMap.trace ℂ _ (A.toLinearMap * B.toLinearMap * C.toLinearMap) =
    LinearMap.trace ℂ _ B.toLinearMap
  rw [LinearMap.trace_mul_cycle]
  change LinearMap.trace ℂ _ ((C * A) * B).toLinearMap = _
  rw [he, one_mul]

end Cloning.TensorLie
