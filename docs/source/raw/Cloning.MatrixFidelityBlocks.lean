import Cloning.MatrixFidelity

/-!
# Fidelity of finite dependent block-diagonal matrices

The square-root identity is proved from positivity and uniqueness of positive
square roots. The block index and every block's matrix dimension are finite;
different blocks may have different dimensions.
-/

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix
namespace Cloning.MatrixFidelity

set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {d : ι → Type*} [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]

/-- Positive semidefiniteness of a finite dependent direct sum. -/
lemma blockDiagonal'_posSemidef (A : ∀ i, Matrix (d i) (d i) ℂ)
    (hA : ∀ i, (A i).PosSemidef) : (Matrix.blockDiagonal' A).PosSemidef := by
  let S := Matrix.blockDiagonal' (fun i => CFC.sqrt (A i))
  have hsq : S.conjTranspose * S = Matrix.blockDiagonal' A := by
    dsimp [S]
    rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
    congr 1
    funext i
    rw [((CFC.sqrt_nonneg (A i)).posSemidef).isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self (A i) (hA i).nonneg
  rw [← hsq]
  exact Matrix.posSemidef_conjTranspose_mul_self S

/-- The positive square root commutes with finite dependent direct sums. -/
lemma sqrt_blockDiagonal' (A : ∀ i, Matrix (d i) (d i) ℂ)
    (hA : ∀ i, (A i).PosSemidef) :
    CFC.sqrt (Matrix.blockDiagonal' A) =
      Matrix.blockDiagonal' (fun i => CFC.sqrt (A i)) := by
  apply CFC.sqrt_unique
  · rw [← Matrix.blockDiagonal'_mul]
    congr 1
    funext i
    exact CFC.sqrt_mul_sqrt_self (A i) (hA i).nonneg
  · exact (blockDiagonal'_posSemidef _
      (fun i => (CFC.sqrt_nonneg (A i)).posSemidef)).nonneg

/-- Root fidelity is additive over finite dependent orthogonal direct sums.
This theorem uses the concrete matrix definition, not an abstract fidelity law. -/
lemma fidelity_blockDiagonal' (A B : ∀ i, Matrix (d i) (d i) ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef) :
    fidelity (Matrix.blockDiagonal' A) (Matrix.blockDiagonal' B) =
      ∑ i, fidelity (A i) (B i) := by
  unfold fidelity
  rw [sqrt_blockDiagonal' B hB, ← Matrix.blockDiagonal'_mul,
    ← Matrix.blockDiagonal'_mul]
  rw [sqrt_blockDiagonal' _ (fun i => sandwich_posSemidef (hA i) (B i)),
    Matrix.trace_blockDiagonal']
  simp

end Cloning.MatrixFidelity
