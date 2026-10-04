import Cloning.MatrixFidelity

/-!
# Isometric invariance of concrete matrix root fidelity

Rectangular isometries are allowed, so this also proves invariance under
embedding a state into a larger support, as used by rank compression.
-/

open scoped MatrixOrder ComplexOrder
open Matrix

noncomputable section

namespace Cloning.MatrixFidelity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem sqrt_isometric_embedding (J : Matrix m n ℂ) (hJ : Jᴴ * J = 1)
    {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    CFC.sqrt (J * A * Jᴴ) = J * CFC.sqrt A * Jᴴ := by
  apply CFC.sqrt_unique
  · calc
      (J * CFC.sqrt A * Jᴴ) * (J * CFC.sqrt A * Jᴴ) =
          J * CFC.sqrt A * (Jᴴ * J) * CFC.sqrt A * Jᴴ := by
        simp only [Matrix.mul_assoc]
      _ = J * A * Jᴴ := by
        rw [hJ, Matrix.mul_one, Matrix.mul_assoc J, sqrt_mul_self hA]
  · exact ((sqrt_posSemidef A).mul_mul_conjTranspose_same J).nonneg

theorem fidelity_isometric_embedding (J : Matrix m n ℂ) (hJ : Jᴴ * J = 1)
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    fidelity (J * A * Jᴴ) (J * B * Jᴴ) = fidelity A B := by
  unfold fidelity
  rw [sqrt_isometric_embedding J hJ hB]
  have hs : (J * CFC.sqrt B * Jᴴ) * (J * A * Jᴴ) *
      (J * CFC.sqrt B * Jᴴ) = J * (CFC.sqrt B * A * CFC.sqrt B) * Jᴴ := by
    calc
      _ = J * CFC.sqrt B * (Jᴴ * J) * A * (Jᴴ * J) * CFC.sqrt B * Jᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by simp [hJ, Matrix.mul_assoc]
  rw [hs, sqrt_isometric_embedding J hJ (sandwich_posSemidef hA B)]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hJ, Matrix.one_mul]

/-- Unitary change of basis is the square-isometry special case. -/
theorem fidelity_unitary_conjugation (U : Matrix n n ℂ) (hU : Uᴴ * U = 1)
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    fidelity (U * A * Uᴴ) (U * B * Uᴴ) = fidelity A B :=
  fidelity_isometric_embedding U hU hA hB

end Cloning.MatrixFidelity
