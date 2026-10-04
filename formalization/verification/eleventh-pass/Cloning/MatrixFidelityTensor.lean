import Cloning.MatrixFidelity

/-!
# Tensor products for concrete finite-dimensional root fidelity

The square-root and fidelity identities below apply to positive semidefinite
complex matrices; no abstract fidelity axioms are assumed.
-/

noncomputable section

open scoped MatrixOrder ComplexOrder Kronecker

namespace Cloning.MatrixFidelity

set_option backward.isDefEq.respectTransparency false

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The positive square root preserves Kronecker products. -/
theorem sqrt_kronecker {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    CFC.sqrt (A ⊗ₖ B) = CFC.sqrt A ⊗ₖ CFC.sqrt B := by
  apply CFC.sqrt_unique
  · rw [← Matrix.mul_kronecker_mul, sqrt_mul_self hA, sqrt_mul_self hB]
  · exact ((sqrt_posSemidef A).kronecker (sqrt_posSemidef B)).nonneg

/-- Root Uhlmann fidelity is multiplicative under tensor products. -/
theorem fidelity_kronecker {A B : Matrix m m ℂ} {C D : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hC : C.PosSemidef) (hD : D.PosSemidef) :
    fidelity (A ⊗ₖ C) (B ⊗ₖ D) = fidelity A B * fidelity C D := by
  have hAB := sandwich_posSemidef hA B
  have hCD := sandwich_posSemidef hC D
  have him : (Matrix.trace (CFC.sqrt (CFC.sqrt B * A * CFC.sqrt B))).im = 0 :=
    trace_im_zero (sqrt_posSemidef _)
  unfold fidelity
  rw [sqrt_kronecker hB hD, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    sqrt_kronecker hAB hCD, Matrix.trace_kronecker, Complex.mul_re, him]
  simp

/-- Tensoring both inputs with the same normalized ancilla preserves fidelity. -/
theorem fidelity_common_ancilla {A B : Matrix m m ℂ} {T : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hT : T.PosSemidef)
    (htrace : (Matrix.trace T).re = 1) :
    fidelity (A ⊗ₖ T) (B ⊗ₖ T) = fidelity A B := by
  rw [fidelity_kronecker hA hB hT hT, fidelity_self hT, htrace, mul_one]

/-- The same cancellation when the ancilla is placed first. -/
theorem fidelity_common_ancilla_left {A B : Matrix m m ℂ} {T : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hT : T.PosSemidef)
    (htrace : (Matrix.trace T).re = 1) :
    fidelity (T ⊗ₖ A) (T ⊗ₖ B) = fidelity A B := by
  rw [fidelity_kronecker hT hT hA hB, fidelity_self hT, htrace, one_mul]

end Cloning.MatrixFidelity
