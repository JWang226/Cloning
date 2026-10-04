import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order

/-!
# Concrete finite-dimensional root fidelity

The trace norm is defined by its spectral formula `Tr sqrt(X* X)`.
Root fidelity uses the equivalent positive sandwich formula. All objects here
are actual complex matrices; no fidelity laws are postulated.
-/

open scoped BigOperators MatrixOrder ComplexOrder
open Matrix

noncomputable section

namespace Cloning.MatrixFidelity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Spectral definition of the finite-dimensional trace norm. -/
def matrixTraceNorm (X : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (CFC.sqrt (Xᴴ * X))).re

/-- Root fidelity, with the second positive matrix in the sandwich. -/
def fidelity (A B : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (CFC.sqrt (CFC.sqrt B * A * CFC.sqrt B))).re

theorem sqrt_posSemidef (A : Matrix n n ℂ) : (CFC.sqrt A).PosSemidef :=
  (CFC.sqrt_nonneg A).posSemidef

theorem sqrt_mul_self {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    CFC.sqrt A * CFC.sqrt A = A :=
  CFC.sqrt_mul_sqrt_self A hA.nonneg

theorem sqrt_conjTranspose (A : Matrix n n ℂ) :
    (CFC.sqrt A)ᴴ = CFC.sqrt A :=
  (sqrt_posSemidef A).isHermitian

omit [DecidableEq n] in
theorem trace_re_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    0 ≤ (Matrix.trace A).re :=
  hA.trace_nonneg.1

omit [DecidableEq n] in
theorem trace_im_zero {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (Matrix.trace A).im = 0 :=
  hA.trace_nonneg.2.symm

theorem sandwich_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (B : Matrix n n ℂ) : (CFC.sqrt B * A * CFC.sqrt B).PosSemidef := by
  simpa only [sqrt_conjTranspose] using
    hA.conjTranspose_mul_mul_same (CFC.sqrt B)

theorem fidelity_nonneg (A B : Matrix n n ℂ) : 0 ≤ fidelity A B :=
  trace_re_nonneg (sqrt_posSemidef _)

theorem matrixTraceNorm_nonneg (X : Matrix n n ℂ) : 0 ≤ matrixTraceNorm X :=
  trace_re_nonneg (sqrt_posSemidef _)

/-- The trace norm of a positive matrix is its trace. -/
theorem matrixTraceNorm_of_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    matrixTraceNorm A = (Matrix.trace A).re := by
  unfold matrixTraceNorm
  rw [hA.isHermitian.eq, ← sq, CFC.sqrt_sq A hA.nonneg]

/-- The sandwich and square-root-product definitions agree for positive matrices. -/
theorem fidelity_eq_traceNorm {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (_hB : B.PosSemidef) :
    fidelity A B = matrixTraceNorm (CFC.sqrt A * CFC.sqrt B) := by
  unfold fidelity matrixTraceNorm
  congr 3
  rw [Matrix.conjTranspose_mul, sqrt_conjTranspose, sqrt_conjTranspose]
  rw [← Matrix.mul_assoc (CFC.sqrt B * CFC.sqrt A),
    Matrix.mul_assoc (CFC.sqrt B) (CFC.sqrt A), sqrt_mul_self hA]

theorem fidelity_self {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    fidelity A A = (Matrix.trace A).re := by
  unfold fidelity
  have hs : CFC.sqrt A * A * CFC.sqrt A = A * A := by
    calc
      CFC.sqrt A * A * CFC.sqrt A =
          CFC.sqrt A * (CFC.sqrt A * CFC.sqrt A) * CFC.sqrt A := by
        rw [sqrt_mul_self hA]
      _ = (CFC.sqrt A * CFC.sqrt A) * (CFC.sqrt A * CFC.sqrt A) := by
        simp only [Matrix.mul_assoc]
      _ = A * A := by rw [sqrt_mul_self hA]
  rw [hs, ← sq, CFC.sqrt_sq A hA.nonneg]

theorem fidelity_zero_left (B : Matrix n n ℂ) : fidelity 0 B = 0 := by
  simp [fidelity]

theorem fidelity_zero_right (A : Matrix n n ℂ) : fidelity A 0 = 0 := by
  simp [fidelity]

/-- A finite-dimensional density matrix. -/
structure State (n : Type*) [Fintype n] where
  matrix : Matrix n n ℂ
  positive : matrix.PosSemidef
  trace_one : Matrix.trace matrix = 1

theorem state_fidelity_self (ρ : State n) : fidelity ρ.matrix ρ.matrix = 1 := by
  rw [fidelity_self ρ.positive, ρ.trace_one]
  rfl

end Cloning.MatrixFidelity
