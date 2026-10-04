import Cloning.MatrixFidelity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Positive trace pairings and inverse square-root order

All assertions concern actual finite complex matrices. Positivity of a
trace pairing follows from positivity of the square-root sandwich. Inverse
antitonicity follows from the C*-algebra inverse-order theorem.
-/

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace Cloning.MatrixFidelity

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Positive matrices have a nonnegative real trace pairing even when they
do not commute. -/
theorem trace_mul_re_nonneg {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A * B)).re := by
  have h := trace_re_nonneg (sandwich_posSemidef hB A)
  rw [Matrix.trace_mul_cycle, sqrt_mul_self hA] at h
  exact h

/-- Positive trace pairings are real. -/
theorem trace_mul_im_zero {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.trace (A * B)).im = 0 := by
  have h := trace_im_zero (sandwich_posSemidef hB A)
  rw [Matrix.trace_mul_cycle, sqrt_mul_self hA] at h
  exact h

/-- Pairing against a positive matrix preserves Loewner order. -/
theorem trace_mul_re_mono_right {A B C : Matrix n n ℂ}
    (hA : A.PosSemidef) (hBC : B ≤ C) :
    (Matrix.trace (A * B)).re ≤ (Matrix.trace (A * C)).re := by
  have h := trace_mul_re_nonneg hA (show (C - B).PosSemidef from hBC)
  simpa only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, sub_nonneg] using h

/-- The trace pairing is also monotone in the first argument. -/
theorem trace_mul_re_mono_left {A B C : Matrix n n ℂ}
    (hA : A.PosSemidef) (hBC : B ≤ C) :
    (Matrix.trace (B * A)).re ≤ (Matrix.trace (C * A)).re := by
  rw [Matrix.trace_mul_comm B A, Matrix.trace_mul_comm C A]
  exact trace_mul_re_mono_right hA hBC

/-- Inversion reverses the Loewner order on positive definite matrices.
The inverses here are the usual matrix nonsingular inverses. -/
theorem matrix_inv_antitone {X Y : Matrix n n ℂ}
    (hX : X.PosDef) (hY : Y.PosDef) (hXY : X ≤ Y) : Y⁻¹ ≤ X⁻¹ := by
  letI : CStarAlgebra (Matrix n n ℂ) := {}
  obtain ⟨u, rfl⟩ := hX.isUnit
  obtain ⟨v, rfl⟩ := hY.isUnit
  have h := CStarAlgebra.inv_le_inv (a := u) (b := v) hX.posSemidef.nonneg hXY
  simpa only [Matrix.coe_units_inv] using h

/-- Inverse square roots reverse the Loewner order on positive definite matrices. -/
theorem sqrt_inv_antitone {X Y : Matrix n n ℂ}
    (hX : X.PosDef) (hY : Y.PosDef) (hXY : X ≤ Y) :
    (CFC.sqrt Y)⁻¹ ≤ (CFC.sqrt X)⁻¹ := by
  letI : CStarAlgebra (Matrix n n ℂ) := {}
  exact matrix_inv_antitone
    (Matrix.isStrictlyPositive_iff_posDef.mp hX.isStrictlyPositive.sqrt)
    (Matrix.isStrictlyPositive_iff_posDef.mp hY.isStrictlyPositive.sqrt)
    (CFC.sqrt_le_sqrt X Y hXY)

/-- The trace-weighted form needed for square-root trace subadditivity. -/
theorem trace_mul_sqrt_inv_antitone {A X Y : Matrix n n ℂ}
    (hA : A.PosSemidef) (hX : X.PosDef) (hY : Y.PosDef) (hXY : X ≤ Y) :
    (Matrix.trace (A * (CFC.sqrt Y)⁻¹)).re ≤
      (Matrix.trace (A * (CFC.sqrt X)⁻¹)).re :=
  trace_mul_re_mono_right hA (sqrt_inv_antitone hX hY hXY)

end Cloning.MatrixFidelity
