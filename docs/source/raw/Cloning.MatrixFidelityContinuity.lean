import Cloning.MatrixFidelityDeletion
import Cloning.MatrixFidelitySymmetry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Tactic.Linarith

/-!
# Dimension-independent continuity of concrete matrix root fidelity

For positive matrices, changing the first argument by trace norm `ε` changes
root fidelity by at most `sqrt (ε * trace T)`. The proof is explicit: the
operator absolute value of the difference supplies a common positive error
majorant; matrix fidelity monotonicity, subadditivity, and the trace-product
bound control both signs of the difference.
-/

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder

namespace Cloning.MatrixFidelity

set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A Hermitian matrix is bounded above by its operator absolute value. -/
theorem hermitian_le_abs {D : Matrix n n ℂ} (hD : D.IsHermitian) :
    D ≤ CFC.abs D := by
  apply sub_nonneg.mp
  rw [CFC.abs_sub_self D hD, two_smul]
  exact add_nonneg (CFC.negPart_nonneg D) (CFC.negPart_nonneg D)

/-- The absolute value also bounds the negative of a Hermitian matrix. -/
theorem neg_hermitian_le_abs {D : Matrix n n ℂ} (hD : D.IsHermitian) :
    -D ≤ CFC.abs D := by
  simpa only [CFC.abs_neg] using hermitian_le_abs hD.neg

/-- The spectral trace-norm definition is the trace of the operator absolute value. -/
theorem trace_abs_eq_matrixTraceNorm (D : Matrix n n ℂ) :
    (Matrix.trace (CFC.abs D)).re = matrixTraceNorm D := rfl

/-- Both positive matrices lie below the other plus the same positive
absolute-difference error matrix. -/
theorem abs_difference_majorizes {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A ≤ B + CFC.abs (A - B) ∧ B ≤ A + CFC.abs (A - B) := by
  have hD : (A - B).IsHermitian := hA.isHermitian.sub hB.isHermitian
  constructor
  · calc
      A ≤ CFC.abs (A - B) + B := sub_le_iff_le_add.mp (hermitian_le_abs hD)
      _ = B + CFC.abs (A - B) := add_comm _ _
  · have hneg : B - A ≤ CFC.abs (A - B) := by
      simpa only [neg_sub] using neg_hermitian_le_abs hD
    calc
      B ≤ CFC.abs (A - B) + A := sub_le_iff_le_add.mp hneg
      _ = A + CFC.abs (A - B) := add_comm _ _

/-- Dimension-independent trace-norm continuity in the first fidelity argument.
No normalization, full rank, or abstract continuity law is assumed. -/
theorem fidelity_continuity_left {A B T : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hT : T.PosSemidef) :
    |fidelity A T - fidelity B T| ≤
      Real.sqrt (matrixTraceNorm (A - B) * (Matrix.trace T).re) := by
  have hH : (CFC.abs (A - B)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg (A - B))
  have hmajor := abs_difference_majorizes hA hB
  have hmonoA := fidelity_mono_left hmajor.1 T
  have hmonoB := fidelity_mono_left hmajor.2 T
  have haddA := fidelity_add_le hA hH T
  have haddB := fidelity_add_le hB hH T
  have hbound := fidelity_le_sqrt_trace_mul_trace hH hT
  rw [trace_abs_eq_matrixTraceNorm] at hbound
  apply abs_sub_le_iff.mpr
  constructor <;> linarith

/-- For a subnormalized target, the continuity constant depends only on
the trace-norm perturbation. -/
theorem fidelity_continuity_left_trace_le_one {A B T : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hT : T.PosSemidef)
    (htrace : (Matrix.trace T).re ≤ 1) :
    |fidelity A T - fidelity B T| ≤ Real.sqrt (matrixTraceNorm (A - B)) := by
  apply (fidelity_continuity_left hA hB hT).trans
  apply Real.sqrt_le_sqrt
  simpa only [mul_one] using mul_le_mul_of_nonneg_left htrace
    (matrixTraceNorm_nonneg (A - B))

/-- A numerical trace-norm bound gives the uniform continuity estimate
used in finite-dimensional approximation arguments. -/
theorem fidelity_continuity_left_of_traceNorm_le {A B T : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hT : T.PosSemidef)
    (htrace : (Matrix.trace T).re ≤ 1) {ε : ℝ}
    (herror : matrixTraceNorm (A - B) ≤ ε) :
    |fidelity A T - fidelity B T| ≤ Real.sqrt ε :=
  (fidelity_continuity_left_trace_le_one hA hB hT htrace).trans
    (Real.sqrt_le_sqrt herror)

/-- The same trace-norm continuity estimate holds in the second argument. -/
theorem fidelity_continuity_right {A B T : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hT : T.PosSemidef) :
    |fidelity T A - fidelity T B| ≤
      Real.sqrt (matrixTraceNorm (A - B) * (Matrix.trace T).re) := by
  rw [fidelity_symm hT hA, fidelity_symm hT hB]
  exact fidelity_continuity_left hA hB hT

/-- Full two-argument continuity for arbitrary positive matrices, including
singular matrices. The two trace factors record the chosen intermediate pair. -/
theorem fidelity_continuity {A B T S : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hT : T.PosSemidef) (hS : S.PosSemidef) :
    |fidelity A T - fidelity B S| ≤
      Real.sqrt (matrixTraceNorm (A - B) * (Matrix.trace T).re) +
        Real.sqrt (matrixTraceNorm (T - S) * (Matrix.trace B).re) := by
  apply (abs_sub_le (fidelity A T) (fidelity B T) (fidelity B S)).trans
  exact add_le_add (fidelity_continuity_left hA hB hT)
    (fidelity_continuity_right hT hS hB)

/-- For subnormalized positive matrices, the two perturbation trace norms
alone control the change in fidelity. -/
theorem fidelity_continuity_trace_le_one {A B T S : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hT : T.PosSemidef) (hS : S.PosSemidef)
    (htraceT : (Matrix.trace T).re ≤ 1) (htraceB : (Matrix.trace B).re ≤ 1) :
    |fidelity A T - fidelity B S| ≤
      Real.sqrt (matrixTraceNorm (A - B)) + Real.sqrt (matrixTraceNorm (T - S)) := by
  apply (abs_sub_le (fidelity A T) (fidelity B T) (fidelity B S)).trans
  apply add_le_add (fidelity_continuity_left_trace_le_one hA hB hT htraceT)
  rw [fidelity_symm hB hT, fidelity_symm hB hS]
  exact fidelity_continuity_left_trace_le_one hT hS hB htraceB

/-- Numerical perturbation bounds yield the usual sum-of-square-roots modulus. -/
theorem fidelity_continuity_of_traceNorm_le {A B T S : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hT : T.PosSemidef) (hS : S.PosSemidef)
    (htraceT : (Matrix.trace T).re ≤ 1) (htraceB : (Matrix.trace B).re ≤ 1)
    {ε η : ℝ} (hleft : matrixTraceNorm (A - B) ≤ ε)
    (hright : matrixTraceNorm (T - S) ≤ η) :
    |fidelity A T - fidelity B S| ≤ Real.sqrt ε + Real.sqrt η := by
  exact (fidelity_continuity_trace_le_one hA hB hT hS htraceT htraceB).trans
    (add_le_add (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright))

end Cloning.MatrixFidelity
