import Cloning.MatrixFidelityContinuity
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Trace norm and positive decompositions

For a Hermitian matrix, the concrete spectral trace norm is the sum of the
absolute values of its eigenvalues. In a spectral basis, any positive
decomposition gives a termwise bound on those absolute values. This proves
the minimal-positive-decomposition estimate used for channel contraction.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix Unitary

namespace Cloning.MatrixFidelity

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Concrete trace norm of a Hermitian matrix in its eigenbasis. -/
theorem traceNorm_eq_sum_abs_eigenvalues {D : Matrix n n ℂ} (hD : D.IsHermitian) :
    matrixTraceNorm D = ∑ i, |hD.eigenvalues i| := by
  rw [← trace_abs_eq_matrixTraceNorm, CFC.abs_eq_cfc_norm D hD,
    hD.cfc_eq (fun x : ℝ ↦ ‖x‖), Matrix.IsHermitian.cfc, conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp only [Function.comp_apply, Complex.re_sum, Real.norm_eq_abs]
  apply Finset.sum_congr rfl
  intro i _
  exact RCLike.ofReal_re (K := ℂ) |hD.eigenvalues i|

/-- A positive decomposition bounds the trace norm of its Hermitian difference.
The estimate is independent of the ambient matrix dimension. -/
theorem traceNorm_sub_le_trace_add {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    matrixTraceNorm (A - B) ≤ (Matrix.trace A).re + (Matrix.trace B).re := by
  let hD : (A - B).IsHermitian := hA.isHermitian.sub hB.isHermitian
  let U := hD.eigenvectorUnitary
  let C : Matrix n n ℂ := (star U : Matrix n n ℂ) * A * (U : Matrix n n ℂ)
  let E : Matrix n n ℂ := (star U : Matrix n n ℂ) * B * (U : Matrix n n ℂ)
  have hC : C.PosSemidef := hA.conjTranspose_mul_mul_same (U : Matrix n n ℂ)
  have hE : E.PosSemidef := hB.conjTranspose_mul_mul_same (U : Matrix n n ℂ)
  have hdiag : C - E = Matrix.diagonal (fun i ↦ (hD.eigenvalues i : ℂ)) := by
    dsimp only [C, E]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    simpa only [conjStarAlgAut_star_apply, Function.comp_apply, Unitary.coe_star] using
      hD.conjStarAlgAut_star_eigenvectorUnitary
  have heig i : hD.eigenvalues i = (C i i).re - (E i i).re := by
    have h := congrArg (fun M : Matrix n n ℂ ↦ (M i i).re) hdiag
    simpa only [Matrix.sub_apply, Complex.sub_re, Matrix.diagonal_apply_eq,
      Complex.ofReal_re] using h.symm
  have htrC : Matrix.trace C = Matrix.trace A := by
    dsimp only [C]
    rw [Matrix.trace_mul_cycle,
      show (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 from
        Unitary.mul_star_self_of_mem U.property, one_mul]
  have htrE : Matrix.trace E = Matrix.trace B := by
    dsimp only [E]
    rw [Matrix.trace_mul_cycle,
      show (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 from
        Unitary.mul_star_self_of_mem U.property, one_mul]
  calc
    matrixTraceNorm (A - B) = ∑ i, |hD.eigenvalues i| :=
      traceNorm_eq_sum_abs_eigenvalues hD
    _ ≤ ∑ i, ((C i i).re + (E i i).re) := by
      apply Finset.sum_le_sum
      intro i _
      rw [heig i]
      calc
        |(C i i).re - (E i i).re| ≤ |(C i i).re| + |(E i i).re| := abs_sub _ _
        _ = (C i i).re + (E i i).re := by
          rw [abs_of_nonneg (Complex.nonneg_iff.mp (hC.diag_nonneg (i := i))).1,
            abs_of_nonneg (Complex.nonneg_iff.mp (hE.diag_nonneg (i := i))).1]
    _ = (Matrix.trace C).re + (Matrix.trace E).re := by
      simp only [Matrix.trace, Matrix.diag, Complex.re_sum, Finset.sum_add_distrib]
    _ = (Matrix.trace A).re + (Matrix.trace B).re := by rw [htrC, htrE]

/-- The positive spectral part is an actual positive matrix. -/
theorem positivePart_posSemidef (D : Matrix n n ℂ) :
    D⁺.PosSemidef := (CFC.posPart_nonneg D).posSemidef

/-- The negative spectral part is an actual positive matrix. -/
theorem negativePart_posSemidef (D : Matrix n n ℂ) :
    D⁻.PosSemidef := (CFC.negPart_nonneg D).posSemidef

/-- Exact positive-minus-negative reconstruction of a Hermitian matrix. -/
theorem positivePart_sub_negativePart {D : Matrix n n ℂ} (hD : D.IsHermitian) :
    D⁺ - D⁻ = D := CFC.posPart_sub_negPart D hD

/-- The canonical positive decomposition attains the trace-norm cost. -/
theorem trace_positivePart_add_negativePart {D : Matrix n n ℂ} (hD : D.IsHermitian) :
    (Matrix.trace D⁺).re + (Matrix.trace D⁻).re =
      matrixTraceNorm D := by
  rw [← Complex.add_re, ← Matrix.trace_add, CFC.posPart_add_negPart D hD,
    trace_abs_eq_matrixTraceNorm]

end Cloning.MatrixFidelity
