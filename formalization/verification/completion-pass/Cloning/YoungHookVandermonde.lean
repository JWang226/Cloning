import Cloning.YoungHookCount
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Fin.Rev

/-! Evaluation of the proved standard-tableau factorial determinant by the
falling-factorial Vandermonde determinant. -/

noncomputable section
open scoped BigOperators Classical
open Polynomial

namespace Cloning.YoungGeneral

theorem inverseFactorial_sub_nat (n k : ℕ) :
    inverseFactorial ((n : ℤ) - (k : ℤ)) =
      (n.descFactorial k : ℝ) * (n.factorial : ℝ)⁻¹ := by
  by_cases hkn : k ≤ n
  · rw [← Nat.cast_sub hkn, inverseFactorial_nat]
    have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hnk : ((n-k).factorial : ℝ) ≠ 0 := by exact_mod_cast (n-k).factorial_ne_zero
    have heq : ((n-k).factorial : ℝ) * (n.descFactorial k : ℝ) = n.factorial := by
      exact_mod_cast Nat.factorial_mul_descFactorial hkn
    field_simp
    nlinarith
  · rw [inverseFactorial_of_neg (by omega), Nat.descFactorial_of_lt (by omega)]
    simp

def shiftedRow {d : ℕ} (μ : Fin d → ℕ) (i : Fin d) : ℕ :=
  μ i + (d - 1 - i.val)

theorem shiftedRow_strictAnti {d : ℕ} (μ : Fin d → ℕ) (hμ : Antitone μ) :
    StrictAnti (shiftedRow μ) := by
  intro i j hij
  have h := hμ (le_of_lt hij)
  have hi := i.isLt
  have hj := j.isLt
  simp only [shiftedRow, Fin.lt_def] at *
  omega

def fallingEvaluation {d : ℕ} (v : Fin d → ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ (descPochhammer ℝ j.val).eval (v i : ℝ)

theorem fallingEvaluation_det {d : ℕ} (v : Fin d → ℕ) :
    (fallingEvaluation v).det =
      ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, ((v j : ℝ) - (v i : ℝ)) := by
  rw [← Matrix.det_vandermonde]
  exact (Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun i ↦ (v i : ℝ)) (fun i ↦ descPochhammer ℝ i.val)
    (fun i ↦ descPochhammer_natDegree ℝ i.val)
    (fun i ↦ monic_descPochhammer ℝ i.val)).symm

theorem factorialMatrix_eq_fallingEvaluation {d : ℕ} (μ : Fin d → ℕ) :
    factorialMatrix (fun i ↦ (μ i : ℤ)) =
      ((fallingEvaluation (shiftedRow μ)).transpose.submatrix Fin.revPerm
        (Equiv.refl (Fin d))) *
        Matrix.diagonal (fun j ↦ ((shiftedRow μ j).factorial : ℝ)⁻¹) := by
  ext i j
  rw [Matrix.mul_diagonal]
  simp only [Matrix.submatrix_apply, Matrix.transpose_apply, Equiv.refl_apply,
    fallingEvaluation, descPochhammer_eval_eq_descFactorial]
  rw [← inverseFactorial_sub_nat]
  unfold factorialMatrix
  congr 1
  have hi := i.isLt
  have hj := j.isLt
  simp only [shiftedRow, Fin.revPerm_apply, Fin.val_rev]
  omega

theorem abs_factorialDeterminant {d : ℕ} (μ : Fin d → ℕ) :
    |factorialDeterminant (fun i ↦ (μ i : ℤ))| =
      (∏ i : Fin d, ∏ j ∈ Finset.Ioi i,
        |((shiftedRow μ j : ℕ) : ℝ) - ((shiftedRow μ i : ℕ) : ℝ)|) *
      ∏ i, ((shiftedRow μ i).factorial : ℝ)⁻¹ := by
  rw [factorialDeterminant, factorialMatrix_eq_fallingEvaluation,
    Matrix.det_mul, abs_mul, Matrix.abs_det_submatrix_equiv_equiv,
    Matrix.det_transpose, fallingEvaluation_det, Matrix.det_diagonal]
  simp only [Finset.abs_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact abs_of_nonneg (by positivity)

/-- The exact Vandermonde/factorial dimension formula for standard tableaux.
The shifted rows are strictly decreasing even when the original partition has
equal parts. -/
theorem standardCount_eq_vandermonde {d N : ℕ} (μ : Fin d → ℕ)
    (hμ : Antitone μ) (hN : ∑ i, μ i = N) :
    (standardCount N μ : ℝ) =
      (N.factorial : ℝ) *
        (∏ i : Fin d, ∏ j ∈ Finset.Ioi i,
          (((shiftedRow μ i : ℕ) : ℝ) - ((shiftedRow μ j : ℕ) : ℝ))) *
        ∏ i, ((shiftedRow μ i).factorial : ℝ)⁻¹ := by
  have h := congrArg abs (standardCount_eq_factorial_determinant μ hμ hN)
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _),
    abs_factorialDeterminant] at h
  rw [h, mul_assoc]
  congr 1
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j hj
  rw [abs_sub_comm, abs_of_nonneg]
  exact sub_nonneg.mpr (by exact_mod_cast (shiftedRow_strictAnti μ hμ (Finset.mem_Ioi.mp hj)).le)

end Cloning.YoungGeneral
