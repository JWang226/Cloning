import Cloning.TensorFundamentalBranchingSlices
import Cloning.TensorWedgeHighest
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The literal last-slot contraction of an antisymmetric column. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

/-- Coefficients of the actual antisymmetrization are literal determinants. -/
theorem wedgeTensor_coefficient_det (v : Fin n → Register (Fin d)) (w : Fin n → Fin d) :
    wedgeTensor n v w = Matrix.det (fun i j => v i (w j)) := by
  simp only [wedgeTensor_apply, Matrix.det_apply, lp.coeFn_sum, Finset.sum_apply,
    Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, lp.coeFn_smul, Pi.smul_apply,
    tensorVector_apply]

/-- Contracting the highest letter from the last slot of an antisymmetric
column leaves exactly the shorter unnormalized antisymmetric column. -/
theorem lastSlice_columnTensorRaw {h d : ℕ} (hd : h + 1 ≤ d) :
    lastSlice (⟨h, by omega⟩ : Fin d) (columnTensorRaw hd) =
      columnTensorRaw (Nat.le_trans (Nat.le_succ h) hd) := by
  ext w
  simp only [lastSlice_apply, columnTensorRaw, wedgeTensor_coefficient_det]
  rw [Matrix.det_succ_column _ (Fin.last h)]
  rw [Finset.sum_eq_single (Fin.last h)]
  · have hdiag : registerBasis (Fin d) (columnLetters hd (Fin.last h))
        ((Fin.snoc w (⟨h, by omega⟩ : Fin d) : Fin (h + 1) → Fin d) (Fin.last h)) = 1 := by
      rw [Fin.snoc_last]
      simp [registerBasis_apply, columnLetters, lp.single_apply]
    rw [hdiag, mul_one]
    have hsign : (-1 : ℂ) ^ ((Fin.last h : Fin (h + 1)).val + (Fin.last h : Fin (h + 1)).val) = 1 := by
      simp [← two_mul, pow_mul]
    rw [hsign, one_mul]
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, Fin.succAbove_last, Fin.snoc_castSucc]
    congr 2
  · intro i _ hi
    have hne : columnLetters hd i ≠ (⟨h, by omega⟩ : Fin d) := by
      intro he
      apply hi
      apply Fin.ext
      simpa only [columnLetters_val, Fin.val_last] using congrArg (fun a : Fin d => a.val) he
    simp [Fin.snoc_last, registerBasis_apply, lp.single_apply, Ne.symm hne]
  · simp

/-- Last-slot contraction respects a tensor factor lying wholly to its left. -/
theorem lastSlice_tensorJoin_last {n h d : ℕ} (r : Fin d)
    (x : TensorRegister n (Fin d)) (y : TensorRegister (h + 1) (Fin d)) :
    lastSlice (n := n + h) r (tensorJoin (n := n) (m := h + 1) x y) =
      tensorJoin x (lastSlice (n := h) r y) := by
  ext w
  simp only [lastSlice_apply, tensorJoin_apply]
  apply congrArg₂ (· * ·)
  · apply congrArg (fun z : Fin n → Fin d => x z)
    funext i
    exact Fin.snoc_castAdd (α := fun _ => Fin d) w r i
  · exact congrArg (fun z : Fin (h + 1) → Fin d => y z) (Fin.snoc_comp_natAdd w r)

end Cloning.TensorLie
