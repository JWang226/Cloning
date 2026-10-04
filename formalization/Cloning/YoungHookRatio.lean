import Cloning.YoungHookVandermonde
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-! The standard-tableau count as a multinomial count times a finite product
of pair ratios.  This exact form separates the local-limit correction from
the multinomial Gaussian approximation. -/
noncomputable section
open scoped BigOperators Classical

namespace Cloning.YoungGeneral

theorem prod_row_offsets {d : ℕ} (i : Fin d) (m : ℕ) :
    (∏ j ∈ Finset.Ioi i, (m + (j.val - i.val))) =
      (m + 1).ascFactorial (d - 1 - i.val) := by
  classical
  calc
    _ = ∏ k : Fin (d - 1 - i.val), (m + 1 + k.val) := by
      apply Finset.prod_bij (fun j hj ↦
        (⟨j.val - i.val - 1, by
          have := j.isLt
          have := Finset.mem_Ioi.mp hj
          simp only [Fin.lt_def] at *
          omega⟩ : Fin (d - 1 - i.val)))
      · intro j hj; exact Finset.mem_univ _
      · intro a ha b hb heq
        have ha' := Finset.mem_Ioi.mp ha
        have hb' := Finset.mem_Ioi.mp hb
        have heq' := congrArg Fin.val heq
        apply Fin.ext
        simp only [Fin.lt_def] at *
        omega
      · intro k _
        have hk := k.isLt
        let j : Fin d := ⟨i.val + 1 + k.val, by omega⟩
        have hj : j ∈ Finset.Ioi i := by simp only [Finset.mem_Ioi, Fin.lt_def, j]; omega
        refine ⟨j, hj, ?_⟩
        apply Fin.ext
        dsimp [j]
        omega
      · intro j hj
        have := Finset.mem_Ioi.mp hj
        simp only [Fin.lt_def] at this
        dsimp
        omega
    _ = _ := by rw [Fin.prod_univ_eq_prod_range, Nat.ascFactorial_eq_prod_range]

theorem factorial_shiftedRow {d : ℕ} (μ : Fin d → ℕ) (i : Fin d) :
    (μ i).factorial * (∏ j ∈ Finset.Ioi i, (μ i + (j.val - i.val))) =
      (shiftedRow μ i).factorial := by
  rw [prod_row_offsets]
  exact Nat.factorial_mul_ascFactorial _ _

def tableauCorrection {d : ℕ} (μ : Fin d → ℕ) : ℝ :=
  ∏ i : Fin d, ∏ j ∈ Finset.Ioi i,
    (((shiftedRow μ i : ℕ) : ℝ) - ((shiftedRow μ j : ℕ) : ℝ)) /
      ((μ i : ℝ) + (j.val - i.val : ℕ))

theorem standardCount_eq_multinomial_correction {d N : ℕ} (μ : Fin d → ℕ)
    (hμ : Antitone μ) (hN : ∑ i, μ i = N) :
    (standardCount N μ : ℝ) =
      (N.factorial : ℝ) * (∏ i, ((μ i).factorial : ℝ)⁻¹) * tableauCorrection μ := by
  rw [standardCount_eq_vandermonde μ hμ hN]
  have hi (i : Fin d) : ((shiftedRow μ i).factorial : ℝ)⁻¹ =
      ((μ i).factorial : ℝ)⁻¹ *
        ∏ j ∈ Finset.Ioi i, ((μ i : ℝ) + (j.val - i.val : ℕ))⁻¹ := by
    have h : ((μ i).factorial : ℝ) *
        (∏ j ∈ Finset.Ioi i, ((μ i : ℝ) + (j.val - i.val : ℕ))) =
          (shiftedRow μ i).factorial := by
      exact_mod_cast factorial_shiftedRow μ i
    rw [← h, mul_inv_rev, Finset.prod_inv_distrib]
    ring
  simp_rw [hi]
  simp only [tableauCorrection, div_eq_mul_inv, Finset.prod_mul_distrib]
  ring

theorem shiftedRow_sub_real {d : ℕ} (μ : Fin d → ℕ) (i j : Fin d) :
    ((shiftedRow μ i : ℕ) : ℝ) - ((shiftedRow μ j : ℕ) : ℝ) =
      (μ i : ℝ) - (μ j : ℝ) + (j.val : ℝ) - (i.val : ℝ) := by
  have hi : i.val ≤ d - 1 := by have := i.isLt; omega
  have hj : j.val ≤ d - 1 := by have := j.isLt; omega
  simp only [shiftedRow, Nat.cast_add, Nat.cast_sub hi, Nat.cast_sub hj]
  ring

theorem tableauCorrection_eq_pair_ratios {d : ℕ} (μ : Fin d → ℕ) :
    tableauCorrection μ =
      ∏ i : Fin d, ∏ j ∈ Finset.Ioi i,
        (((μ i : ℝ) - (μ j : ℝ) + (j.val : ℝ) - (i.val : ℝ)) /
          ((μ i : ℝ) + (j.val : ℝ) - (i.val : ℝ))) := by
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j hj
  have hij : i.val ≤ j.val := Fin.le_def.mp (le_of_lt (Finset.mem_Ioi.mp hj))
  rw [shiftedRow_sub_real, Nat.cast_sub hij]
  ring

end Cloning.YoungGeneral
