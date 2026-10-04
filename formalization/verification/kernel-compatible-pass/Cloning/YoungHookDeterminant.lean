import Cloning.YoungBranchingStandard
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The factorial determinant and its predecessor recurrence

The reciprocal factorial is extended by zero to negative integers.  Its exact
one-step recurrence proves the determinant predecessor identity, including
boundary terms.  This is the algebraic input to the standard-tableau dimension
formula; it does not assume a hook formula or a representation dimension.
-/

noncomputable section
open scoped BigOperators Classical

namespace Cloning.YoungGeneral

def inverseFactorial (z : ℤ) : ℝ :=
  if 0 ≤ z then ((z.toNat.factorial : ℕ) : ℝ)⁻¹ else 0

@[simp] theorem inverseFactorial_nat (n : ℕ) :
    inverseFactorial n = (n.factorial : ℝ)⁻¹ := by
  simp [inverseFactorial]

theorem inverseFactorial_of_neg {z : ℤ} (hz : z < 0) :
    inverseFactorial z = 0 := by
  simp [inverseFactorial, not_le.mpr hz]

theorem mul_inverseFactorial (z : ℤ) :
    (z : ℝ) * inverseFactorial z = inverseFactorial (z - 1) := by
  by_cases hz : 0 < z
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hz)
    cases n with
    | zero => simp at hz
    | succ n =>
      rw [show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by omega]
      change ((n + 1 : ℕ) : ℝ) * inverseFactorial ((n + 1 : ℕ) : ℤ) =
        inverseFactorial (n : ℤ)
      rw [inverseFactorial_nat, inverseFactorial_nat]
      simp only [Nat.factorial_succ, Nat.cast_add,
        Nat.cast_one, Nat.cast_mul]
      have h : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
  · by_cases hz0 : z = 0
    · subst z
      norm_num [inverseFactorial]
    · rw [inverseFactorial_of_neg (by omega),
        inverseFactorial_of_neg (by omega)]
      simp

/-- Columns are indexed by rows of the partition.  Transposing this matrix
gives the usual `1 / (a_i - i + j)!` convention. -/
def factorialMatrix {d : ℕ} (a : Fin d → ℤ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ inverseFactorial (a j - (j.val : ℤ) + (i.val : ℤ))

def factorialDeterminant {d : ℕ} (a : Fin d → ℤ) : ℝ :=
  (factorialMatrix a).det

def lowerIntegerRow {d : ℕ} (a : Fin d → ℤ) (i : Fin d) : Fin d → ℤ :=
  fun j ↦ a j - if j = i then 1 else 0

theorem factorialMatrix_lower_product {d : ℕ} (a : Fin d → ℤ)
    (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    (∏ j, factorialMatrix (lowerIntegerRow a i) (σ j) j) =
      ((a i - (i.val : ℤ) + ((σ i).val : ℤ) : ℤ) : ℝ) *
        ∏ j, factorialMatrix a (σ j) j := by
  have heq : (fun j ↦ factorialMatrix (lowerIntegerRow a i) (σ j) j) =
      Function.update (fun j ↦ factorialMatrix a (σ j) j) i
        (inverseFactorial (a i - (i.val : ℤ) + ((σ i).val : ℤ) - 1)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [factorialMatrix, lowerIntegerRow, ite_true, Function.update_self]
      congr 1
      ring
    · simp [factorialMatrix, lowerIntegerRow, hji]
  rw [heq, Finset.prod_update_of_mem (Finset.mem_univ i),
    ← mul_inverseFactorial]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase, factorialMatrix, mul_assoc]

/-- The exact predecessor sum, valid for every integer vector, with no
partition or nonnegativity assumptions. -/
theorem factorialDeterminant_predecessors {d : ℕ} (a : Fin d → ℤ) :
    (∑ i, factorialDeterminant (lowerIntegerRow a i)) =
      (∑ i, (a i : ℝ)) * factorialDeterminant a := by
  simp only [factorialDeterminant, Matrix.det_apply']
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp_rw [factorialMatrix_lower_product]
  have hs : (∑ i, ((a i - (i.val : ℤ) + ((σ i).val : ℤ) : ℤ) : ℝ)) =
      ∑ i, (a i : ℝ) := by
    simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [Equiv.sum_comp σ (fun i : Fin d ↦ (i.val : ℝ))]
    ring
  calc
    _ = (Equiv.Perm.sign σ : ℝ) *
        ((∑ i, ((a i - (i.val : ℤ) + ((σ i).val : ℤ) : ℤ) : ℝ)) *
          ∏ j, factorialMatrix a (σ j) j) := by
      rw [Finset.sum_mul, Finset.mul_sum]
    _ = _ := by rw [hs]; ring

theorem factorialDeterminant_zero_shape (d : ℕ) :
    factorialDeterminant (fun _ : Fin d ↦ (0 : ℤ)) = 1 := by
  unfold factorialDeterminant
  rw [Matrix.det_of_lowerTriangular]
  · simp [factorialMatrix, inverseFactorial]
  · intro i j hij
    apply inverseFactorial_of_neg
    change j.val > i.val at hij
    dsimp only
    omega

theorem factorialDeterminant_lower_equal_next {d : ℕ} (μ : Fin d → ℕ)
    (i j : Fin d) (hij : j.val = i.val + 1) (hμ : μ i = μ j) :
    factorialDeterminant (lowerIntegerRow (fun k ↦ (μ k : ℤ)) i) = 0 := by
  apply Matrix.det_zero_of_column_eq (show i ≠ j by intro h; subst j; omega)
  intro k
  have hji : j ≠ i := by intro h; subst j; omega
  simp only [factorialMatrix, lowerIntegerRow, ite_true, if_neg hji, sub_zero]
  congr 1
  rw [hμ]
  omega

theorem factorialDeterminant_lower_zero {d : ℕ} (μ : Fin d → ℕ)
    (hμ : Antitone μ) (i : Fin d) (hi : μ i = 0) :
    factorialDeterminant (lowerIntegerRow (fun k ↦ (μ k : ℤ)) i) = 0 := by
  by_cases hn : i.val + 1 < d
  · let j : Fin d := ⟨i.val + 1, hn⟩
    apply factorialDeterminant_lower_equal_next μ i j rfl
    have hj := hμ (show i ≤ j by simp [j, Fin.le_def])
    omega
  · apply Matrix.det_eq_zero_of_column_eq_zero i
    intro k
    apply inverseFactorial_of_neg
    simp only [lowerIntegerRow, ite_true, hi, Nat.cast_zero]
    have hk := k.isLt
    omega

theorem removeBox_antitone_of_strict {d : ℕ} (μ : Fin d → ℕ)
    (hμ : Antitone μ) (i : Fin d) (hi : ∀ j, i < j → μ j < μ i) :
    Antitone (removeBox μ i) := by
  intro a b hab
  have h := hμ hab
  by_cases hai : a = i
  · subst a
    by_cases hbi : b = i
    · subst b; exact le_rfl
    · have hib : i < b := lt_of_le_of_ne hab (Ne.symm hbi)
      have hstrict := hi b hib
      simp only [removeBox, if_neg hbi, ite_true]
      omega
  · simp only [removeBox, if_neg hai]
    split_ifs <;> omega

theorem factorialDeterminant_lower_not_antitone {d : ℕ} (μ : Fin d → ℕ)
    (hμ : Antitone μ) (i : Fin d) (hbad : ¬ Antitone (removeBox μ i)) :
    factorialDeterminant (lowerIntegerRow (fun k ↦ (μ k : ℤ)) i) = 0 := by
  have hex : ∃ j, i < j ∧ μ j = μ i := by
    by_contra! hn
    apply hbad
    apply removeBox_antitone_of_strict μ hμ i
    intro j hij
    exact lt_of_le_of_ne (hμ (le_of_lt hij)) (hn j hij)
  obtain ⟨j, hij, heq⟩ := hex
  have hnext : i.val + 1 < d := by have := j.isLt; simp only [Fin.lt_def] at hij; omega
  let k : Fin d := ⟨i.val + 1, hnext⟩
  apply factorialDeterminant_lower_equal_next μ i k rfl
  have hik := hμ (show i ≤ k by simp [k, Fin.le_def])
  have hkj := hμ (show k ≤ j by simp only [Fin.le_def, k]; simp only [Fin.lt_def] at hij; omega)
  omega

theorem lowerIntegerRow_removeBox {d : ℕ} (μ : Fin d → ℕ)
    (i : Fin d) (hi : 0 < μ i) :
    lowerIntegerRow (fun k ↦ (μ k : ℤ)) i = fun k ↦ (removeBox μ i k : ℤ) := by
  funext k
  simp only [lowerIntegerRow, removeBox]
  by_cases hki : k = i
  · subst k
    simp only [ite_true]
    omega
  · simp [hki]

end Cloning.YoungGeneral
