import Cloning.YoungHookDeterminant

/-! The exact factorial determinant formula for the literal standard-word
count.  Its proof is induction on the proved Young-lattice predecessor
recurrence; no representation dimension formula is an input. -/

noncomputable section
open scoped BigOperators Classical

namespace Cloning.YoungGeneral

theorem standardCount_eq_zero_of_not_antitone {d N : ℕ} (μ : Fin d → ℕ)
    (hμ : ¬ Antitone μ) : standardCount N μ = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hw' := (Finset.mem_filter.mp hw).2
  exact hμ (hw'.2 ▸ standardWord_rows_antitone w hw'.1)

@[simp] theorem standardCount_empty (d : ℕ) :
    standardCount 0 (fun _ : Fin d ↦ 0) = 1 := by
  have hall : ∀ w : Fin 0 → Fin d,
      IsStandardWord w ∧ rowCount w = fun _ ↦ 0 := by
    intro w
    constructor
    · intro n i j hij
      simp
    · funext i
      simp [rowCount]
  simp [standardCount, hall]

theorem removeBox_sum {d : ℕ} (μ : Fin d → ℕ) (i : Fin d) (hi : 0 < μ i) :
    (∑ j, removeBox μ i j) + 1 = ∑ j, μ j := by
  have h := addBox_sum (removeBox μ i) i
  rw [(addBox_eq_iff (removeBox μ i) μ i).mpr ⟨hi, rfl⟩] at h
  exact h.symm

/-- Frobenius' factorial determinant, for the actual finite standard tableaux.
The matrix convention is transposed, which leaves its determinant unchanged. -/
theorem standardCount_eq_factorial_determinant {d N : ℕ} (μ : Fin d → ℕ)
    (hμ : Antitone μ) (hN : ∑ i, μ i = N) :
    (standardCount N μ : ℝ) = (N.factorial : ℝ) *
      factorialDeterminant (fun i ↦ (μ i : ℤ)) := by
  induction N generalizing μ with
  | zero =>
    have hz : μ = fun _ ↦ 0 := by
      funext i
      have hle : μ i ≤ ∑ j, μ j := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (μ j))
        (Finset.mem_univ i)
      omega
    subst μ
    simp [factorialDeterminant_zero_shape]
  | succ N ih =>
    rw [standardCount_succ, if_pos hμ, Nat.cast_sum]
    have hterm (i : Fin d) :
        ((if 0 < μ i then standardCount N (removeBox μ i) else 0 : ℕ) : ℝ) =
          (N.factorial : ℝ) *
            factorialDeterminant (lowerIntegerRow (fun j ↦ (μ j : ℤ)) i) := by
      by_cases hi : 0 < μ i
      · rw [if_pos hi]
        by_cases hr : Antitone (removeBox μ i)
        · rw [lowerIntegerRow_removeBox μ i hi]
          apply ih _ hr
          have h := removeBox_sum μ i hi
          omega
        · rw [standardCount_eq_zero_of_not_antitone _ hr,
            factorialDeterminant_lower_not_antitone μ hμ i hr]
          simp
      · rw [if_neg hi, factorialDeterminant_lower_zero μ hμ i (by omega)]
        simp
    simp_rw [hterm]
    rw [← Finset.mul_sum, factorialDeterminant_predecessors]
    have hs : (∑ i, ((μ i : ℤ) : ℝ)) = (N + 1 : ℕ) := by
      simp only [Int.cast_natCast, ← Nat.cast_sum, hN]
    rw [hs, Nat.factorial_succ, Nat.cast_mul]
    ring

end Cloning.YoungGeneral
