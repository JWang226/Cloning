import Cloning.YoungBranchingContent

/-!
# Exact branching of the total concrete tableau mass

This file performs the standard-tableau half of normalization directly on
the finite formula.  The resulting one-box Schur sum is explicit.  It is not
replaced by a supplied normalization or concentration premise.
-/

noncomputable section
open scoped BigOperators Classical

namespace Cloning.YoungGeneral

def zeroSemistandardContent (d N : ℕ) : SemistandardContent N (0 : Fin d → ℕ) :=
  ⟨fun _ _ ↦ 0, by simp [IsSemistandardContent]⟩

theorem eq_zeroSemistandardContent {d N : ℕ} (A : SemistandardContent N (0 : Fin d → ℕ)) :
    A = zeroSemistandardContent d N := by
  apply Subtype.ext
  funext i j
  apply Fin.ext
  have h := content_entry_le_row A i j
  change (A.val i j).val = 0
  exact Nat.eq_zero_of_le_zero h

theorem schurPolynomial_zero_shape (d N : ℕ) (p : Fin d → ℝ) :
    schurPolynomial N p (0 : Fin d → ℕ) = 1 := by
  rw [schurPolynomial_eq_content_sum]
  rw [Finset.sum_eq_single (zeroSemistandardContent d N)]
  · simp [zeroSemistandardContent, contentWeight]
  · intro A _ hA
    exact False.elim (hA (eq_zeroSemistandardContent A))
  · simp

def weightedStandardSum {d : ℕ} (N : ℕ) (F : (Fin d → ℕ) → ℝ) : ℝ :=
  ∑ w : Fin N → Fin d, if IsStandardWord w then F (rowCount w) else 0

theorem weightedStandardSum_zero {d : ℕ} (F : (Fin d → ℕ) → ℝ) :
    weightedStandardSum 0 F = F 0 := by
  have hs (w : Fin 0 → Fin d) : IsStandardWord w := by
    intro n i j hij
    simp
  have hr (w : Fin 0 → Fin d) : rowCount w = 0 := by
    funext i
    simp [rowCount]
  simp [weightedStandardSum, hs, hr]

/-- Weighted standard-tableau branching, proved by the actual final-letter
equivalence for words. -/
theorem weightedStandardSum_succ {d : ℕ} (N : ℕ) (F : (Fin d → ℕ) → ℝ) :
    weightedStandardSum (N + 1) F = weightedStandardSum N
      (fun μ ↦ ∑ i : Fin d, if Antitone (addBox μ i) then F (addBox μ i) else 0) := by
  unfold weightedStandardSum
  rw [← (Fin.snocEquiv (fun _ : Fin (N + 1) ↦ Fin d)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  change (∑ i : Fin d, if IsStandardWord (Fin.snoc w i) then F (rowCount (Fin.snoc w i)) else 0) = _
  simp_rw [isStandardWord_snoc_iff, rowCount_snoc]
  by_cases hw : IsStandardWord w
  · simp only [hw, true_and, if_true]
  · simp only [hw, false_and, if_false, Finset.sum_const_zero]

def totalTableauMass (d N : ℕ) (p : Fin d → ℝ) : ℝ :=
  ∑ μ : Shape d N, youngWeight N p (fun i ↦ (μ i).val)

theorem totalTableauMass_eq_standardSum (d N : ℕ) (p : Fin d → ℝ) :
    totalTableauMass d N p = weightedStandardSum N (schurPolynomial N p) := by
  have h := sum_youngWeight_mul N p (fun _ ↦ (1 : ℝ))
  simpa only [mul_one, totalTableauMass, weightedStandardSum, standardWordWeight] using h

theorem totalTableauMass_zero (d : ℕ) (p : Fin d → ℝ) : totalTableauMass d 0 p = 1 := by
  rw [totalTableauMass_eq_standardSum, weightedStandardSum_zero, schurPolynomial_zero_shape]

/-- The entire normalization problem reduces to the explicit one-box Schur
sum at each actual standard-tableau shape; no abstract law enters this identity. -/
theorem totalTableauMass_succ (d N : ℕ) (p : Fin d → ℝ) :
    totalTableauMass d (N + 1) p = weightedStandardSum N
      (fun μ ↦ ∑ i : Fin d, if Antitone (addBox μ i) then schurPolynomial (N + 1) p (addBox μ i) else 0) := by
  rw [totalTableauMass_eq_standardSum, weightedStandardSum_succ]

theorem weightedStandardSum_congr_on_shapes {d : ℕ} (N : ℕ)
    (F G : (Fin d → ℕ) → ℝ)
    (h : ∀ μ, Antitone μ → (∑ i, μ i = N) → F μ = G μ) :
    weightedStandardSum N F = weightedStandardSum N G := by
  apply Finset.sum_congr rfl
  intro w _
  split_ifs with hw
  · exact h (rowCount w) (standardWord_rows_antitone w hw) (sum_rowCount w)
  · rfl

end Cloning.YoungGeneral
