import Cloning.YoungBranchingStandard

/-! Removing the initial column below an addable row. -/
noncomputable section
namespace Cloning.TensorLie
open YoungGeneral
variable {d : ℕ}

/-- Remove one box from every row strictly above the chosen new box. -/
def removeInitialColumn (mu : Fin d → ℕ) (r : Fin d) : Fin d → ℕ :=
  fun a => mu a - if a < r then 1 else 0

theorem positive_above_addable (mu : Fin d → ℕ) (r : Fin d)
    (hr : Antitone (addBox mu r)) {a : Fin d} (ha : a < r) : 0 < mu a := by
  have h := hr (le_of_lt ha)
  have hne : a ≠ r := ne_of_lt ha
  simp [addBox, hne] at h
  omega

theorem removeInitialColumn_antitone (mu : Fin d → ℕ) (hmu : Antitone mu)
    (r : Fin d) (hr : Antitone (addBox mu r)) : Antitone (removeInitialColumn mu r) := by
  intro a b hab
  have h := hmu hab
  by_cases hbr : b < r
  · have har : a < r := lt_of_le_of_lt hab hbr
    simpa only [removeInitialColumn, if_pos hbr, if_pos har] using Nat.sub_le_sub_right h 1
  · by_cases har : a < r
    · have hgap := hr (le_of_lt har)
      have hne : a ≠ r := ne_of_lt har
      simp [addBox, hne] at hgap
      have htail := hmu (le_of_not_gt hbr)
      simp only [removeInitialColumn, if_neg hbr, if_pos har, Nat.sub_zero]
      omega
    · simpa only [removeInitialColumn, if_neg hbr, if_neg har, Nat.sub_zero] using h

theorem removeInitialColumn_add_indicator (mu : Fin d → ℕ) (r : Fin d)
    (hr : Antitone (addBox mu r)) (a : Fin d) :
    removeInitialColumn mu r a + (if a.val < r.val then 1 else 0) = mu a := by
  by_cases ha : a < r
  · have hp := positive_above_addable mu r hr ha
    simp only [removeInitialColumn, if_pos ha, if_pos (show a.val < r.val from ha)]
    omega
  · simp only [removeInitialColumn, if_neg ha, if_neg (show ¬ a.val < r.val from ha), Nat.sub_zero, add_zero]

theorem removeInitialColumn_add_succ_indicator (mu : Fin d → ℕ) (r : Fin d)
    (hr : Antitone (addBox mu r)) (a : Fin d) :
    removeInitialColumn mu r a + (if a.val < r.val + 1 then 1 else 0) = addBox mu r a := by
  have he := removeInitialColumn_add_indicator mu r hr a
  by_cases har : a < r
  · have hne := ne_of_lt har
    have hav : a.val < r.val := har
    simp only [if_pos hav] at he
    simp only [addBox, if_neg hne, if_pos (by omega : a.val < r.val + 1)]
    exact he
  · by_cases heq : a = r
    · subst a
      simp [removeInitialColumn, addBox]
    · have hneval : a.val ≠ r.val := fun h => heq (Fin.ext h)
      have hav : ¬ a.val < r.val := har
      simp only [if_neg hav, add_zero] at he
      simp only [addBox, if_neg heq, if_neg (by omega : ¬ a.val < r.val + 1), add_zero]
      exact he

end Cloning.TensorLie
