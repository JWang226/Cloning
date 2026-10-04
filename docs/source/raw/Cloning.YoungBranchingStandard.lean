import Cloning.YoungGeneralTableaux
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Exact branching of the standard-tableau count

The concrete standard words used in the general Young formula are split at
their final letter.  This proves the Young-lattice predecessor recurrence,
including all support conditions, without supplying any dimension or branching
formula as a hypothesis.  This is one half of the normalization induction;
the weighted semistandard Pieri bijection is a separate combinatorial step.
-/

noncomputable section
open scoped BigOperators Classical

namespace Cloning.YoungGeneral

def addBox {d : ℕ} (μ : Fin d → ℕ) (i : Fin d) : Fin d → ℕ :=
  fun j ↦ μ j + if j = i then 1 else 0

def removeBox {d : ℕ} (μ : Fin d → ℕ) (i : Fin d) : Fin d → ℕ :=
  fun j ↦ μ j - if j = i then 1 else 0

theorem addBox_eq_iff {d : ℕ} (ν μ : Fin d → ℕ) (i : Fin d) :
    addBox ν i = μ ↔ 0 < μ i ∧ ν = removeBox μ i := by
  constructor
  · intro h
    have hi := congrFun h i
    simp only [addBox, ite_true] at hi
    refine ⟨by omega, funext fun j ↦ ?_⟩
    have hj := congrFun h j
    dsimp only [addBox] at hj
    dsimp only [removeBox]
    split_ifs at hj ⊢ <;> omega
  · rintro ⟨hi, rfl⟩
    funext j
    dsimp only [addBox, removeBox]
    by_cases hji : j = i
    · subst j
      simp only [ite_true]
      omega
    · simp [hji]

theorem addBox_sum {d : ℕ} (μ : Fin d → ℕ) (i : Fin d) :
    ∑ j, addBox μ i j = (∑ j, μ j) + 1 := by
  simp [addBox, Finset.sum_add_distrib]

def prefixCount {d N : ℕ} (w : Fin N → Fin d) (n : ℕ) (i : Fin d) : ℕ :=
  ∑ k, if k.val < n ∧ w k = i then 1 else 0

theorem prefixCount_eq_card {d N : ℕ} (w : Fin N → Fin d) (n : ℕ) (i : Fin d) :
    prefixCount w n i = (Finset.univ.filter (fun k ↦ k.val < n ∧ w k = i)).card := by
  simp [prefixCount, Finset.sum_boole]

theorem isStandardWord_iff_prefix {d N : ℕ} (w : Fin N → Fin d) :
    IsStandardWord w ↔ ∀ n, Antitone (prefixCount w n) := by
  simp only [IsStandardWord, Antitone, prefixCount_eq_card]

theorem prefixCount_eq_rowCount {d N : ℕ} (w : Fin N → Fin d) (n : ℕ) (hn : N ≤ n) :
    prefixCount w n = rowCount w := by
  funext i
  simp only [prefixCount_eq_card, rowCount]
  congr 1
  apply Finset.filter_congr
  intro k _
  simp only [show k.val < n from lt_of_lt_of_le k.isLt hn, true_and]

theorem prefixCount_snoc {d N : ℕ} (w : Fin N → Fin d) (i : Fin d) (n : ℕ) (j : Fin d) :
    prefixCount (Fin.snoc w i) n j = prefixCount w n j + if N < n ∧ i = j then 1 else 0 := by
  simp only [prefixCount, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.val_castSucc,
    Fin.snoc_last, Fin.val_last]

theorem rowCount_snoc {d N : ℕ} (w : Fin N → Fin d) (i : Fin d) :
    rowCount (Fin.snoc w i) = addBox (rowCount w) i := by
  rw [← prefixCount_eq_rowCount (Fin.snoc w i) (N + 1) le_rfl]
  funext j
  rw [prefixCount_snoc, prefixCount_eq_rowCount w (N + 1) (by omega)]
  simp [addBox, eq_comm]

/-- Extending a standard tableau by one label requires exactly that the new
shape remain a decreasing partition. -/
theorem isStandardWord_snoc_iff {d N : ℕ} (w : Fin N → Fin d) (i : Fin d) :
    IsStandardWord (Fin.snoc w i) ↔
      IsStandardWord w ∧ Antitone (addBox (rowCount w) i) := by
  rw [isStandardWord_iff_prefix, isStandardWord_iff_prefix]
  constructor
  · intro h
    refine ⟨fun n ↦ ?_, ?_⟩
    · by_cases hn : n ≤ N
      · have he : prefixCount (Fin.snoc w i) n = prefixCount w n := by
          funext j
          rw [prefixCount_snoc]
          simp [Nat.not_lt.mpr hn]
        rw [← he]
        exact h n
      · rw [prefixCount_eq_rowCount w n (by omega)]
        have he : prefixCount (Fin.snoc w i) N = rowCount w := by
          funext j
          rw [prefixCount_snoc, prefixCount_eq_rowCount w N le_rfl]
          simp
        rw [← he]
        exact h N
    · have he : prefixCount (Fin.snoc w i) (N + 1) = addBox (rowCount w) i := by
        rw [prefixCount_eq_rowCount _ _ le_rfl, rowCount_snoc]
      rw [← he]
      exact h (N + 1)
  · rintro ⟨hw, hi⟩ n
    by_cases hn : n ≤ N
    · have he : prefixCount (Fin.snoc w i) n = prefixCount w n := by
        funext j
        rw [prefixCount_snoc]
        simp [Nat.not_lt.mpr hn]
      rw [he]
      exact hw n
    · rw [prefixCount_eq_rowCount _ _ (by omega), rowCount_snoc]
      exact hi

theorem standardCount_eq_sum {d : ℕ} (N : ℕ) (μ : Fin d → ℕ) :
    standardCount N μ = ∑ w : Fin N → Fin d, if IsStandardWord w ∧ rowCount w = μ then 1 else 0 := by
  simp [standardCount, Finset.sum_boole]

/-- Exact predecessor branching for the standard-tableau dimension. -/
theorem standardCount_succ {d : ℕ} (N : ℕ) (μ : Fin d → ℕ) :
    standardCount (N + 1) μ =
      if Antitone μ then ∑ i : Fin d, if 0 < μ i then standardCount N (removeBox μ i) else 0 else 0 := by
  rw [standardCount_eq_sum]
  rw [← (Fin.snocEquiv (fun _ : Fin (N + 1) ↦ Fin d)).sum_comp]
  rw [Fintype.sum_prod_type]
  by_cases hμ : Antitone μ
  · rw [if_pos hμ]
    apply Finset.sum_congr rfl
    intro i _
    have hpoint (w : Fin N → Fin d) :
        (if IsStandardWord (Fin.snoc w i) ∧ rowCount (Fin.snoc w i) = μ then 1 else 0 : ℕ) =
          if 0 < μ i then (if IsStandardWord w ∧ rowCount w = removeBox μ i then 1 else 0) else 0 := by
      rw [isStandardWord_snoc_iff, rowCount_snoc]
      by_cases hi : 0 < μ i
      · rw [if_pos hi]
        congr 1
        rw [and_assoc, and_left_comm]
        apply propext
        constructor
        · rintro ⟨_, hw, he⟩
          exact ⟨hw, (addBox_eq_iff _ _ i).mp he |>.2⟩
        · rintro ⟨hw, he⟩
          have he' := (addBox_eq_iff _ _ i).mpr ⟨hi, he⟩
          exact ⟨he' ▸ hμ, hw, he'⟩
      · rw [if_neg hi]
        apply if_neg
        rintro ⟨_, he⟩
        exact hi ((addBox_eq_iff _ _ i).mp he).1
    change (∑ w : Fin N → Fin d,
      if IsStandardWord (Fin.snoc w i) ∧ rowCount (Fin.snoc w i) = μ then 1 else 0) = _
    simp_rw [hpoint]
    by_cases hi : 0 < μ i
    · simp only [if_pos hi, ← standardCount_eq_sum]
    · simp only [if_neg hi, Finset.sum_const_zero]
  · rw [if_neg hμ]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro w _
    change (if IsStandardWord (Fin.snoc w i) ∧ rowCount (Fin.snoc w i) = μ then 1 else 0) = 0
    apply if_neg
    rintro ⟨hw, he⟩
    exact hμ (he ▸ standardWord_rows_antitone _ hw)

end Cloning.YoungGeneral
