import Cloning.TensorCartanWordSplit
import Mathlib.Data.Nat.Choose.Basic

/-! The exact multiplicity of left/right root assignments is the product of
binomial coefficients of the root occupations. -/
noncomputable section
open scoped BigOperators
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

local instance : DecidableEq (PositiveRoot d → ℕ) := Classical.decEq _

def rootIncrement (a : PositiveRoot d) (k : PositiveRoot d → ℕ) : PositiveRoot d → ℕ :=
  Function.update k a (k a + 1)

def rootDecrement (a : PositiveRoot d) (k : PositiveRoot d → ℕ) : PositiveRoot d → ℕ :=
  Function.update k a (k a - 1)

theorem rootIncrement_injective (a : PositiveRoot d) : Function.Injective (rootIncrement a) := by
  intro k l h
  funext b
  have hb := congrFun h b
  by_cases he : b = a
  · subst b
    simpa [rootIncrement] using hb
  · simpa [rootIncrement, he] using hb

theorem rootIncrement_decrement (a : PositiveRoot d) (k : PositiveRoot d → ℕ)
    (h : 0 < k a) : rootIncrement a (rootDecrement a k) = k := by
  funext b
  by_cases he : b = a
  · subst b
    simp only [rootIncrement, rootDecrement, Function.update_self]
    omega
  · simp [rootIncrement, rootDecrement, he]

def rootOccupationSplits : List (PositiveRoot d) → List (PositiveRoot d → ℕ)
  | [] => [0]
  | a :: w => (rootOccupationSplits w).map (rootIncrement a) ++ rootOccupationSplits w

theorem rootCounts_cons (a : PositiveRoot d) (w : List (PositiveRoot d)) :
    (fun b => (a :: w).count b) = rootIncrement a (fun b => w.count b) := by
  funext b
  by_cases he : b = a
  · subst b
    simp [List.count_cons, rootIncrement, Nat.add_comm]
  · simp [List.count_cons, rootIncrement, he, Ne.symm he]

theorem loweringSplits_map_counts (w : List (PositiveRoot d)) :
    (loweringSplits w).map (fun uv => fun a => uv.1.count a) = rootOccupationSplits w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [loweringSplits, List.map_append, List.map_map, Function.comp_def,
      rootCounts_cons, rootOccupationSplits]
    have he : (fun uv : List (PositiveRoot d) × List (PositiveRoot d) =>
        fun b => (a :: uv.1).count b) = rootIncrement a ∘
          (fun uv : List (PositiveRoot d) × List (PositiveRoot d) => fun b => uv.1.count b) := by
      funext uv
      exact rootCounts_cons a uv.1
    rw [he, ← List.map_map, ih]

theorem count_map_rootIncrement (a : PositiveRoot d)
    (l : List (PositiveRoot d → ℕ)) (k : PositiveRoot d → ℕ) :
    (l.map (rootIncrement a)).count k =
      if k a = 0 then 0 else l.count (rootDecrement a k) := by
  classical
  by_cases hk : k a = 0
  · rw [if_pos hk]
    apply List.count_eq_zero.mpr
    intro h
    obtain ⟨r, _, hr⟩ := List.mem_map.mp h
    have he := congrFun hr a
    simp only [rootIncrement, Function.update_self, hk] at he
    omega
  · rw [if_neg hk]
    simpa only [rootIncrement_decrement a k (Nat.pos_of_ne_zero hk)] using
      List.count_map_of_injective l (rootIncrement a) (rootIncrement_injective a) (rootDecrement a k)

def occupationChoices (w : List (PositiveRoot d)) (k : PositiveRoot d → ℕ) : ℕ :=
  ∏ a : PositiveRoot d, (w.count a).choose (k a)

theorem occupationChoices_cons (a : PositiveRoot d) (w : List (PositiveRoot d))
    (k : PositiveRoot d → ℕ) :
    occupationChoices (a :: w) k =
      (if k a = 0 then 0 else occupationChoices w (rootDecrement a k)) +
        occupationChoices w k := by
  classical
  have hm : a ∈ (Finset.univ : Finset (PositiveRoot d)) := Finset.mem_univ a
  have hrest : (∏ b ∈ (Finset.univ : Finset (PositiveRoot d)).erase a,
      ((a :: w).count b).choose (k b)) =
      ∏ b ∈ (Finset.univ : Finset (PositiveRoot d)).erase a, (w.count b).choose (k b) := by
    apply Finset.prod_congr rfl
    intro b hb
    have hba := (Finset.mem_erase.mp hb).1
    simp [List.count_cons, hba, Ne.symm hba]
  have hdec : (∏ b ∈ (Finset.univ : Finset (PositiveRoot d)).erase a,
      (w.count b).choose (rootDecrement a k b)) =
      ∏ b ∈ (Finset.univ : Finset (PositiveRoot d)).erase a, (w.count b).choose (k b) := by
    apply Finset.prod_congr rfl
    intro b hb
    simp [rootDecrement, (Finset.mem_erase.mp hb).1]
  unfold occupationChoices
  rw [← Finset.mul_prod_erase _ (fun b => ((a :: w).count b).choose (k b)) hm]
  rw [hrest]
  rw [← Finset.mul_prod_erase _ (fun b => (w.count b).choose (k b)) hm]
  simp only [List.count_cons_self]
  by_cases hk : k a = 0
  · simp only [hk, if_true, Nat.choose_zero_right, one_mul, zero_add]
  · rw [if_neg hk, ← Finset.mul_prod_erase _
      (fun b => (w.count b).choose (rootDecrement a k b)) hm, hdec]
    simp only [rootDecrement, Function.update_self]
    rw [Nat.choose_succ_left _ _ (Nat.pos_of_ne_zero hk)]
    ring

/-- Independent choices among repeated roots give the exact product-binomial
multiplicity, without any operator or representation assumptions. -/
theorem rootOccupationSplits_count (w : List (PositiveRoot d))
    (k : PositiveRoot d → ℕ) :
    (rootOccupationSplits w).count k = occupationChoices w k := by
  classical
  induction w generalizing k with
  | nil =>
    by_cases hk : k = 0
    · subst k
      simp [rootOccupationSplits, occupationChoices]
    · have hz : occupationChoices ([] : List (PositiveRoot d)) k = 0 := by
        obtain ⟨a, ha⟩ : ∃ a, k a ≠ 0 := by
          by_contra! h
          exact hk (funext h)
        apply Finset.prod_eq_zero (Finset.mem_univ a)
        exact Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero ha)
      simp [rootOccupationSplits, hk, Ne.symm hk, hz]
  | cons a w ih =>
    rw [rootOccupationSplits, List.count_append, count_map_rootIncrement,
      occupationChoices_cons, ih, ih]

theorem loweringSplits_count_left_occupations (w : List (PositiveRoot d))
    (k : PositiveRoot d → ℕ) :
    ((loweringSplits w).map (fun uv => fun a => uv.1.count a)).count k =
      ∏ a : PositiveRoot d, (w.count a).choose (k a) := by
  rw [loweringSplits_map_counts, rootOccupationSplits_count]
  rfl

end Cloning.TensorLie
