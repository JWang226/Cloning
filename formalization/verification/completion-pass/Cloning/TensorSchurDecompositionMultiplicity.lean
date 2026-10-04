import Cloning.TensorSchurDecompositionPMF
import Cloning.TensorSchurMultiplicityDecomposition
import Cloning.YoungBranchingStandard

/-! Actual physical copy multiplicities equal the concrete standard-word count. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.YoungGeneral
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n d : ℕ}

theorem physicalCopyCount_eq_sum (L : List (PhysicalHighestTensor n d)) (mu : Fin d → ℕ) :
    physicalCopyCount L mu = ∑ i : Fin L.length, if (L.get i).weight = mu then 1 else 0 := by
  simp [physicalCopyCount, Finset.sum_boole]

@[simp] theorem physicalCopyCount_nil (mu : Fin d → ℕ) :
    physicalCopyCount ([] : List (PhysicalHighestTensor n d)) mu = 0 := by
  simp [physicalCopyCount]

@[simp] theorem physicalCopyCount_cons (H : PhysicalHighestTensor n d)
    (L : List (PhysicalHighestTensor n d)) (mu : Fin d → ℕ) :
    physicalCopyCount (H :: L) mu =
      (if H.weight = mu then 1 else 0) + physicalCopyCount L mu := by
  simp only [physicalCopyCount_eq_sum, List.length_cons, Fin.sum_univ_succ,
    List.get_cons_zero]
  rfl

@[simp] theorem physicalCopyCount_append (L K : List (PhysicalHighestTensor n d))
    (mu : Fin d → ℕ) : physicalCopyCount (L ++ K) mu =
      physicalCopyCount L mu + physicalCopyCount K mu := by
  induction L with
  | nil => simp
  | cons H L ih => simp [ih, Nat.add_assoc]

/-- The predecessor count for one actual irreducible copy. Every addable row
occurs exactly once, by the physical branching construction. -/
theorem fundamentalBranchList_copyCount (H : PhysicalHighestTensor n d) (mu : Fin d → ℕ) :
    physicalCopyCount (fundamentalBranchList H) mu =
      if Antitone mu then ∑ r : Fin d,
        if 0 < mu r then (if H.weight = removeBox mu r then 1 else 0) else 0 else 0 := by
  by_cases hmu : Antitone mu
  · rw [if_pos hmu]
    have hc : physicalCopyCount (fundamentalBranchList H) mu =
        (Finset.univ.filter (fun r : Fin d => addBox H.weight r = mu)).card := by
      unfold physicalCopyCount
      apply Finset.card_bij (fun i _ => (fundamentalBranchData H).rows i)
      · intro i hi
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, (fundamentalBranchData H).labels i |>.symm.trans
          (Finset.mem_filter.mp hi).2⟩
      · intro i hi j hj he
        exact (fundamentalBranchData H).rows.injective he
      · intro r hr
        have he := (Finset.mem_filter.mp hr).2
        obtain ⟨i, hi⟩ := ((fundamentalBranchData H).row_range r).mp (he ▸ hmu)
        refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hi⟩
        exact ((fundamentalBranchData H).labels i).trans (hi ▸ he)
    rw [hc]
    calc
      _ = ∑ r : Fin d, if addBox H.weight r = mu then (1 : ℕ) else 0 := by simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r _
        by_cases hr : 0 < mu r <;> simp [addBox_eq_iff, hr]

  · rw [if_neg hmu]
    exact physicalCopyCount_eq_zero_of_not_partition _ _ (Or.inl hmu)

/-- Refinement of a physical list obeys the same exact predecessor recurrence
as the standard-tableau row words. -/
theorem fundamentalRefinement_copyCount (L : List (PhysicalHighestTensor n d))
    (mu : Fin d → ℕ) :
    physicalCopyCount (L.flatMap fundamentalBranchList) mu =
      if Antitone mu then ∑ r : Fin d,
        if 0 < mu r then physicalCopyCount L (removeBox mu r) else 0 else 0 := by
  by_cases hmu : Antitone mu
  · rw [if_pos hmu]
    induction L with
    | nil => simp
    | cons H L ih =>
      rw [List.flatMap_cons, physicalCopyCount_append, fundamentalBranchList_copyCount,
        if_pos hmu, ih, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : 0 < mu r <;> simp [hr]
  · rw [if_neg hmu]
    exact physicalCopyCount_eq_zero_of_not_partition _ _ (Or.inl hmu)

/-- The physical multiplicity formula, with no representation-theoretic count
or decomposition premise. -/
theorem recursivePhysicalDecomposition_copyCount (n d : ℕ) (mu : Fin d → ℕ) :
    physicalCopyCount (recursivePhysicalDecomposition n d) mu = standardCount n mu := by
  induction n generalizing mu with
  | zero =>
    simp only [recursivePhysicalDecomposition_zero, physicalCopyCount_cons,
      emptyPhysicalHighest_weight, physicalCopyCount_nil, Nat.add_zero]
    have hs : ∀ w : Fin 0 → Fin d, IsStandardWord w := by
      intro w k a b hab
      simp
    have hr : ∀ w : Fin 0 → Fin d, rowCount w = fun _ => 0 := by
      intro w
      funext a
      simp [rowCount]
    simp [standardCount_eq_sum, hs, hr]
  | succ n ih =>
    rw [recursivePhysicalDecomposition_succ, fundamentalRefinement_copyCount, standardCount_succ]
    simp_rw [ih]

/-- The normalized physical Young law with exact standard-tableau multiplicity. -/
def tensorYoungPMF (n d : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hs : ∑ a, p a = 1) : PMF (Shape d n) :=
  physicalYoungPMF (recursivePhysicalDecomposition n d)
    (recursivePhysicalDecomposition_is_decomposition n d).1
    (recursivePhysicalDecomposition_is_decomposition n d).2 p hp hs

theorem tensorYoungPMF_formula (n d : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hs : ∑ a, p a = 1) (mu : Shape d n) :
    (tensorYoungPMF n d p hp hs mu).toReal =
      (standardCount n (fun a => (mu a).val) : ℝ) *
        physicalSectorCharacter (fun a => (mu a).val) p := by
  rw [tensorYoungPMF, physicalYoungPMF_toReal, recursivePhysicalDecomposition_copyCount]

end Cloning.TensorLie
