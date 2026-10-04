import Cloning.TensorLANEmbeddingCellWeights

/-! Exact reconstruction of physical copy probabilities by the reverse
uniform-within-label selector. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace NNReal ENNReal
open MeasureTheory Filter
namespace Cloning.TensorLAN
open Cloning.YoungHyperplane Cloning.TensorLie Cloning.PCTJointGaussianWhitening
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

section Generic
variable {ι Λ X : Type*} [Fintype ι] [DecidableEq Λ] [MeasurableSpace Λ]
  [MeasurableSingletonClass Λ] [MeasurableSpace X] {ν : Measure X}

theorem labelMultiplicity_own_pos (labels : ι → Λ) (i : ι) :
    0 < labelMultiplicity labels (labels i) := by
  apply Finset.card_pos.mpr
  exact ⟨i, by simp [labelMultiplicity]⟩

theorem copyCellWeight_mul_integrable (labels : ι → Λ) (q : X → Λ)
    (hq : Measurable q) (f : X → ℝ) (hf : Integrable f ν) (i : ι) :
    Integrable (fun x => copyCellWeight labels q i x * f x) ν := by
  have he : (fun x => copyCellWeight labels q i x*f x) =
      fun x => (1/(labelMultiplicity labels (labels i) : ℝ)) *
        ((q ⁻¹' {labels i}).indicator f) x := by
    funext x
    by_cases hx : q x = labels i <;> simp [copyCellWeight, Set.indicator, hx]
  rw [he]
  exact (hf.indicator (hq (measurableSet_singleton _))).const_mul _

theorem integral_copyCellWeight_mul (labels : ι → Λ) (q : X → Λ)
    (hq : Measurable q) (f : X → ℝ) (i : ι) :
    (∫ x, copyCellWeight labels q i x*f x ∂ν) =
      YoungRounding.binMass ν q f (labels i) / labelMultiplicity labels (labels i) := by
  have he : (fun x => copyCellWeight labels q i x*f x) =
      fun x => (1/(labelMultiplicity labels (labels i) : ℝ)) *
        ((q ⁻¹' {labels i}).indicator f) x := by
    funext x
    by_cases hx : q x = labels i <;> simp [copyCellWeight, Set.indicator, hx]
  rw [he, integral_const_mul, integral_indicator (hq (measurableSet_singleton _))]
  simp only [YoungRounding.binMass, one_div, div_eq_mul_inv, mul_comm,
    one_mul]

theorem copyCellWeight_recovers (labels : ι → Λ) (q : X → Λ)
    (hq : Measurable q) (f : X → ℝ) (w : ι → ℝ)
    (hlabels : ∀ i j, labels i = labels j → w i = w j)
    (hmass : ∀ a, YoungRounding.binMass ν q f a =
      ∑ i, if labels i = a then w i else 0) (i : ι) :
    (∫ x, copyCellWeight labels q i x*f x ∂ν) = w i := by
  rw [integral_copyCellWeight_mul labels q hq f i, hmass]
  have he : (∑ j, if labels j = labels i then w j else 0) =
      (labelMultiplicity labels (labels i) : ℝ)*w i := by
    calc
      _ = ∑ j, if labels j = labels i then w i else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs with h
        · exact hlabels j i h
        · rfl
      _ = _ := by simp [labelMultiplicity, Finset.sum_ite, mul_comm]
  rw [he]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (labelMultiplicity_own_pos labels i).ne')

theorem uniformLabelSelector_recovers (labels : ι → Λ) (q : X → Λ)
    (hq : Measurable q) (f : X → ℝ) (hf : Integrable f ν) (hint : ∫ x, f x ∂ν = 1)
    (w : ι → ℝ) (hw : ∑ i, w i = 1)
    (hlabels : ∀ i j, labels i = labels j → w i = w j)
    (hmass : ∀ a, YoungRounding.binMass ν q f a =
      ∑ i, if labels i = a then w i else 0) (i : Option ι) :
    (∫ x, uniformLabelSelector labels q i x*f x ∂ν) =
      i.elim 0 w := by
  cases i with
  | some i => exact copyCellWeight_recovers labels q hq f w hlabels hmass i
  | none =>
    have he : (fun x => uniformLabelSelector labels q none x*f x) =
        fun x => f x - ∑ i, copyCellWeight labels q i x*f x := by
      funext x
      simp [uniformLabelSelector, sub_mul, Finset.sum_mul]
    rw [he, integral_sub hf (integrable_finset_sum _
      (fun i _ => copyCellWeight_mul_integrable labels q hq f hf i)),
      integral_finset_sum _ (fun i _ => copyCellWeight_mul_integrable labels q hq f hf i)]
    simp_rw [copyCellWeight_recovers labels q hq f w hlabels hmass]
    simp only [hint, hw, sub_self, Option.elim_none]
end Generic

/-- Copies with the same literal affine label have the same actual character
weight, because their canonical cyclic sectors are identical. -/
theorem physicalCopy_character_eq_of_lattice_eq (N d : ℕ) (p : Fin (d+1) → ℝ)
    (i j : SchurCopy N (d+1)) (h : schurCopyLattice N d i = schurCopyLattice N d j) :
    ((recursivePhysicalDecomposition N (d+1)).get i).character p =
      ((recursivePhysicalDecomposition N (d+1)).get j).character p := by
  have hw : ((recursivePhysicalDecomposition N (d+1)).get i).weight =
      ((recursivePhysicalDecomposition N (d+1)).get j).weight := by
    funext a
    have he := congrArg (fun x : Lattice d (N : ℤ) => x.1 a) h
    change (((recursivePhysicalDecomposition N (d+1)).get i).weight a : ℤ) =
      (((recursivePhysicalDecomposition N (d+1)).get j).weight a : ℤ) at he
    exact_mod_cast he
  simp only [PhysicalHighestTensor.character_eq_physicalSectorCharacter, hw]

end Cloning.TensorLAN
