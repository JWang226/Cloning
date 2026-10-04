import Cloning.TensorLANEmbeddingSchur
import Cloning.TensorSchurDecompositionMultiplicity

/-! The reverse cell selector chooses physical copies uniformly within the
measured partition label. Its weights and outside fallback sum to one by the
proved physical multiplicity count, without a normalization premise. -/
noncomputable section
open scoped BigOperators Classical
namespace Cloning.TensorLAN
open MeasureTheory Cloning.TensorLie Cloning.PCT Cloning.InfiniteTraceClass Cloning.Hybrid
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

section Selector
variable {ι Λ X : Type*} [Fintype ι] [DecidableEq Λ] [MeasurableSpace Λ]
  [MeasurableSingletonClass Λ] [MeasurableSpace X] {ν : Measure X}

def labelMultiplicity (labels : ι → Λ) (a : Λ) : ℕ :=
  (Finset.univ.filter (fun i => labels i = a)).card

def copyCellWeight (labels : ι → Λ) (q : X → Λ) (i : ι) (x : X) : ℝ :=
  if q x = labels i then 1 / (labelMultiplicity labels (labels i) : ℝ) else 0

def uniformLabelSelector (labels : ι → Λ) (q : X → Λ) : Option ι → X → ℝ
  | none, x => 1 - ∑ i, copyCellWeight labels q i x
  | some i, x => copyCellWeight labels q i x

theorem copyCellWeight_nonneg (labels : ι → Λ) (q : X → Λ) (i : ι) (x : X) :
    0 ≤ copyCellWeight labels q i x := by
  unfold copyCellWeight
  split_ifs <;> positivity

theorem copyCellWeight_sum (labels : ι → Λ) (q : X → Λ) (x : X) :
    (∑ i, copyCellWeight labels q i x) =
      if labelMultiplicity labels (q x) = 0 then 0 else 1 := by
  have he : (∑ i, copyCellWeight labels q i x) =
      (∑ i : ι, if labels i = q x then (1 : ℝ) else 0) / labelMultiplicity labels (q x) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : labels i = q x <;> simp [copyCellWeight, hi, eq_comm]
  rw [he]
  have hc : (∑ i : ι, if labels i = q x then (1 : ℝ) else 0) =
      (labelMultiplicity labels (q x) : ℝ) := by
    simp [labelMultiplicity]
  rw [hc]
  by_cases hz : labelMultiplicity labels (q x) = 0
  · simp [hz]
  · simp [hz, Nat.cast_ne_zero.mpr hz]

theorem uniformLabelSelector_nonneg (labels : ι → Λ) (q : X → Λ) (i : Option ι) (x : X) :
    0 ≤ uniformLabelSelector labels q i x := by
  cases i with
  | none => simp only [uniformLabelSelector, copyCellWeight_sum]; split_ifs <;> norm_num
  | some i => exact copyCellWeight_nonneg labels q i x

theorem uniformLabelSelector_sum (labels : ι → Λ) (q : X → Λ) (x : X) :
    (∑ i : Option ι, uniformLabelSelector labels q i x) = 1 := by
  rw [Fintype.sum_option]
  simp only [uniformLabelSelector]
  ring

theorem copyCellWeight_measurable (labels : ι → Λ) (q : X → Λ) (hq : Measurable q) (i : ι) :
    Measurable (copyCellWeight labels q i) := by
  apply Measurable.ite _ measurable_const measurable_const
  exact hq (measurableSet_singleton (labels i))

theorem uniformLabelSelector_measurable (labels : ι → Λ) (q : X → Λ) (hq : Measurable q)
    (i : Option ι) : Measurable (uniformLabelSelector labels q i) := by
  cases i with
  | none =>
      exact measurable_const.sub (Finset.measurable_sum _
        (fun j _ => copyCellWeight_measurable labels q hq j))
  | some i => exact copyCellWeight_measurable labels q hq i

end Selector

local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def schurCopyLabel (n d : ℕ) (i : SchurCopy n d) : Fin d → ℕ :=
  ((recursivePhysicalDecomposition n d).get i).weight

theorem schurCopyLabel_multiplicity (n d : ℕ) (a : Fin d → ℕ) :
    labelMultiplicity (schurCopyLabel n d) a = Cloning.YoungGeneral.standardCount n a :=
  recursivePhysicalDecomposition_copyCount n d a

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- Read a measurable classical label, choose uniformly among its actual
physical copies, and use the explicit physical fallback outside the label set. -/
def schurReverseFromLabels (n d R : ℕ) (ρ : DensityState (TensorRegister n (Fin d)))
    (q : X → Fin d → ℕ) (hq : Measurable q) :
    HybridToQuantum (RootFock d) (TensorRegister n (Fin d)) ν :=
  schurReverse n d R ρ (uniformLabelSelector (schurCopyLabel n d) q)
    (fun i => (uniformLabelSelector_measurable _ _ hq i).aestronglyMeasurable)
    (uniformLabelSelector_nonneg _ _) (uniformLabelSelector_sum _ _)

/-- On each label cell the reverse channel uses exactly reciprocal tableau
multiplicity, now identified with the actual physical copy count. -/
theorem schurReverseFromLabels_copy_weight (n d : ℕ) (q : X → Fin d → ℕ)
    (i : SchurCopy n d) (x : X) :
    uniformLabelSelector (schurCopyLabel n d) q (some i) x =
      if q x = schurCopyLabel n d i then
        1 / (Cloning.YoungGeneral.standardCount n (schurCopyLabel n d i) : ℝ) else 0 := by
  simp only [uniformLabelSelector, copyCellWeight, schurCopyLabel_multiplicity]

end Cloning.TensorLAN
