import Cloning.PCTCountMeasurementFidelity

/-! A finite computational measurement with arbitrary labels, including the
full affine count lattice. Its finite image supplies the actual CPTP map. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Classical
namespace Cloning.PCTCountMeasurement
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {H I J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype I]

theorem weightCLM_apply_any (b : I → H) (label : I → J) (j : J) (A : TraceClass H) :
    weightCLM b label j A = ∑ i, if label i=j then (⟪b i,A.1 (b i)⟫_ℂ).re else 0 := by
  simp only [weightCLM, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : label i=j
  · simp only [if_pos hi]; rfl
  · simp only [if_neg hi, ContinuousLinearMap.zero_apply]

def imageLabel (label : I → J) (i : I) : Set.range label := ⟨label i, i, rfl⟩

instance imageLabelFintype (label : I → J) : Fintype (Set.range label) :=
  (Set.finite_range label).fintype

theorem weightCLM_image (b : I → H) (label : I → J) (j : Set.range label) (A : TraceClass H) :
    weightCLM b (imageLabel label) j A = weightCLM b label j.val A := by
  simp only [weightCLM_apply, weightCLM_apply_any]
  apply Finset.sum_congr rfl
  intro i _
  have he : imageLabel label i=j ↔ label i=j.val := Subtype.ext_iff
  rw [he]

theorem weightCLM_zero_outside (b : I → H) (label : I → J) (A : TraceClass H)
    (j : J) (hj : j ∉ Set.range label) : weightCLM b label j A=0 := by
  rw [weightCLM_apply_any]
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (fun h => hj ⟨i,h⟩)

theorem weightCLM_support (b : I → H) (label : I → J) (A : TraceClass H) :
    Function.support (fun j => weightCLM b label j A) ⊆ Set.range label := by
  intro j hj
  by_contra hn
  exact hj (weightCLM_zero_outside b label A j hn)

theorem weightCLM_summable (b : I → H) (label : I → J) (A : TraceClass H) :
    Summable (fun j => weightCLM b label j A) :=
  summable_of_hasFiniteSupport ((Set.finite_range label).subset (weightCLM_support b label A))

theorem weightCLM_nonneg_any (b : I → H) (label : I → J) (A : TraceClass H)
    (hA : 0≤A.1) (j : J) : 0≤weightCLM b label j A := by
  by_cases hj : j∈Set.range label
  · rw [← weightCLM_image b label ⟨j,hj⟩ A]
    exact weightCLM_nonneg b (imageLabel label) ⟨j,hj⟩ A hA
  · rw [weightCLM_zero_outside b label A j hj]

theorem tsum_eq_image_sum (label : I → J) (f : J → ℝ)
    (hf : ∀ j, j∉Set.range label → f j=0) :
    (∑' j, f j) = ∑ j : Set.range label, f j.val := by
  have he : (∑' j : Set.range label, f j.val) = ∑' j, f j :=
    tsum_subtype_eq_of_support_subset (by
      intro j hj
      by_contra hn
      exact hj (hf j hn))
  simpa only [tsum_fintype] using he.symm

theorem weightCLM_tsum (b : OrthonormalBasis I ℂ H) (label : I → J) (A : TraceClass H) :
    (∑' j, weightCLM b label j A)=(traceCLM A).re := by
  rw [tsum_eq_image_sum label _ (weightCLM_zero_outside b label A)]
  simp_rw [← weightCLM_image]
  exact weightCLM_sum b (imageLabel label) A

theorem weightCLM_tsum_l1_contraction (b : OrthonormalBasis I ℂ H) (label : I → J)
    (A B : TraceClass H) (hA : 0≤A.1) (hB : 0≤B.1) :
    (∑' j, |weightCLM b label j A-weightCLM b label j B|)≤‖A-B‖ := by
  rw [tsum_eq_image_sum label _ (by
    intro j hj
    rw [weightCLM_zero_outside b label A j hj, weightCLM_zero_outside b label B j hj]
    simp)]
  simp_rw [← weightCLM_image]
  exact weightCLM_l1_contraction b (imageLabel label) A B hA hB

theorem rootFidelity_le_tsum_affinity [DecidableEq I] (label : I → J)
    (A B : PositiveTraceClass (Register I)) :
    A.rootFidelity B ≤ ∑' j, Real.sqrt (weightCLM (registerBasis I) label j A.1) *
      Real.sqrt (weightCLM (registerBasis I) label j B.1) := by
  rw [tsum_eq_image_sum label _ (by
    intro j hj
    rw [weightCLM_zero_outside _ label A.1 j hj]
    simp)]
  simp_rw [← weightCLM_image]
  have h := rootFidelity_le_measurement_affinity (imageLabel label) A B
  simpa only [Real.sqrt_mul (weightCLM_nonneg _ _ _ A.1 A.2)] using h

end Cloning.PCTCountMeasurement
