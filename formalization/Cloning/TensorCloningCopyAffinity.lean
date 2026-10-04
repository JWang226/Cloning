import Cloning.TensorCloningKernelLabels
import Cloning.TensorLANEmbeddingSchurWeights
import Cloning.YoungPhysicalRoundingLabels

/-! Exact preservation of classical fidelity when uniformly distributed
physical multiplicity copies are grouped into their Young labels. -/
noncomputable section
open scoped BigOperators Classical ENNReal
namespace Cloning.TensorCloning
open Cloning.TensorLie Cloning.TensorLAN Cloning.YoungGeneral Cloning.YoungCompatibility
open Cloning.YoungHyperplane
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section FiberAffinity
variable {ι Λ : Type*} [Fintype ι] [DecidableEq Λ]

theorem probability_map_eq_sum (P : PMF ι) (label : ι → Λ) (a : Λ) :
    probability (P.map label) a = ∑ i ∈ Finset.univ.filter (fun i ↦ label i = a), probability P i := by
  rw [probability, PMF.map_apply, tsum_fintype,
    ENNReal.toReal_sum (by intro i hi; split_ifs <;> simp [P.apply_ne_top i])]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : label i = a
  · simp only [h, if_true, probability]
  · simp only [h, Ne.symm h, if_false, ENNReal.toReal_zero]

/-- Grouping copies loses no affinity when each law is constant on every
multiplicity fiber. The label type can be countably infinite. -/
theorem affinity_map_of_constant_fibers (P Q : PMF ι) (label : ι → Λ)
    (hP : ∀ i j, label i = label j → probability P i = probability P j)
    (hQ : ∀ i j, label i = label j → probability Q i = probability Q j) :
    CountableScheffe.affinity (probability (P.map label)) (probability (Q.map label)) =
      CountableScheffe.affinity (probability P) (probability Q) := by
  unfold CountableScheffe.affinity
  rw [tsum_eq_sum (s := Finset.univ.image label) (by
    intro a ha
    have hz : probability (P.map label) a = 0 := by
      rw [probability_map_eq_sum]
      apply Finset.sum_eq_zero
      intro i hi
      exact False.elim (ha (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩))
    rw [hz, Real.sqrt_zero, zero_mul])]
  rw [tsum_fintype]
  calc
    (∑ a ∈ Finset.univ.image label, Real.sqrt (probability (P.map label) a) *
        Real.sqrt (probability (Q.map label) a)) =
      ∑ a ∈ Finset.univ.image label, ∑ i ∈ Finset.univ.filter (fun i ↦ label i = a),
        Real.sqrt (probability P i) * Real.sqrt (probability Q i) := by
      apply Finset.sum_congr rfl
      intro a ha
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
      let S := Finset.univ.filter (fun i ↦ label i = label j)
      have hps : (∑ i ∈ S, probability P i) = (S.card : ℝ) * probability P j := by
        rw [Finset.sum_congr rfl (fun i hi ↦ hP i j (Finset.mem_filter.mp hi).2),
          Finset.sum_const, nsmul_eq_mul]
      have hqs : (∑ i ∈ S, probability Q i) = (S.card : ℝ) * probability Q j := by
        rw [Finset.sum_congr rfl (fun i hi ↦ hQ i j (Finset.mem_filter.mp hi).2),
          Finset.sum_const, nsmul_eq_mul]
      rw [probability_map_eq_sum, probability_map_eq_sum]
      change Real.sqrt (∑ i ∈ S, probability P i) * Real.sqrt (∑ i ∈ S, probability Q i) = _
      rw [hps, hqs, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_mul (Nat.cast_nonneg _)]
      have he : ∀ i ∈ S, Real.sqrt (probability P i) * Real.sqrt (probability Q i) =
          Real.sqrt (probability P j) * Real.sqrt (probability Q j) := by
        intro i hi
        rw [hP i j (Finset.mem_filter.mp hi).2, hQ i j (Finset.mem_filter.mp hi).2]
      rw [show (∑ i ∈ Finset.univ.filter (fun i ↦ label i = label j),
          Real.sqrt (probability P i) * Real.sqrt (probability Q i)) =
          (S.card : ℝ) * (Real.sqrt (probability P j) * Real.sqrt (probability Q j)) by
        rw [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul]]
      calc
        _ = (Real.sqrt (S.card : ℝ) * Real.sqrt (S.card : ℝ)) *
            (Real.sqrt (probability P j) * Real.sqrt (probability Q j)) := by ring
        _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun i _ ↦ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) _

end FiberAffinity

/-- The output-copy law of the literal spectrum-independent channel. -/
def universalOutputCopyPMF (n m d : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : PMF (SchurCopy m (d+1)) :=
  (physicalCopyPMF n (d+1) p hp hs).bind (universalCopyPMF n m d)

theorem physicalCopyPMF_integer_label (n d : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    (physicalCopyPMF n (d+1) p hp hs).map (integerCopyLabel n d) =
      tensorYoungIntegerPMF d n p hp hs := by
  rw [tensorYoungIntegerPMF, tensorYoungPMF_eq_map_copies, PMF.map_comp]
  rfl

theorem universalOutputCopyPMF_integer_label (n m d : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    (universalOutputCopyPMF n m d p hp hs).map (integerCopyLabel m d) =
      tensorYoungFallbackOutput d n m ((m : ℝ)/(n : ℝ)) p hp hs := by
  rw [universalOutputCopyPMF, PMF.map_bind]
  simp_rw [universalCopyPMF_label]
  rw [tensorYoungFallbackOutput, tensorYoungPMF_eq_map_copies, PMF.bind_map]
  rfl

theorem universalCopyPMF_constant_fibers (n m d : ℕ) (i : SchurCopy n (d+1))
    (j k : SchurCopy m (d+1)) (hjk : integerCopyLabel m d j = integerCopyLabel m d k) :
    universalCopyPMF n m d i j = universalCopyPMF n m d i k := by
  unfold universalCopyPMF
  rw [PMF.bind_apply, PMF.bind_apply]
  apply tsum_congr
  intro ν
  by_cases hz : fallbackKernel ((m : ℝ)/(n : ℝ)) n m (integerCopyLabel n d i) ν = 0
  · simp [hz]
  · have hv := fallbackKernel_support_isYoung ((m : ℝ)/(n : ℝ)) n m
        (by omega) (integerCopyLabel n d i) (integerCopyLabel_isYoung n d i) ν hz
    simp only [uniformFiberPMF_apply _ _ ν (exists_copy_integer_label m d ν hv), hjk]

theorem universalOutputCopyPMF_constant_fibers (n m d : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (j k : SchurCopy m (d+1)) (hjk : integerCopyLabel m d j = integerCopyLabel m d k) :
    probability (universalOutputCopyPMF n m d p hp hs) j =
      probability (universalOutputCopyPMF n m d p hp hs) k := by
  unfold probability universalOutputCopyPMF
  congr 1
  rw [PMF.bind_apply, PMF.bind_apply]
  apply tsum_congr
  intro i
  rw [universalCopyPMF_constant_fibers n m d i j k hjk]

theorem physicalCopyPMF_constant_fibers (n d : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (j k : SchurCopy n (d+1)) (hjk : integerCopyLabel n d j = integerCopyLabel n d k) :
    probability (physicalCopyPMF n (d+1) p hp hs) j =
      probability (physicalCopyPMF n (d+1) p hp hs) k := by
  have hw : ((recursivePhysicalDecomposition n (d+1)).get j).weight =
      ((recursivePhysicalDecomposition n (d+1)).get k).weight := by
    funext a
    have ha := congrFun hjk a
    change (((recursivePhysicalDecomposition n (d+1)).get j).weight a : ℤ) =
      (((recursivePhysicalDecomposition n (d+1)).get k).weight a : ℤ) at ha
    exact_mod_cast ha
  simp only [probability, physicalCopyPMF_toReal,
    PhysicalHighestTensor.character_eq_physicalSectorCharacter, hw]

/-- The actual copy sampler retains exactly the classical Young-label
fidelity. No multiplicity correction remains in the global protocol. -/
theorem universalOutputCopyPMF_affinity (n m d : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    CountableScheffe.affinity (probability (universalOutputCopyPMF n m d p hp hs))
      (probability (physicalCopyPMF m (d+1) p hp hs)) =
    CountableScheffe.affinity
      (probability (tensorYoungFallbackOutput d n m ((m : ℝ)/(n : ℝ)) p hp hs))
      (probability (tensorYoungIntegerPMF d m p hp hs)) := by
  rw [← affinity_map_of_constant_fibers _ _ (integerCopyLabel m d)
    (universalOutputCopyPMF_constant_fibers n m d p hp hs)
    (physicalCopyPMF_constant_fibers m d p hp hs),
    universalOutputCopyPMF_integer_label, physicalCopyPMF_integer_label]

end Cloning.TensorCloning
