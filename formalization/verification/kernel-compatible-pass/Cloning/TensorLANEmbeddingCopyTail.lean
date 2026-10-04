import Cloning.TensorLANEmbeddingSchurWeights
import Cloning.TensorLANEmbeddingTypical

/-! The exceptional weight of the literal physical copy mixture is exactly
the actual Young tail, hence has a uniform vanishing bound. -/
noncomputable section
open scoped BigOperators Topology Classical NNReal ENNReal
open Filter
namespace Cloning.TensorLAN
open Cloning.TensorLie Cloning.YoungGeneral
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem physicalCopy_expectation (N d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (f : Shape d N → ℝ) :
    (∑ mu, (tensorYoungPMF N d p hp hs mu).toReal*f mu) =
      ∑ i : SchurCopy N d, ((recursivePhysicalDecomposition N d).get i).character p *
        f ((recursivePhysicalDecomposition N d).get i).shape := by
  classical
  rw [tensorYoungPMF_eq_map_copies]
  simp_rw [PMF.map_apply, tsum_fintype]
  have he (mu : Shape d N) :
      (∑ i : SchurCopy N d, if mu = ((recursivePhysicalDecomposition N d).get i).shape then
        physicalCopyPMF N d p hp hs i else 0).toReal =
      ∑ i : SchurCopy N d, if mu = ((recursivePhysicalDecomposition N d).get i).shape then
        ((recursivePhysicalDecomposition N d).get i).character p else 0 := by
    rw [ENNReal.toReal_sum (by
      intro i _
      split_ifs
      · exact (physicalCopyPMF N d p hp hs).apply_ne_top i
      · exact ENNReal.zero_ne_top)]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  calc
    _ = ∑ mu : Shape d N, (∑ i : SchurCopy N d,
        if mu = ((recursivePhysicalDecomposition N d).get i).shape then
          ((recursivePhysicalDecomposition N d).get i).character p else 0)*f mu := by
      apply Finset.sum_congr rfl
      intro mu _
      apply congrArg (fun x : ℝ => x*f mu)
      convert he mu using 1 <;> congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : mu = ((recursivePhysicalDecomposition N d).get i).shape
      · simp only [if_pos hi]
      · simp only [if_neg hi]
    _ = _ := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp

def physicalCopyTail (N d : ℕ) (p : Fin d → ℝ) : ℝ :=
  ∑ i : SchurCopy N d,
    if TypicalLabel N p ((recursivePhysicalDecomposition N d).get i).weight then 0
    else ((recursivePhysicalDecomposition N d).get i).character p

theorem physicalCopyTail_eq_young_tail (N d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) :
    physicalCopyTail N d p = tailProbability (tensorYoungPMF N d p hp hs) p (shrinkingRadius N) := by
  have he := physicalCopy_expectation N d p hp hs (fun mu =>
    if ∃ a, (N : ℝ)*shrinkingRadius N ≤ |((mu a).val : ℝ)-(N : ℝ)*p a| then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at he
  rw [tailProbability, he]
  unfold physicalCopyTail
  apply Finset.sum_congr rfl
  intro i _
  have hn : (¬ TypicalLabel N p ((recursivePhysicalDecomposition N d).get i).weight) ↔
      ∃ a, (N : ℝ)*shrinkingRadius N ≤
        |(((recursivePhysicalDecomposition N d).get i).shape a).val-(N : ℝ)*p a| := by
    simp [TypicalLabel, PhysicalHighestTensor.shape]
  by_cases ht : TypicalLabel N p ((recursivePhysicalDecomposition N d).get i).weight
  · have hnot : ¬ ∃ a, (N : ℝ)*shrinkingRadius N ≤
        |(((recursivePhysicalDecomposition N d).get i).shape a).val-(N : ℝ)*p a| :=
      fun h => hn.mpr h ht
    rw [if_pos ht, if_neg hnot]
  · simp only [if_neg ht, if_pos (hn.mp ht)]

def physicalCopyTailEnvelope (d N : ℕ) : ℝ :=
  ((d : ℝ)+1)^Fintype.card (PositiveRoot d) *
    (((N : ℝ)+1)^Fintype.card (PositiveRoot d)*concentrationEnvelope d N)

theorem physicalCopyTail_le (N d : ℕ) (hN : 1 ≤ N) (p : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (horder : Antitone p) :
    physicalCopyTail N d p ≤ physicalCopyTailEnvelope d N := by
  rw [physicalCopyTail_eq_young_tail N d p hp hs]
  exact tensorYoungPMF_tail_shrinking_le N hN p hp hs horder

theorem physicalCopyTailEnvelope_tendsto_zero (d : ℕ) :
    Tendsto (physicalCopyTailEnvelope d) atTop (𝓝 0) := by
  simpa only [physicalCopyTailEnvelope, mul_zero] using
    (polynomial_concentrationEnvelope_tendsto_zero d (Fintype.card (PositiveRoot d))).const_mul
      (((d : ℝ)+1)^Fintype.card (PositiveRoot d))

end Cloning.TensorLAN
