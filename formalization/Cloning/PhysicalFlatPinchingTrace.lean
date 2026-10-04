import Cloning.PhysicalFlatPinchingInflation
import Cloning.TensorCloningAchievabilityProbability
import Cloning.YoungFlatFidelityBounds

/-! The trace of the actual supported inflated input is exactly the physical
rank-flat expectation of the ambient/support dimension ratio. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical ComplexOrder
namespace Cloning.PhysicalFlatConverse
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass
open Cloning.YoungGeneral Cloning.YoungDimensionRatio
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem rankFlat_highest_pad {r : ℕ} (μ : Fin r → ℕ) (k : ℕ) :
    (∏ a, rankFlatSpectrum r k a ^ padPartition μ k a) = (1/(r:ℝ)) ^ (∑ a,μ a) := by
  rw [Fin.prod_univ_add]
  simp only [padPartition_left, padPartition_right, pow_zero, Finset.prod_const_one, mul_one]
  have he (a : Fin r) : rankFlatSpectrum r k (Fin.castAdd k a) = 1/(r:ℝ) := by
    simp [rankFlatSpectrum, a.isLt]
  simp only [he]
  rw [Finset.prod_pow_eq_pow_sum]

theorem rankFlat_highest_dimension_pad {r : ℕ} (μ : Fin r → ℕ) (hμ : Antitone μ) (k : ℕ) :
    (∏ a, rankFlatSpectrum r k a ^ padPartition μ k a) *
      (partitionDimension (padPartition μ k) (padPartition_antitone μ hμ k) : ℝ) =
    physicalSectorCharacter (padPartition μ k) (rankFlatSpectrum r k) *
      dimensionRatio r k (fun a => (μ a : ℝ)) := by
  rw [rankFlat_highest_pad, physicalSectorCharacter_rankFlat μ hμ k, ← partitionDimension_pad_ratio μ hμ k,
    one_div_pow]
  have hD : (partitionDimension μ hμ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (partitionDimension_pos μ hμ).ne'
  field_simp

/-- The scalar identity also holds on unsupported partitions: both sides
vanish there because the literal rank-flat tensor has a zero eigenvalue. -/
theorem rankFlat_highest_dimension {r k : ℕ} (μ : Fin (r+k) → ℕ) (hμ : Antitone μ) :
    (∏ a, rankFlatSpectrum r k a ^ μ a) * (partitionDimension μ hμ : ℝ) =
      physicalSectorCharacter μ (rankFlatSpectrum r k) *
        dimensionRatio r k (fun a => (μ (Fin.castAdd k a) : ℝ)) := by
  by_cases ht : ∀ a : Fin k, μ (Fin.natAdd r a) = 0
  · let ν : Fin r → ℕ := fun a => μ (Fin.castAdd k a)
    have hν : Antitone ν := fun a b hab => hμ (show Fin.castAdd k a ≤ Fin.castAdd k b from hab)
    have he : padPartition ν k = μ := by
      funext a
      induction a using Fin.addCases with
      | left a => simp only [padPartition_left, ν]
      | right a => simpa only [padPartition_right] using (ht a).symm
    have hh := rankFlat_highest_dimension_pad ν hν k
    simpa only [he, ν] using hh
  · push_neg at ht
    obtain ⟨a,ha⟩ := ht
    have hc := physicalSectorCharacter_rankFlat_zero μ (Fin.natAdd r a) (by simp [Fin.val_natAdd]) ha
    have hz : (∏ b, rankFlatSpectrum r k b ^ μ b) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ (Fin.natAdd r a))
      simp [rankFlatSpectrum, Fin.val_natAdd, ha]
    rw [hz,hc,zero_mul,zero_mul]

/-- The inflation coefficient is exactly r^(-n) on every supported copy. -/
theorem rankFlat_copy_highest_supported {n r k : ℕ} (H : PhysicalHighestTensor n (r+k))
    (ht : ∀ a : Fin k, H.weight (Fin.natAdd r a) = 0) :
    (∏ a, rankFlatSpectrum r k a ^ H.weight a) = (1/(r:ℝ))^n := by
  let μ : Fin r → ℕ := fun a => H.weight (Fin.castAdd k a)
  have he : padPartition μ k = H.weight := by
    funext a
    induction a using Fin.addCases with
    | left a => simp only [padPartition_left, μ]
    | right a => simpa only [padPartition_right] using (ht a).symm
  have hs : ∑ a,μ a = n := by
    rw [← sum_padPartition μ k, he, H.weight_sum]
  rw [← he,rankFlat_highest_pad,hs]

theorem rankFlat_copy_highest_unsupported {n r k : ℕ} (H : PhysicalHighestTensor n (r+k))
    (ht : ¬ ∀ a : Fin k, H.weight (Fin.natAdd r a) = 0) :
    (∏ a, rankFlatSpectrum r k a ^ H.weight a) = 0 := by
  push_neg at ht
  obtain ⟨a,ha⟩ := ht
  apply Finset.prod_eq_zero (Finset.mem_univ (Fin.natAdd r a))
  simp [rankFlatSpectrum, Fin.val_natAdd, ha]

/-- Exact physical trace, including multiplicities and the padded rank-r
Young law. No classical probability law is assumed. -/
theorem flatInflatedInput_trace (n r k : ℕ) (hr : 0 < r) :
    (traceCLM (flatInflatedInput n r k)).re =
      ∑ μ : Shape r n, (tensorFlatYoungPMF n r hr μ).toReal *
        dimensionRatio r k (fun a => ((μ a).val : ℝ)) := by
  rw [flatInflatedInput, inflatedTensor_trace]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  simp_rw [rankFlat_highest_dimension]
  let f : Shape (r+k) n → ℝ := fun μ => dimensionRatio r k (fun a => ((μ (Fin.castAdd k a)).val : ℝ))
  have he := TensorCloning.tensorYoungPMF_sum_eq_copies n (r+k) (rankFlatSpectrum r k)
    (rankFlatSpectrum_nonneg r k) (rankFlatSpectrum_sum hr) f
  have hc (i : SchurCopy n (r+k)) :
      TensorCloning.knownCopyWeight n (r+k) (rankFlatSpectrum r k) i =
        physicalSectorCharacter ((recursivePhysicalDecomposition n (r+k)).get i).weight
          (rankFlatSpectrum r k) := by
    simp only [TensorCloning.knownCopyWeight, PhysicalHighestTensor.character,
      physicalSectorCharacter, dif_pos ((recursivePhysicalDecomposition n (r+k)).get i).weight_antitone]
  simp only [hc, f, PhysicalHighestTensor.shape] at he
  rw [← he]
  change (∑ μ : Shape (r+k) n, (tensorRankFlatYoungPMF n r k hr μ).toReal * f μ) = _
  rw [tensorRankFlatYoungPMF_eq_map hr]
  rw [← Cloning.YoungFlat.pmf_sum_map]
  simp only [f, padShape, Fin.append_left]

end Cloning.PhysicalFlatConverse
