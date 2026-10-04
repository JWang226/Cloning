import Cloning.PhysicalFlatPinchingTrace

/-! Exact inverse-dimension output moment, allowing zero target blocks. -/
noncomputable section
open scoped BigOperators Classical
namespace Cloning.PhysicalFlatConverse
open Cloning.TensorLie Cloning.TensorLAN Cloning.YoungGeneral Cloning.YoungDimensionRatio
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem rankFlat_copy_sum (n r k : ℕ) (hr : 0 < r) (f : (Fin r → ℕ) → ℝ) :
    (∑ i : SchurCopy n (r+k),
      ((recursivePhysicalDecomposition n (r+k)).get i).character (rankFlatSpectrum r k) *
        f (fun a => ((recursivePhysicalDecomposition n (r+k)).get i).weight (Fin.castAdd k a))) =
    ∑ μ : Shape r n, (tensorFlatYoungPMF n r hr μ).toReal * f (fun a => (μ a).val) := by
  let F : Shape (r+k) n → ℝ := fun μ => f (fun a => (μ (Fin.castAdd k a)).val)
  have he := TensorCloning.tensorYoungPMF_sum_eq_copies n (r+k) (rankFlatSpectrum r k)
    (rankFlatSpectrum_nonneg r k) (rankFlatSpectrum_sum hr) F
  simp only [TensorCloning.knownCopyWeight, F, PhysicalHighestTensor.shape] at he
  rw [← he]
  change (∑ μ : Shape (r+k) n, (tensorRankFlatYoungPMF n r k hr μ).toReal * F μ) = _
  rw [tensorRankFlatYoungPMF_eq_map hr, ← Cloning.YoungFlat.pmf_sum_map]
  simp only [F, padShape, Fin.append_left]

theorem rankFlat_copy_inverse_moment {n r k : ℕ} (H : PhysicalHighestTensor n (r+k)) :
    H.character (rankFlatSpectrum r k)^2 /
        ((1/(r:ℝ))^n * (partitionDimension H.weight H.weight_antitone : ℝ)) =
      H.character (rankFlatSpectrum r k) *
        (dimensionRatio r k (fun a => (H.weight (Fin.castAdd k a) : ℝ)))⁻¹ := by
  have hc : H.character (rankFlatSpectrum r k) = physicalSectorCharacter H.weight (rankFlatSpectrum r k) := by
    simp only [PhysicalHighestTensor.character, physicalSectorCharacter, dif_pos H.weight_antitone]
  by_cases hz : H.character (rankFlatSpectrum r k) = 0
  · simp [hz]
  · have ht : ∀ a : Fin k, H.weight (Fin.natAdd r a) = 0 := by
      intro a
      by_contra ha
      apply hz
      rw [hc]
      exact physicalSectorCharacter_rankFlat_zero H.weight (Fin.natAdd r a) (by simp [Fin.val_natAdd]) ha
    have he := rankFlat_highest_dimension H.weight H.weight_antitone
    rw [rankFlat_copy_highest_supported H ht, ← hc] at he
    rw [he, pow_two, mul_div_mul_left _ _ hz, div_eq_mul_inv]

/-- The output moment needed after Haar averaging uses actual copy
characters and dimensions, and equals the inverse ratio under the proved
physical rank-r Young law. -/
theorem flat_output_inverse_moment (n r k : ℕ) (hr : 0 < r) :
    (∑ i : SchurCopy n (r+k),
      ((recursivePhysicalDecomposition n (r+k)).get i).character (rankFlatSpectrum r k)^2 /
        ((1/(r:ℝ))^n * (partitionDimension ((recursivePhysicalDecomposition n (r+k)).get i).weight
          ((recursivePhysicalDecomposition n (r+k)).get i).weight_antitone : ℝ))) =
    ∑ μ : Shape r n, (tensorFlatYoungPMF n r hr μ).toReal *
      (dimensionRatio r k (fun a => ((μ a).val : ℝ)))⁻¹ := by
  simp_rw [rankFlat_copy_inverse_moment]
  exact rankFlat_copy_sum n r k hr (fun μ => (dimensionRatio r k (fun a => (μ a : ℝ)))⁻¹)

end Cloning.PhysicalFlatConverse
