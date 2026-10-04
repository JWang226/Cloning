import Cloning.TensorLANEmbeddingCellRecovery
import Cloning.TensorLANEmbeddingSchurState

/-! Quantitative bounds for the literal complete physical channels, including
the exact rotated tensor block law and reverse cell reconstruction. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace Matrix
open MeasureTheory Filter
namespace Cloning.TensorLAN
open Cloning.YoungHyperplane Cloning.TensorLie Cloning.PCTJointGaussianWhitening
open Cloning.Hybrid Cloning.InfiniteTraceClass Cloning.PCT
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite
variable (p : Fin (d+1) → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (d+1)) ℝ (EuclideanSpace ℝ (Fin (d+1))))
    (hb : b 0 = sqrtSpectrum p)

theorem physicalCellForward_rotated (N R : ℕ) (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (r : Fin (d+1) → ℝ) (hr : ∀ a, 0 < r a) :
    (physicalCellForward p hp b hb N R).map
      (matrixTensorPower (U*Matrix.diagonal (fun a => (r a : ℂ))*Uᴴ) N) =
    ∑ i : SchurCopy N (d+1), prepareL1 (μ := (volume : Measure (Fin d → ℝ))) (physicalCellDensity p hp b hb N i)
      (physicalCellDensity_integrable p hp b hb N i)
      ((((recursivePhysicalDecomposition N (d+1)).get i).character r : ℂ) •
        (copyToFock N (d+1) R i).toLinearMap
          (canonicalRotatedGibbs ((recursivePhysicalDecomposition N (d+1)).get i) U r)) := by
  have he := schurForward_apply N (d+1) R (physicalCellDensity p hp b hb N)
    (physicalCellDensity_integrable p hp b hb N)
    (physicalCellDensity_nonneg p hp b hb N)
    (physicalCellDensity_integral p hp b hb N)
    (matrixTensorPower (U*Matrix.diagonal (fun a => (r a : ℂ))*Uᴴ) N)
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  let H := (recursivePhysicalDecomposition N (d+1)).get i
  have hblock := (matrixTensorPower_canonical_block H
    (U*Matrix.diagonal (fun a => (r a : ℂ))*Uᴴ)).trans
      (canonicalTensorWeight_rotated_diagonal H U r hr)
  exact congrArg (prepareL1 (physicalCellDensity p hp b hb N i)
    (physicalCellDensity_integrable p hp b hb N i))
      ((congrArg (copyToFock N (d+1) R i).toLinearMap hblock).trans
        ((copyToFock N (d+1) R i).toLinearMap.map_smul _ _))

theorem physicalCellForward_rotated_error (N R : ℕ)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (r : Fin (d+1) → ℝ) (hr : ∀ a, 0 < r a)
    (σ : TraceClass (RootFock (d+1))) (f : (Fin d → ℝ) → ℝ) (hf : Integrable f (volume : Measure (Fin d → ℝ))) :
    ‖(physicalCellForward p hp b hb N R).map
      (matrixTensorPower (U*Matrix.diagonal (fun a => (r a : ℂ))*Uᴴ) N)-prepareL1 f hf σ‖ ≤
      (∑ i : SchurCopy N (d+1), ((recursivePhysicalDecomposition N (d+1)).get i).character r *
        ‖(copyToFock N (d+1) R i).toLinearMap
          (canonicalRotatedGibbs ((recursivePhysicalDecomposition N (d+1)).get i) U r)-σ‖) +
      (∫ y, |physicalLabelDensity p hp b hb N r y-f y|)*‖σ‖ := by
  rw [physicalCellForward_rotated p hp b hb N R U r hr]
  exact finite_prepared_mixture_error _ (fun i => PhysicalHighestTensor.character_nonneg _ _)
    _ (physicalCellDensity_integrable p hp b hb N) (physicalCellDensity_nonneg p hp b hb N)
    (physicalCellDensity_integral p hp b hb N) _ σ f hf

theorem fockToCopy_error_le (N R : ℕ) (i : SchurCopy N (d+1))
    (A : TraceClass ((recursivePhysicalDecomposition N (d+1)).get i).CanonicalSector)
    (σ : TraceClass (RootFock (d+1))) :
    ‖(fockToCopy N (d+1) R i).toLinearMap σ -
      conjugationLinearMap ((recursivePhysicalDecomposition N (d+1)).get i).canonicalEmbedding.toContinuousLinearMap A‖ ≤
      2*‖(fockToSectorTotal
        (partitionHighestTensor ((recursivePhysicalDecomposition N (d+1)).get i).weight
          ((recursivePhysicalDecomposition N (d+1)).get i).weight_antitone)
        ((recursivePhysicalDecomposition N (d+1)).get i).weight R
        (partitionHighestTensor_norm _ _)).toLinearMap σ-A‖ := by
  let H := (recursivePhysicalDecomposition N (d+1)).get i
  change ‖conjugationLinearMap H.canonicalEmbedding.toContinuousLinearMap _-
    conjugationLinearMap H.canonicalEmbedding.toContinuousLinearMap A‖ ≤ _
  rw [← map_sub]
  exact (QuantumChannel.ofIsometry H.canonicalEmbedding).toPositiveTracePreservingMap.norm_map_le_two_mul _

theorem physicalCellReverse_rotated_error (N R : ℕ) (hN : 0 < N)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (r : Fin (d+1) → ℝ) (hr : ∀ a, 0 < r a) (hs : ∑ a, r a = 1)
    (σ : TraceClass (RootFock (d+1))) (f : (Fin d → ℝ) → ℝ) (hf : Integrable f (volume : Measure (Fin d → ℝ))) :
    ‖(physicalCellReverse p hp b hb N R).map (prepareL1 f hf σ)-
      matrixTensorPower (U*Matrix.diagonal (fun a => (r a : ℂ))*Uᴴ) N‖ ≤
    2*(∑ i : SchurCopy N (d+1), ((recursivePhysicalDecomposition N (d+1)).get i).character r *
      ‖(fockToSectorTotal
        (partitionHighestTensor ((recursivePhysicalDecomposition N (d+1)).get i).weight
          ((recursivePhysicalDecomposition N (d+1)).get i).weight_antitone)
        ((recursivePhysicalDecomposition N (d+1)).get i).weight R
        (partitionHighestTensor_norm _ _)).toLinearMap σ-
          canonicalRotatedGibbs ((recursivePhysicalDecomposition N (d+1)).get i) U r‖) +
    2*(∫ y, |physicalLabelDensity p hp b hb N r y-f y|)*‖σ‖ := by
  let F := physicalLabelDensity p hp b hb N r
  let hF := physicalLabelDensity_integrable p hp b hb N r
  let S := physicalCellReverse p hp b hb N R
  let T := matrixTensorPower (U*Matrix.diagonal (fun a => (r a : ℂ))*Uᴴ) N
  have ht := norm_sub_le_norm_sub_add_norm_sub (S.map (prepareL1 f hf σ))
    (S.map (prepareL1 F hF σ)) T
  have hc : ‖S.map (prepareL1 f hf σ)-S.map (prepareL1 F hF σ)‖ ≤
      2*(∫ y, |F y-f y|)*‖σ‖ := by
    calc
      _ = ‖S.map (prepareL1 f hf σ-prepareL1 F hF σ)‖ :=
        congrArg norm (S.map.map_sub _ _).symm
      _ ≤ 2*‖prepareL1 f hf σ-prepareL1 F hF σ‖ := S.norm_le_two _
      _ = 2*((∫ y, |f y-F y|)*‖σ‖) :=
        congrArg (fun x : ℝ => 2*x) (prepareL1_density_difference_norm f F hf hF σ)
      _ = _ := by
        rw [show (fun y => |f y-F y|) = (fun y => |F y-f y|) from
          funext fun _ => abs_sub_comm _ _]
        ring
  have hq : ‖S.map (prepareL1 F hF σ)-T‖ ≤
      2*(∑ i : SchurCopy N (d+1), ((recursivePhysicalDecomposition N (d+1)).get i).character r *
        ‖(fockToSectorTotal
          (partitionHighestTensor ((recursivePhysicalDecomposition N (d+1)).get i).weight
            ((recursivePhysicalDecomposition N (d+1)).get i).weight_antitone)
          ((recursivePhysicalDecomposition N (d+1)).get i).weight R
          (partitionHighestTensor_norm _ _)).toLinearMap σ-
            canonicalRotatedGibbs ((recursivePhysicalDecomposition N (d+1)).get i) U r‖) := by
    dsimp only [S,F,hF,T]
    rw [physicalCellReverse_prepare_physicalLabelDensity p hp b hb N R hN r (fun a => (hr a).le) hs,
      matrixTensorPower_rotated_eq_copy_mixture (n := N) U r hr, ← Finset.sum_sub_distrib]
    simp_rw [← smul_sub]
    apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    let H := (recursivePhysicalDecomposition N (d+1)).get i
    let A := canonicalRotatedGibbs H U r
    let D := (fockToCopy N (d+1) R i).toLinearMap σ-
      conjugationLinearMap H.canonicalEmbedding.toContinuousLinearMap A
    have hw : ‖(H.character r : ℂ)‖ = H.character r := by
      exact (Complex.norm_real _).trans (Real.norm_of_nonneg (H.character_nonneg r))
    have hi := mul_le_mul_of_nonneg_left (fockToCopy_error_le N R i A σ) (H.character_nonneg r)
    calc
      ‖(H.character r : ℂ) • D‖ = ‖(H.character r : ℂ)‖*‖D‖ := norm_smul _ _
      _ = H.character r*‖D‖ := congrArg (fun x : ℝ => x*‖D‖) hw
      _ ≤ _ := hi
      _ = _ := by ring
  exact ht.trans ((add_le_add hc hq).trans_eq (by ring))

end Cloning.TensorLAN
