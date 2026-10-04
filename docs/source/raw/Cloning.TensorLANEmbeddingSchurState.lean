import Cloning.TensorLANEmbeddingSchurWeights
import Cloning.TensorGibbsCutoffState

/-! The literal local quantum experiment is an exact finite mixture of its
actual normalized physical Gibbs sectors. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical ComplexOrder Matrix
namespace Cloning.TensorLAN
open Cloning.PCT Cloning.TensorLie Cloning.InfiniteTraceClass Cloning.Hybrid
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def canonicalGibbsDensity (H : PhysicalHighestTensor n d) (p : Fin d → ℝ) :
    TraceClass H.CanonicalSector :=
  sectorGibbsDensity (partitionHighestTensor H.weight H.weight_antitone) H.weight
    (partitionHighestTensor_cartan H.weight H.weight_antitone)
    (partitionHighestTensor_raising_zero H.weight H.weight_antitone) p

def canonicalRotatedGibbs (H : PhysicalHighestTensor n d)
    (U : Matrix (Fin d) (Fin d) ℂ) (p : Fin d → ℝ) : TraceClass H.CanonicalSector :=
  conjugationLinearMap (H.canonicalTensorOperator U) (canonicalGibbsDensity H p)

theorem canonicalTensorWeight_conjugate (H : PhysicalHighestTensor n d)
    (U X : Matrix (Fin d) (Fin d) ℂ) :
    canonicalTensorWeight H (U * X * Uᴴ) =
      conjugationLinearMap (H.canonicalTensorOperator U) (canonicalTensorWeight H X) := by
  apply Subtype.ext
  change H.canonicalTensorOperator (U * X * Uᴴ) =
    operatorConjugation (H.canonicalTensorOperator U) (H.canonicalTensorOperator X)
  unfold PhysicalHighestTensor.canonicalTensorOperator
  rw [cyclicTensorOperator_mul, cyclicTensorOperator_mul, cyclicTensorOperator_star]
  rfl

/-- The true block has its actual trace weight multiplying its normalized
rotated sector state. -/
theorem canonicalTensorWeight_rotated_diagonal (H : PhysicalHighestTensor n d)
    (U : Matrix (Fin d) (Fin d) ℂ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) :
    canonicalTensorWeight H (U * Matrix.diagonal (fun a => (p a : ℂ)) * Uᴴ) =
      (H.character p : ℂ) • canonicalRotatedGibbs H U p := by
  rw [canonicalTensorWeight_conjugate, canonicalTensorWeight_diagonal,
    sectorGibbsWeight_eq_partition_smul_state _ _ _ _
      (partitionHighestTensor_norm H.weight H.weight_antitone) p hp, map_smul]
  rfl

theorem canonicalRotatedGibbs_nonneg (H : PhysicalHighestTensor n d)
    (U : Matrix (Fin d) (Fin d) ℂ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) :
    0 ≤ (canonicalRotatedGibbs H U p).1 :=
  conjugationLinearMap_nonneg _ _
    (sectorGibbsDensity_nonneg _ _ _ _
      (partitionHighestTensor_norm H.weight H.weight_antitone) p hp)

theorem canonicalRotatedGibbs_norm (H : PhysicalHighestTensor n d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) : ‖canonicalRotatedGibbs H U p‖ = 1 := by
  let V := cyclicUnitary (partitionHighestTensor H.weight H.weight_antitone)
    (fun a => (H.weight a : ℂ))
    (partitionHighestTensor_cartan H.weight H.weight_antitone)
    (partitionHighestTensor_raising_zero H.weight H.weight_antitone) U hU
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ (canonicalRotatedGibbs_nonneg H U p hp)]
  change (traceCLM (conjugationLinearMap V.toLinearIsometry.toContinuousLinearMap
    (canonicalGibbsDensity H p))).re = 1
  rw [conjugationLinearMap_isometry_trace]
  change (traceCLM (sectorGibbsDensity _ _ _ _ p)).re = 1
  rw [sectorGibbsDensity_trace _ _ _ _ (partitionHighestTensor_norm H.weight H.weight_antitone) p hp]
  rfl

/-- Exact trace-class mixture on the full physical tensor register. -/
theorem matrixTensorPower_rotated_eq_copy_mixture
    (U : Matrix (Fin d) (Fin d) ℂ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) :
    matrixTensorPower (U * Matrix.diagonal (fun a => (p a : ℂ)) * Uᴴ) n =
      ∑ i : SchurCopy n d,
        (((recursivePhysicalDecomposition n d).get i).character p : ℂ) •
          conjugationLinearMap
            ((recursivePhysicalDecomposition n d).get i).canonicalEmbedding.toContinuousLinearMap
            (canonicalRotatedGibbs ((recursivePhysicalDecomposition n d).get i) U p) := by
  rw [matrixTensorPower_eq_sum_canonical_blocks (recursivePhysicalDecomposition n d)
    (recursivePhysicalDecomposition_is_decomposition n d).1
    (recursivePhysicalDecomposition_is_decomposition n d).2]
  apply Finset.sum_congr rfl
  intro i _
  rw [canonicalTensorWeight_rotated_diagonal _ U p hp, map_smul]

end Cloning.TensorLAN
