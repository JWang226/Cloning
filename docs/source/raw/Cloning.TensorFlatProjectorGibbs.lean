import Cloning.TensorFlatProjectorTraceClass
import Cloning.TensorLANEmbeddingSchurState

/-! Exact physical Gibbs mixtures at nonnegative spectra, including zero eigenvalues. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Matrix
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.Hybrid
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite
variable (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)

theorem sectorGibbsDensity_nonneg_of_nonneg (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) :
    0 ≤ (sectorGibbsDensity Ω mu hweight hraise p).1 := by
  change 0 ≤ (((sectorPartitionFunction Ω mu hweight hraise p)⁻¹ : ℝ) : ℂ) •
    (sectorGibbsWeight Ω mu hweight hraise p).1
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  apply ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (sectorGibbsWeight_nonneg Ω mu hweight hraise p hp)).smul_of_nonneg
  exact_mod_cast inv_nonneg.mpr (norm_nonneg (sectorGibbsWeight Ω mu hweight hraise p))

/-- Scalar reconstruction also holds for zero blocks, whose actual weight is zero. -/
theorem sectorGibbsWeight_eq_partition_smul_density (p : Fin d → ℝ) :
    sectorGibbsWeight Ω mu hweight hraise p =
      (sectorPartitionFunction Ω mu hweight hraise p : ℂ) • sectorGibbsDensity Ω mu hweight hraise p := by
  by_cases hz : sectorGibbsWeight Ω mu hweight hraise p = 0
  · simp [sectorGibbsDensity, hz]
  · rw [sectorGibbsDensity, sectorPartitionFunction, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), Complex.ofReal_one, one_smul]

theorem sectorGibbsDensity_norm_le_one (p : Fin d → ℝ) :
    ‖sectorGibbsDensity Ω mu hweight hraise p‖ ≤ 1 := by
  rw [sectorGibbsDensity, sectorPartitionFunction, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  change ‖sectorGibbsWeight Ω mu hweight hraise p‖⁻¹ * ‖sectorGibbsWeight Ω mu hweight hraise p‖ ≤ 1
  by_cases hz : sectorGibbsWeight Ω mu hweight hraise p = 0
  · simp [hz]
  · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]

end Cloning.TensorLie

namespace Cloning.TensorLAN
open Cloning.PCT Cloning.TensorLie Cloning.InfiniteTraceClass Cloning.Hybrid
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem canonicalTensorWeight_rotated_diagonal_nonneg (H : PhysicalHighestTensor n d)
    (U : Matrix (Fin d) (Fin d) ℂ) (p : Fin d → ℝ) :
    canonicalTensorWeight H (U * Matrix.diagonal (fun a => (p a : ℂ)) * Uᴴ) =
      (H.character p : ℂ) • canonicalRotatedGibbs H U p := by
  rw [canonicalTensorWeight_conjugate, canonicalTensorWeight_diagonal,
    sectorGibbsWeight_eq_partition_smul_density, map_smul]
  rfl

theorem canonicalRotatedGibbs_nonneg_of_nonneg (H : PhysicalHighestTensor n d)
    (U : Matrix (Fin d) (Fin d) ℂ) (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) :
    0 ≤ (canonicalRotatedGibbs H U p).1 :=
  conjugationLinearMap_nonneg _ _ (sectorGibbsDensity_nonneg_of_nonneg _ _ _ _ p hp)

theorem canonicalRotatedGibbs_norm_le_one (H : PhysicalHighestTensor n d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1) (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) :
    ‖canonicalRotatedGibbs H U p‖ ≤ 1 := by
  let V := cyclicUnitary (partitionHighestTensor H.weight H.weight_antitone)
    (fun a => (H.weight a : ℂ)) (partitionHighestTensor_cartan _ _)
    (partitionHighestTensor_raising_zero _ _) U hU
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ (canonicalRotatedGibbs_nonneg_of_nonneg H U p hp)]
  change (traceCLM (conjugationLinearMap V.toLinearIsometry.toContinuousLinearMap (canonicalGibbsDensity H p))).re ≤ 1
  rw [conjugationLinearMap_isometry_trace]
  have hn : 0 ≤ (canonicalGibbsDensity H p).1 := sectorGibbsDensity_nonneg_of_nonneg
    (partitionHighestTensor H.weight H.weight_antitone) H.weight
    (partitionHighestTensor_cartan _ _) (partitionHighestTensor_raising_zero _ _) p hp
  change (trace (canonicalGibbsDensity H p).1 (canonicalGibbsDensity H p).2).re ≤ 1
  rw [← TraceClass.norm_eq_trace_re_of_nonneg _ hn]
  exact sectorGibbsDensity_norm_le_one _ _ _ _ p

/-- The full physical tensor-state mixture includes arbitrary zero eigenvalues. -/
theorem matrixTensorPower_rotated_eq_copy_mixture_nonneg
    (U : Matrix (Fin d) (Fin d) ℂ) (p : Fin d → ℝ) :
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
  rw [canonicalTensorWeight_rotated_diagonal_nonneg, map_smul]

end Cloning.TensorLAN
