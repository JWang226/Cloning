import Cloning.TensorLANEmbeddingSchur
import Cloning.TensorGibbsState
import Cloning.PCTPhysicalState

/-! Exact trace-class blocks of the literal physical tensor input. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical
namespace Cloning.TensorLAN
open Cloning.PCT Cloning.TensorLie Cloning.InfiniteTraceClass Cloning.Hybrid
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- The actual restricted tensor operator, regarded as a trace-class operator. -/
def canonicalTensorWeight (H : PhysicalHighestTensor n d)
    (X : Matrix (Fin d) (Fin d) ℂ) : TraceClass H.CanonicalSector :=
  TraceClass.ofOperator (H.canonicalTensorOperator X) (isTraceClass_of_finiteDimensional _)

theorem canonicalEmbedding_adjoint_self (H : PhysicalHighestTensor n d)
    (x : H.CanonicalSector) :
    H.canonicalEmbedding.toContinuousLinearMap.adjoint (H.canonicalEmbedding x) = x := by
  have h := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self
    H.canonicalEmbedding.toContinuousLinearMap).mp H.canonicalEmbedding.norm_map
  exact congrArg (fun T : H.CanonicalSector →L[ℂ] H.CanonicalSector => T x) h

/-- Compressing the literal tensor power to a physical Schur copy gives its
literal canonical representation, for every complex matrix. -/
theorem matrixTensorPower_canonical_block (H : PhysicalHighestTensor n d)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    conjugationLinearMap H.canonicalEmbedding.toContinuousLinearMap.adjoint
      (matrixTensorPower X n) = canonicalTensorWeight H X := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  change H.canonicalEmbedding.toContinuousLinearMap.adjoint
    (tensorOperator n X (H.canonicalEmbedding.toContinuousLinearMap.adjoint.adjoint x)) = _
  rw [ContinuousLinearMap.adjoint_adjoint]
  change H.canonicalEmbedding.toContinuousLinearMap.adjoint
    (tensorOperator n X (H.canonicalEmbedding x)) = H.canonicalTensorOperator X x
  rw [← H.canonicalEmbedding_tensorOperator, canonicalEmbedding_adjoint_self]

/-- The complete physical tensor is the sum of its embedded canonical blocks.
The identity is an equality of actual trace-class operators. -/
theorem matrixTensorPower_eq_sum_canonical_blocks
    (L : List (PhysicalHighestTensor n d))
    (hL : OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
      (fun i => (L.get i).sector.subtypeₗᵢ))
    (hspan : (⨆ i : Fin L.length, (L.get i).sector) = ⊤)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    matrixTensorPower X n = ∑ i : Fin L.length,
      conjugationLinearMap (L.get i).canonicalEmbedding.toContinuousLinearMap
        (canonicalTensorWeight (L.get i) X) := by
  apply Subtype.ext
  change (matrixTensorPower X n).1 = inclusionCLM (∑ i : Fin L.length, _)
  rw [map_sum]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.sum_apply, inclusionCLM_apply, conjugationLinearMap_coe,
    operatorConjugation_apply, canonicalTensorWeight, TraceClass.ofOperator_coe]
  change tensorOperator n X x = ∑ i : Fin L.length,
    (L.get i).canonicalEmbedding ((L.get i).canonicalTensorOperator X
      ((L.get i).canonicalEmbedding.toContinuousLinearMap.adjoint x))
  simp_rw [PhysicalHighestTensor.canonicalEmbedding_tensorOperator, ← map_sum]
  congr 1
  have hcoord := hilbertSum_adjoint_eq_coordinate
    (fun i : Fin L.length => (L.get i).canonicalEmbedding)
    (canonicalSectorHilbertSum L hL hspan)
  simp_rw [hcoord]
  exact (by
    simpa only [LinearIsometryEquiv.symm_apply_apply] using
      physicalSchurIsometry_symm_apply L hL hspan (physicalSchurIsometry L hL hspan x))

@[simp] theorem canonicalTensorWeight_diagonal (H : PhysicalHighestTensor n d)
    (p : Fin d → ℝ) :
    canonicalTensorWeight H (Matrix.diagonal (fun a => (p a : ℂ))) =
      sectorGibbsWeight (partitionHighestTensor H.weight H.weight_antitone) H.weight
        (partitionHighestTensor_cartan H.weight H.weight_antitone)
        (partitionHighestTensor_raising_zero H.weight H.weight_antitone) p := rfl

/-- Normalization only changes the positive block by its actual partition
function; no presumed spectral decomposition enters this identity. -/
theorem sectorGibbsWeight_eq_partition_smul_state
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (hΩ : ‖Ω‖ = 1) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) :
    sectorGibbsWeight Ω mu hweight hraise p =
      (sectorPartitionFunction Ω mu hweight hraise p : ℂ) •
        TraceClass.ofOperator (sectorGibbsState Ω mu hweight hraise hΩ p hp).op
          (sectorGibbsState Ω mu hweight hraise hΩ p hp).traceClass := by
  apply Subtype.ext
  change sectorGibbsOperator Ω mu hweight hraise p =
    (sectorPartitionFunction Ω mu hweight hraise p : ℂ) •
      (((sectorPartitionFunction Ω mu hweight hraise p)⁻¹ : ℝ) : ℂ) •
        sectorGibbsOperator Ω mu hweight hraise p
  have hc : (sectorPartitionFunction Ω mu hweight hraise p : ℂ) *
      (((sectorPartitionFunction Ω mu hweight hraise p)⁻¹ : ℝ) : ℂ) = 1 := by
    exact_mod_cast mul_inv_cancel₀ (sectorPartitionFunction_pos Ω mu hweight hraise hΩ p hp).ne'
  rw [smul_smul (sectorPartitionFunction Ω mu hweight hraise p : ℂ)
    (((sectorPartitionFunction Ω mu hweight hraise p)⁻¹ : ℝ) : ℂ)
    (sectorGibbsOperator Ω mu hweight hraise p), hc]
  exact (one_smul ℂ (sectorGibbsOperator Ω mu hweight hraise p)).symm

end Cloning.TensorLAN
