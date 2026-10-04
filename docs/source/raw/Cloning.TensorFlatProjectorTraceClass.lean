import Cloning.TensorFlatProjectorFidelity
import Cloning.TensorCartanStateOperator
import Cloning.HybridStates

/-! Physical trace-class flat states and the exact Cartan fidelity adapter. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix ComplexOrder
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner Cloning.Hybrid
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def partitionMatrixState (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) (hM : M.PosSemidef) :
    PositiveTraceClass (cyclicSector (partitionHighestTensor mu hmu)) :=
  ⟨matrixLift (partitionBasis mu hmu) M, ofMatrix_nonneg (partitionBasis mu hmu).orthonormal hM⟩

theorem partitionMatrixState_fidelity (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M N : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ)
    (hM : M.PosSemidef) (hN : N.PosSemidef) :
    (partitionMatrixState mu hmu M hM).rootFidelity (partitionMatrixState mu hmu N hN) =
      Cloning.MatrixFidelity.fidelity M N :=
  fidelity_ofMatrix (partitionBasis mu hmu).orthonormal hM hN

theorem physicalCartanMatrixChannel_positive (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) (hM : M.PosSemidef) :
    ((physicalCartanMatrixChannel mu nu hmu hnu).toFun M).PosSemidef := by
  rw [physicalCartanMatrixChannel_apply, Cloning.CartanChannel.sectorMap_eq_kraus _ _ _ _ (by positivity)]
  exact Cloning.Channels.krausMap_positive _ hM

/-- Actual trace-class channel fidelity agrees with its proved finite matrix formula. -/
theorem physicalCartanChannel_partitionMatrix_fidelity (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) (hM : M.PosSemidef)
    (N : Matrix (PartitionIndex (fun a => mu a + nu a) (sumPartition_antitone mu nu hmu hnu)) _ ℂ)
    (hN : N.PosSemidef) :
    ((partitionMatrixState mu hmu M hM).map
      (physicalCartanChannel mu nu hmu hnu).toPositiveTracePreservingMap).rootFidelity
      (partitionMatrixState _ (sumPartition_antitone mu nu hmu hnu) N hN) =
        Cloning.MatrixFidelity.fidelity ((physicalCartanMatrixChannel mu nu hmu hnu).toFun M) N := by
  have he : (partitionMatrixState mu hmu M hM).map
      (physicalCartanChannel mu nu hmu hnu).toPositiveTracePreservingMap =
      partitionMatrixState _ (sumPartition_antitone mu nu hmu hnu)
        ((physicalCartanMatrixChannel mu nu hmu hnu).toFun M)
        (physicalCartanMatrixChannel_positive mu nu hmu hnu M hM) := by
    apply Subtype.ext
    change (physicalCartanChannel mu nu hmu hnu).toLinearMap (matrixLift (partitionBasis mu hmu) M) = _
    rw [← partitionMatrixOperator_eq_matrixLift, physicalCartanChannel_partitionMatrixOperator,
      partitionMatrixOperator_eq_matrixLift]
    simp only [partitionMatrixState, physicalCartanMatrixChannel_apply]
  rw [he, partitionMatrixState_fidelity]

def rankFlatSectorState (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :=
  partitionMatrixState (padPartition mu k) (padPartition_antitone mu hmu k)
    (rankFlatSectorDensity mu hmu k) (rankFlatSectorDensity_posSemidef mu hmu k)

theorem rankFlatSectorState_norm (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    ‖(rankFlatSectorState mu hmu k).1‖ = 1 := by
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ (rankFlatSectorState mu hmu k).2]
  change (trace (ofMatrix (partitionBasis _ _) (rankFlatSectorDensity mu hmu k)) _).re = _
  rw [trace_ofMatrix (partitionBasis _ _).orthonormal, rankFlatSectorDensity_trace]
  rfl

/-- The literal rank-flat Gibbs block is its physical character times the
constructed normalized support state, including the zero-fold tensor. -/
theorem partitionActionMatrix_rankFlat (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    partitionActionMatrix (padPartition mu k) (padPartition_antitone mu hmu k)
      (Matrix.diagonal (fun a => (rankFlatSpectrum r k a : ℂ))) =
      physicalSectorCharacter (padPartition mu k) (rankFlatSpectrum r k) • rankFlatSectorDensity mu hmu k := by
  have he : partitionActionMatrix (padPartition mu k) (padPartition_antitone mu hmu k)
      (Matrix.diagonal (fun a => (rankFlatSpectrum r k a : ℂ))) =
      ((1/(r:ℝ))^(∑a,mu a)) •
        partitionCoordinateProjection (padPartition mu k) (padPartition_antitone mu hmu k) := by
    ext i j
    rw [partitionActionMatrix_apply]
    change ⟪partitionBasis _ _ i, sectorGibbsOperator _ _ _ _ _ (partitionBasis _ _ j)⟫_ℂ = _
    rw [sectorGibbsOperator_rankFlat mu hmu k, ContinuousLinearMap.smul_apply, inner_smul_right]
    simp only [Matrix.smul_apply, Complex.real_smul, partitionCoordinateProjection,
      partitionActionMatrix_apply]
    rfl
  rw [he, rankFlatSectorDensity, smul_smul, physicalSectorCharacter_rankFlat mu hmu k]
  congr 1
  have hD : (partitionDimension mu hmu : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (partitionDimension_pos mu hmu).ne'
  rw [one_div_pow]
  field_simp

end Cloning.TensorLie
