import Cloning.TensorCartanScalarity
import Cloning.TensorCartanLieBalance
import Cloning.FiniteKrausLift

/-! Genuine CPTP Cartan channels on the actual physical cyclic sectors.
All representation, isometry and balancing inputs are constructed internally. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Kronecker
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.PCTPurificationChannel
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- The physical Cartan range projection has the exact balanced partial trace,
with the actual cyclic-sector dimension ratio. -/
theorem physicalCartanBalance
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) :
    Cloning.Compression.partialTrace
      (cartanMatrix mu nu hmu hnu * (cartanMatrix mu nu hmu hnu)ᴴ) =
    ((partitionDimension (fun i => mu i + nu i) (sumPartition_antitone mu nu hmu hnu) : ℝ) /
      (partitionDimension mu hmu : ℝ)) • (1 : Matrix (PartitionIndex mu hmu) _ ℂ) := by
  simpa only [Fintype.card_fin] using
    Cloning.TensorCartanLieBalance.balanced_partialTrace_of_lie_intertwining
      (partitionGeneratorMatrix mu hmu) (partitionGeneratorMatrix nu hnu)
      (partitionGeneratorMatrix _ (sumPartition_antitone mu nu hmu hnu))
      (cartanMatrix mu nu hmu hnu)
      (partitionGeneratorMatrix_adjoint mu hmu) (partitionGeneratorMatrix_adjoint nu hnu)
      (partitionGeneratorMatrix_adjoint _ (sumPartition_antitone mu nu hmu hnu))
      (by simpa only [Fintype.card_fin] using partitionDimension_pos mu hmu)
      (cartanMatrix_isometry mu nu hmu hnu)
      (cartanMatrix_intertwines mu nu hmu hnu)
      (partitionGeneratorMatrix_commutant_scalar mu hmu)

def physicalCartanMatrixChannel
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) :
    Cloning.Channels.MatrixChannel (PartitionIndex mu hmu)
      (PartitionIndex (fun i => mu i + nu i) (sumPartition_antitone mu nu hmu hnu)) :=
  Cloning.CartanChannel.cartanChannel (cartanMatrix mu nu hmu hnu)
    (partitionDimension mu hmu : ℝ)
    (partitionDimension _ (sumPartition_antitone mu nu hmu hnu) : ℝ)
    (Nat.cast_pos.mpr (partitionDimension_pos mu hmu))
    (Nat.cast_pos.mpr (partitionDimension_pos _ (sumPartition_antitone mu nu hmu hnu)))
    (physicalCartanBalance mu nu hmu hnu)

theorem physicalCartanMatrixChannel_apply
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (X : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) :
    (physicalCartanMatrixChannel mu nu hmu hnu).toFun X =
    Cloning.Compression.sectorMap (partitionDimension mu hmu : ℝ)
      (partitionDimension _ (sumPartition_antitone mu nu hmu hnu) : ℝ)
      (cartanMatrix mu nu hmu hnu) X :=
  Cloning.CartanChannel.cartanChannel_apply _ _ _ _ _ _ X

def physicalCartanRegisterChannel
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) :
    QuantumChannel (Register (PartitionIndex mu hmu))
      (Register (PartitionIndex (fun i => mu i + nu i) (sumPartition_antitone mu nu hmu hnu))) :=
  Cloning.FiniteKrausLift.channel
    (Cloning.CartanChannel.cartanKraus (cartanMatrix mu nu hmu hnu)
      (partitionDimension mu hmu : ℝ)
      (partitionDimension _ (sumPartition_antitone mu nu hmu hnu) : ℝ))
    (Cloning.CartanChannel.cartanKraus_normalization _ _ _
      (Nat.cast_pos.mpr (partitionDimension_pos mu hmu))
      (Nat.cast_pos.mpr (partitionDimension_pos _ (sumPartition_antitone mu nu hmu hnu)))
      (physicalCartanBalance mu nu hmu hnu))

theorem physicalCartanRegisterChannel_registerLiftCLM
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (X : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) :
    (physicalCartanRegisterChannel mu nu hmu hnu).toLinearMap (registerLiftCLM X) =
      registerLiftCLM ((physicalCartanMatrixChannel mu nu hmu hnu).toFun X) := by
  rw [physicalCartanMatrixChannel_apply]
  exact (Cloning.FiniteKrausLift.channel_registerLiftCLM _ _ X).trans
    (congrArg registerLiftCLM
      (Cloning.CartanChannel.sectorMap_eq_kraus _ X _ _ (by positivity)).symm)

/-- Physical orthonormal coordinates, as a genuine Hilbert-space equivalence. -/
def partitionRegisterEquiv (mu : Fin d → ℕ) (hmu : Antitone mu) :
    cyclicSector (partitionHighestTensor mu hmu) ≃ₗᵢ[ℂ] Register (PartitionIndex mu hmu) :=
  (partitionBasis mu hmu).repr.trans (registerBasis (PartitionIndex mu hmu)).toOrthonormalBasis.repr.symm

/-- The actual CPTP sector channel, with source and target the constructed
physical cyclic Hilbert spaces rather than abstract representation data. -/
def physicalCartanChannel
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) :
    QuantumChannel (cyclicSector (partitionHighestTensor mu hmu))
      (cyclicSector (partitionHighestTensor (fun i => mu i + nu i)
        (sumPartition_antitone mu nu hmu hnu))) :=
  (QuantumChannel.ofIsometry
    (partitionRegisterEquiv _ (sumPartition_antitone mu nu hmu hnu)).symm.toLinearIsometry).comp
    ((physicalCartanRegisterChannel mu nu hmu hnu).comp
      (QuantumChannel.ofIsometry (partitionRegisterEquiv mu hmu).toLinearIsometry))

/-- The actual trace-class operator corresponding to a complex matrix in the
physical orthonormal sector basis. -/
def partitionMatrixOperator (mu : Fin d → ℕ) (hmu : Antitone mu)
    (X : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) :
    TraceClass (cyclicSector (partitionHighestTensor mu hmu)) :=
  (QuantumChannel.ofIsometry (partitionRegisterEquiv mu hmu).symm.toLinearIsometry).toLinearMap
    (registerLiftCLM X)

theorem isometryEquiv_channel_roundtrip {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : H ≃ₗᵢ[ℂ] K) (X : TraceClass K) :
    (QuantumChannel.ofIsometry e.toLinearIsometry).toLinearMap
      ((QuantumChannel.ofIsometry e.symm.toLinearIsometry).toLinearMap X) = X := by
  apply Subtype.ext
  ext x
  have he : e.toLinearIsometry.toContinuousLinearMap.adjoint =
      e.symm.toLinearIsometry.toContinuousLinearMap := e.adjoint_eq_symm
  have hs : e.symm.toLinearIsometry.toContinuousLinearMap.adjoint =
      e.toLinearIsometry.toContinuousLinearMap := e.symm.adjoint_eq_symm
  simp only [QuantumChannel.ofIsometry_apply_coe, he, hs,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.apply_symm_apply]

/-- Exact all-input action of the genuine physical channel agrees with the
Cartan dimension-ratio formula, with no balance premise. -/
theorem physicalCartanChannel_partitionMatrixOperator
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (X : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) :
    (physicalCartanChannel mu nu hmu hnu).toLinearMap (partitionMatrixOperator mu hmu X) =
    partitionMatrixOperator _ (sumPartition_antitone mu nu hmu hnu)
      (Cloning.Compression.sectorMap (partitionDimension mu hmu : ℝ)
        (partitionDimension _ (sumPartition_antitone mu nu hmu hnu) : ℝ)
        (cartanMatrix mu nu hmu hnu) X) := by
  change (QuantumChannel.ofIsometry
    (partitionRegisterEquiv _ (sumPartition_antitone mu nu hmu hnu)).symm.toLinearIsometry).toLinearMap
    ((physicalCartanRegisterChannel mu nu hmu hnu).toLinearMap
      ((QuantumChannel.ofIsometry (partitionRegisterEquiv mu hmu).toLinearIsometry).toLinearMap
        ((QuantumChannel.ofIsometry (partitionRegisterEquiv mu hmu).symm.toLinearIsometry).toLinearMap
          (registerLiftCLM X)))) = _
  rw [isometryEquiv_channel_roundtrip, physicalCartanRegisterChannel_registerLiftCLM,
    physicalCartanMatrixChannel_apply]
  rfl

end Cloning.TensorLie
