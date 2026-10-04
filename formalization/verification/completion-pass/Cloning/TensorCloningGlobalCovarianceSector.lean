import Cloning.TensorCloningGlobalCovarianceAlgebra
import Cloning.TensorCloningTransitionCovariance

/-! Every actual partition transition, including its invariant replacement
branch, is covariant on all complex trace-class inputs. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Classical
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem partitionTransitionChannel_incompatible_apply (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (hc : ¬PartitionCompatible mu nu)
    (A : TraceClass (cyclicSector (partitionHighestTensor mu hmu))) :
    (partitionTransitionChannel mu nu hmu hnu).toLinearMap A =
      traceCLM A • TraceClass.ofOperator (partitionInvariantState nu hnu).op
        (partitionInvariantState nu hnu).traceClass := by
  unfold partitionTransitionChannel
  rw [dif_neg hc, QuantumChannel.ofContraction_apply, conjugation_zero]
  simp only [map_zero, sub_zero, zero_add]

/-- Literal covariance for every partition pair, without compatibility or
positivity assumptions on the complex trace-class input. -/
theorem partitionTransitionChannel_covariant_all (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1)
    (A : TraceClass (cyclicSector (partitionHighestTensor mu hmu))) :
    (partitionTransitionChannel mu nu hmu hnu).toLinearMap
      (conjugationLinearMap (partitionTensorAction mu hmu U) A) =
      conjugationLinearMap (partitionTensorAction nu hnu U)
        ((partitionTransitionChannel mu nu hmu hnu).toLinearMap A) := by
  by_cases hc : PartitionCompatible mu nu
  · exact partitionTransitionChannel_covariant mu nu hmu hnu hc U hU A
  · rw [partitionTransitionChannel_incompatible_apply mu nu hmu hnu hc,
      partitionTransitionChannel_incompatible_apply mu nu hmu hnu hc,
      partitionTensorAction_conjugation_trace mu hmu U hU, map_smul,
      partitionInvariantState_covariant nu hnu U hU]

theorem canonicalEmbedding_intertwines {n : ℕ} (H : PhysicalHighestTensor n d)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    H.canonicalEmbedding.toContinuousLinearMap.comp (partitionTensorAction H.weight H.weight_antitone X) =
      (tensorOperator n X).comp H.canonicalEmbedding.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  exact H.canonicalEmbedding_tensorOperator X x

theorem canonicalEmbedding_adjoint_intertwines {n : ℕ} (H : PhysicalHighestTensor n d)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    H.canonicalEmbedding.toContinuousLinearMap.adjoint.comp (tensorOperator n X) =
      (partitionTensorAction H.weight H.weight_antitone X).comp H.canonicalEmbedding.toContinuousLinearMap.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (canonicalEmbedding_intertwines H Xᴴ)
  simpa only [ContinuousLinearMap.adjoint_comp, partitionTensorAction,
    cyclicTensorOperator_star, tensorOperator_star, ContinuousLinearMap.adjoint_adjoint] using h.symm

theorem canonicalCompression_covariant {n : ℕ} (H : PhysicalHighestTensor n d)
    (X : Matrix (Fin d) (Fin d) ℂ) (A : TraceClass (TensorRegister n (Fin d))) :
    conjugationLinearMap H.canonicalEmbedding.toContinuousLinearMap.adjoint
      (conjugationLinearMap (tensorOperator n X) A) =
      conjugationLinearMap (partitionTensorAction H.weight H.weight_antitone X)
        (conjugationLinearMap H.canonicalEmbedding.toContinuousLinearMap.adjoint A) :=
  conjugation_intertwines _ _ _ (canonicalEmbedding_adjoint_intertwines H X) A

theorem copyTransition_covariant (n m : ℕ) (i : SchurCopy n d) (j : SchurCopy m d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1)
    (A : TraceClass ((recursivePhysicalDecomposition n d).get i).CanonicalSector) :
    (copyTransition n m d i j).toLinearMap
      (conjugationLinearMap (partitionTensorAction ((recursivePhysicalDecomposition n d).get i).weight
        ((recursivePhysicalDecomposition n d).get i).weight_antitone U) A) =
      conjugationLinearMap (tensorOperator m U) ((copyTransition n m d i j).toLinearMap A) := by
  let H := (recursivePhysicalDecomposition n d).get i
  let K := (recursivePhysicalDecomposition m d).get j
  change conjugationLinearMap K.canonicalEmbedding.toContinuousLinearMap
    ((partitionTransitionChannel H.weight K.weight H.weight_antitone K.weight_antitone).toLinearMap
      (conjugationLinearMap (partitionTensorAction H.weight H.weight_antitone U) A)) =
    conjugationLinearMap (tensorOperator m U)
      (conjugationLinearMap K.canonicalEmbedding.toContinuousLinearMap
        ((partitionTransitionChannel H.weight K.weight H.weight_antitone K.weight_antitone).toLinearMap A))
  rw [partitionTransitionChannel_covariant_all H.weight K.weight H.weight_antitone K.weight_antitone U hU]
  exact conjugation_intertwines _ _ _ (canonicalEmbedding_intertwines K U) _

end Cloning.TensorCloning
