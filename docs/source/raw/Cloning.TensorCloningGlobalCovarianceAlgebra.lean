import Cloning.TensorCloningGlobalCovarianceState
import Cloning.TensorCartanTensorAction
import Cloning.InfiniteIsometricChannel

/-! Exact covariance algebra on arbitrary complex trace-class inputs. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Classical
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
section Algebra
variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

theorem conjugation_comp_eq (V : K →L[ℂ] L) (W : H →L[ℂ] K) (A : TraceClass H) :
    conjugationLinearMap V (conjugationLinearMap W A) = conjugationLinearMap (V.comp W) A := by
  apply Subtype.ext
  ext x
  simp only [conjugationLinearMap_coe, operatorConjugation_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_comp]

theorem conjugation_intertwines (V : H →L[ℂ] K) (S : H →L[ℂ] H) (T : K →L[ℂ] K)
    (h : V.comp S = T.comp V) (A : TraceClass H) :
    conjugationLinearMap V (conjugationLinearMap S A) =
      conjugationLinearMap T (conjugationLinearMap V A) := by
  rw [conjugation_comp_eq, conjugation_comp_eq, h]

theorem conjugation_zero (A : TraceClass H) : conjugationLinearMap (0 : H →L[ℂ] K) A = 0 := by
  apply Subtype.ext
  ext x
  change (0 : H →L[ℂ] K) (A.1 ((0 : H →L[ℂ] K).adjoint x)) = (0 : K →L[ℂ] K) x
  simp only [ContinuousLinearMap.zero_apply]

theorem operatorConjugation_scalar_identity (S : H →L[ℂ] H) (hS : S * S.adjoint = 1) (c : ℂ) :
    operatorConjugation S (c • 1) = c • (1 : H →L[ℂ] H) := by
  ext x
  change S (c • (S.adjoint x)) = c • x
  rw [map_smul]
  have he := congrArg (fun T : H →L[ℂ] H => T x) hS
  simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using congrArg (fun y => c • y) he

end Algebra

variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem partitionTensorAction_mul_adjoint (mu : Fin d → ℕ) (hmu : Antitone mu)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1) :
    partitionTensorAction mu hmu U * (partitionTensorAction mu hmu U).adjoint = 1 := by
  rw [← cyclicTensorOperator_star _ _ _ _ U, ← cyclicTensorOperator_mul,
    mul_eq_one_comm.mp hU, cyclicTensorOperator_one]

theorem partitionTensorAction_conjugation_trace (mu : Fin d → ℕ) (hmu : Antitone mu)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1)
    (A : TraceClass (cyclicSector (partitionHighestTensor mu hmu))) :
    traceCLM (conjugationLinearMap (partitionTensorAction mu hmu U) A) = traceCLM A :=
  conjugationLinearMap_isometry_trace (cyclicUnitary (partitionHighestTensor mu hmu)
    (fun a => (mu a : ℂ)) (partitionHighestTensor_cartan mu hmu)
    (partitionHighestTensor_raising_zero mu hmu) U hU).toLinearIsometry A

theorem partitionInvariantState_covariant (mu : Fin d → ℕ) (hmu : Antitone mu)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1) :
    conjugationLinearMap (partitionTensorAction mu hmu U)
      (TraceClass.ofOperator (partitionInvariantState mu hmu).op (partitionInvariantState mu hmu).traceClass) =
      TraceClass.ofOperator (partitionInvariantState mu hmu).op (partitionInvariantState mu hmu).traceClass := by
  apply Subtype.ext
  change operatorConjugation (partitionTensorAction mu hmu U) (partitionInvariantState mu hmu).op =
    (partitionInvariantState mu hmu).op
  rw [partitionInvariantState_op]
  exact operatorConjugation_scalar_identity _ (partitionTensorAction_mul_adjoint mu hmu U hU) _

end Cloning.TensorCloning
