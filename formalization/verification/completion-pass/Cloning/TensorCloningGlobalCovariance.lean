import Cloning.TensorCloningGlobalCovarianceSector
import Cloning.TensorCloningKernel
import Cloning.TensorCloningGlobalCovarianceInstrument

/-! Exact all-input unitary covariance of the physical global cloning
channels, including their fallback actions. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Classical
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Any state-independent stochastic table of physical sector transitions
gives an exactly covariant channel on the whole complex trace-class space. -/
theorem channel_covariant (n m d : ℕ) (q : SchurCopy n d → SchurCopy m d → ℝ)
    (hq : ∀ i j, 0 ≤ q i j) (hs : ∀ i, ∑ j, q i j = 1)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1)
    (A : TraceClass (TensorRegister n (Fin d))) :
    (channel n m d q hq hs).toLinearMap (conjugationLinearMap (tensorOperator n U) A) =
      conjugationLinearMap (tensorOperator m U) ((channel n m d q hq hs).toLinearMap A) := by
  have hin (i : SchurCopy n d) (B : TraceClass (TensorRegister n (Fin d))) :=
    canonicalCompression_covariant (n := n) (d := d) ((recursivePhysicalDecomposition n d).get i) U B
  have hout (i : SchurCopy n d) (j : SchurCopy m d)
      (B : TraceClass ((recursivePhysicalDecomposition n d).get i).CanonicalSector) :=
    copyTransition_covariant (d := d) n m i j U hU B
  have hcov := finite_instrument_covariant
    (fun i : SchurCopy n d => ((recursivePhysicalDecomposition n d).get i).canonicalEmbedding.toContinuousLinearMap.adjoint)
    (fun (i : SchurCopy n d) (j : SchurCopy m d) => (copyTransition n m d i j).toLinearMap)
    (fun i j => (q i j : ℂ)) (tensorOperator n U) (tensorOperator m U)
    (fun i : SchurCopy n d => partitionTensorAction ((recursivePhysicalDecomposition n d).get i).weight
      ((recursivePhysicalDecomposition n d).get i).weight_antitone U) hin hout A
  exact (channel_apply n m d q hq hs (conjugationLinearMap (tensorOperator n U) A)).trans
    (hcov.trans (congrArg (conjugationLinearMap (tensorOperator m U)) (channel_apply n m d q hq hs A).symm))

/-- The known-spectrum cloner is exactly covariant at every sample size. -/
theorem knownSpectrumChannel_covariant (n m d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1)
    (A : TraceClass (TensorRegister n (Fin d))) :
    (knownSpectrumChannel n m d p hp hs).toLinearMap (conjugationLinearMap (tensorOperator n U) A) =
      conjugationLinearMap (tensorOperator m U) ((knownSpectrumChannel n m d p hp hs).toLinearMap A) :=
  channel_covariant n m d _ _ _ U hU A

/-- The universal cloner is a single exactly covariant channel, with no
spectral parameter and no restriction to compatible transitions. -/
theorem universalChannel_covariant (n m d : ℕ)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (hU : Uᴴ * U = 1)
    (A : TraceClass (TensorRegister n (Fin (d+1)))) :
    (universalChannel n m d).toLinearMap (conjugationLinearMap (tensorOperator n U) A) =
      conjugationLinearMap (tensorOperator m U) ((universalChannel n m d).toLinearMap A) :=
  channel_covariant n m (d+1) _ _ _ U hU A

end Cloning.TensorCloning
