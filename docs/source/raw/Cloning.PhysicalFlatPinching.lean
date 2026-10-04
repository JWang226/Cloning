import Cloning.InfiniteFiniteInstrument
import Cloning.TensorLANEmbeddingBlocks
import Cloning.InfiniteChannelFidelity
import Cloning.HybridStates

/-! The literal Schur pinching channel on the full physical tensor register.
Every individual canonical copy is retained. The map is completely positive
and trace preserving on all complex trace-class inputs, and fixes every
matrix tensor power. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical ComplexOrder
namespace Cloning.PhysicalFlatConverse
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Measurement of the actual complete Schur-copy decomposition followed by
the same canonical physical embedding. -/
def schurPinching (n d : ℕ) : QuantumChannel (TensorRegister n (Fin d)) (TensorRegister n (Fin d)) :=
  QuantumChannel.ofHilbertSum
    (fun i : SchurCopy n d => ((recursivePhysicalDecomposition n d).get i).canonicalEmbedding)
    (canonicalSectorHilbertSum (recursivePhysicalDecomposition n d)
      (recursivePhysicalDecomposition_is_decomposition n d).1
      (recursivePhysicalDecomposition_is_decomposition n d).2)
    (fun i => QuantumChannel.ofIsometry ((recursivePhysicalDecomposition n d).get i).canonicalEmbedding)

/-- Exact action on arbitrary complex operators, with each individual copy
compressed and embedded back into the full register. -/
theorem schurPinching_apply (n d : ℕ) (A : TraceClass (TensorRegister n (Fin d))) :
    (schurPinching n d).toLinearMap A = ∑ i : SchurCopy n d,
      conjugationLinearMap ((recursivePhysicalDecomposition n d).get i).canonicalEmbedding.toContinuousLinearMap
        (conjugationLinearMap
          ((recursivePhysicalDecomposition n d).get i).canonicalEmbedding.toContinuousLinearMap.adjoint A) := by
  rw [schurPinching, QuantumChannel.ofHilbertSum_apply]
  rfl

theorem schurPinching_completelyPositive (n d : ℕ) :
    IsCompletelyPositive (schurPinching n d).toLinearMap :=
  (schurPinching n d).completelyPositive

theorem schurPinching_nonneg (n d : ℕ) (A : TraceClass (TensorRegister n (Fin d))) (hA : 0 ≤ A.1) :
    0 ≤ ((schurPinching n d).toLinearMap A).1 :=
  (schurPinching n d).toPositiveTracePreservingMap.map_nonneg A hA

theorem schurPinching_trace (n d : ℕ) (A : TraceClass (TensorRegister n (Fin d))) :
    traceCLM ((schurPinching n d).toLinearMap A) = traceCLM A :=
  (schurPinching n d).toPositiveTracePreservingMap.trace_preserving A

/-- Every literal tensor power is fixed, without a positivity or Hermitian
restriction on its one-site matrix. -/
theorem schurPinching_matrixTensorPower (n d : ℕ) (X : Matrix (Fin d) (Fin d) ℂ) :
    (schurPinching n d).toLinearMap (matrixTensorPower X n) = matrixTensorPower X n := by
  rw [schurPinching_apply]
  simp only [matrixTensorPower_canonical_block]
  exact (matrixTensorPower_eq_sum_canonical_blocks (recursivePhysicalDecomposition n d)
    (recursivePhysicalDecomposition_is_decomposition n d).1
    (recursivePhysicalDecomposition_is_decomposition n d).2 X).symm

theorem schurPinching_rootFidelity (n d : ℕ)
    (A B : PositiveTraceClass (TensorRegister n (Fin d))) :
    A.rootFidelity B ≤
      (A.map (schurPinching n d).toPositiveTracePreservingMap).rootFidelity
        (B.map (schurPinching n d).toPositiveTracePreservingMap) :=
  InfiniteFidelity.fidelity_data_processing (schurPinching n d) A.1 B.1 A.2 B.2

/-- Pinching can only improve fidelity against any fixed target. -/
theorem schurPinching_rootFidelity_of_fixed (n d : ℕ)
    (A B : PositiveTraceClass (TensorRegister n (Fin d)))
    (hB : (schurPinching n d).toLinearMap B.1 = B.1) :
    A.rootFidelity B ≤ (A.map (schurPinching n d).toPositiveTracePreservingMap).rootFidelity B := by
  have he : B.map (schurPinching n d).toPositiveTracePreservingMap = B := Subtype.ext hB
  simpa only [he] using schurPinching_rootFidelity n d A B

/-- In particular this applies to every physical tensor-power target. -/
theorem schurPinching_rootFidelity_tensor (n d : ℕ)
    (A : PositiveTraceClass (TensorRegister n (Fin d)))
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : 0 ≤ (matrixTensorPower X n).1) :
    A.rootFidelity ⟨matrixTensorPower X n,hX⟩ ≤
      (A.map (schurPinching n d).toPositiveTracePreservingMap).rootFidelity ⟨matrixTensorPower X n,hX⟩ :=
  schurPinching_rootFidelity_of_fixed n d A ⟨matrixTensorPower X n,hX⟩
    (schurPinching_matrixTensorPower n d X)

end Cloning.PhysicalFlatConverse
