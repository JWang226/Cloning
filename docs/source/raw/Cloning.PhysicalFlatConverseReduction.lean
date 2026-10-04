import Cloning.PhysicalFlatPinchingOrbit
import Cloning.InfiniteFidelityHilbertSum
import Cloning.InfiniteFidelityTransition

/-! Every actual physical cloning channel is reduced to its positive Schur
output blocks after the proved invariant input majorization. No covariance
of the competing channel is assumed. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical ComplexOrder
namespace Cloning.PhysicalFlatConverse
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
open Cloning.InfiniteFiniteCorner Cloning.InfiniteFidelityHilbertSum Cloning.PCTPhysicalState
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def schurCopyBlock (n d : ℕ) (A : TraceClass (TensorRegister n (Fin d))) (i : SchurCopy n d) :
    TraceClass ((recursivePhysicalDecomposition n d).get i).CanonicalSector :=
  conjugationLinearMap ((recursivePhysicalDecomposition n d).get i).canonicalEmbedding.toContinuousLinearMap.adjoint A

def schurCopyPositive (n d : ℕ) (A : PositiveTraceClass (TensorRegister n (Fin d))) (i : SchurCopy n d) :
    PositiveTraceClass ((recursivePhysicalDecomposition n d).get i).CanonicalSector :=
  ⟨schurCopyBlock n d A.1 i, conjugationLinearMap_nonneg _ _ A.2⟩

def schurCopyMatrix (n d : ℕ) (A : TraceClass (TensorRegister n (Fin d))) (i : SchurCopy n d) :=
  matrixOf (partitionBasis ((recursivePhysicalDecomposition n d).get i).weight
    ((recursivePhysicalDecomposition n d).get i).weight_antitone) (schurCopyBlock n d A i).1

theorem schurCopyMatrix_posSemidef (n d : ℕ) (A : PositiveTraceClass (TensorRegister n (Fin d)))
    (i : SchurCopy n d) : (schurCopyMatrix n d A.1 i).PosSemidef :=
  matrixOf_posSemidef _ (schurCopyPositive n d A i).2

theorem schurPinching_eq_orthogonalSum (n d : ℕ) (A : PositiveTraceClass (TensorRegister n (Fin d))) :
    A.map (schurPinching n d).toPositiveTracePreservingMap =
      orthogonalSum (fun i : SchurCopy n d => ((recursivePhysicalDecomposition n d).get i).canonicalEmbedding)
        (schurCopyPositive n d A) := by
  apply Subtype.ext
  exact schurPinching_apply n d A.1

theorem rootFidelity_le_schurCopyMatrices (n d : ℕ)
    (A B : PositiveTraceClass (TensorRegister n (Fin d))) :
    A.rootFidelity B ≤ ∑ i : SchurCopy n d,
      Cloning.MatrixFidelity.fidelity (schurCopyMatrix n d A.1 i) (schurCopyMatrix n d B.1 i) := by
  have hh := schurPinching_rootFidelity n d A B
  rw [schurPinching_eq_orthogonalSum,schurPinching_eq_orthogonalSum,
    rootFidelity_orthogonalSum _
      (canonicalSectorFamily_orthogonal (recursivePhysicalDecomposition n d)
        (recursivePhysicalDecomposition_is_decomposition n d).1)
      (fun i => partitionBasis ((recursivePhysicalDecomposition n d).get i).weight
        ((recursivePhysicalDecomposition n d).get i).weight_antitone)] at hh
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro i _
  exact (rootFidelity_matrixOf_basis _ (schurCopyPositive n d A i) (schurCopyPositive n d B i)).symm

theorem trace_schurCopyMatrix (n d : ℕ) (A : TraceClass (TensorRegister n (Fin d))) (i : SchurCopy n d) :
    (schurCopyMatrix n d A i).trace = traceCLM (schurCopyBlock n d A i) := by
  let b := partitionBasis ((recursivePhysicalDecomposition n d).get i).weight
    ((recursivePhysicalDecomposition n d).get i).weight_antitone
  have hh := congrArg traceCLM (matrixLift_basis_matrixOf b (schurCopyBlock n d A i))
  change traceCLM (matrixLift b (schurCopyMatrix n d A i)) = _ at hh
  rw [show traceCLM (matrixLift b (schurCopyMatrix n d A i)) =
      (schurCopyMatrix n d A i).trace from trace_ofMatrix b.orthonormal _] at hh
  exact hh

theorem sum_trace_schurCopyMatrix (n d : ℕ) (A : TraceClass (TensorRegister n (Fin d))) :
    (∑ i : SchurCopy n d, (schurCopyMatrix n d A i).trace.re) = (traceCLM A).re := by
  have hh := congrArg Complex.re (schurPinching_trace n d A)
  rw [schurPinching_apply,map_sum] at hh
  simp only [Complex.re_sum,conjugationLinearMap_isometry_trace] at hh
  simpa only [trace_schurCopyMatrix,schurCopyBlock] using hh

/-- Actual channel images preserve Loewner domination. -/
theorem channel_map_le {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (Φ : QuantumChannel H K) (A B : TraceClass H) (hAB : A.1 ≤ B.1) :
    (Φ.toLinearMap A).1 ≤ (Φ.toLinearMap B).1 := by
  have hh := Φ.toPositiveTracePreservingMap.map_nonneg (B-A) (sub_nonneg.mpr hAB)
  rw [map_sub] at hh
  exact sub_nonneg.mp hh

/-- Universal physical upper reduction: the same inflated input dominates
all orbit points before applying any competing quantum channel. -/
theorem payoff_le_schurCopyMatrices (r k : ℕ) (hr : 0 < r) (n m : ℕ)
    (Φ : QuantumChannel (TensorRegister n (Fin (r+k))) (TensorRegister m (Fin (r+k))))
    (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) :
    letI : Nonempty (Fin (r+k)) := ⟨⟨0,Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
    payoff r k hr n m Φ U ≤ ∑ i : SchurCopy m (r+k),
      Cloning.MatrixFidelity.fidelity
        (schurCopyMatrix m (r+k) (Φ.toLinearMap (flatInflatedInput n r k)) i)
        (schurCopyMatrix m (r+k) (tensorState (orbitState r k hr U) m).1 i) := by
  letI : Nonempty (Fin (r+k)) := ⟨⟨0,Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
  let B : PositiveTraceClass (TensorRegister m (Fin (r+k))) :=
    ⟨Φ.toLinearMap (flatInflatedInput n r k),
      Φ.toPositiveTracePreservingMap.map_nonneg _ (flatInflatedInput_nonneg n r k)⟩
  have hh := PositiveTraceClass.rootFidelity_mono_left
    ((tensorState (orbitState r k hr U) n).map Φ.toPositiveTracePreservingMap) B
    (tensorState (orbitState r k hr U) m)
    (channel_map_le Φ _ _ (orbit_tensorState_le_flatInflatedInput n r k hr U))
  exact hh.trans (rootFidelity_le_schurCopyMatrices m (r+k) B (tensorState (orbitState r k hr U) m))

end Cloning.PhysicalFlatConverse
