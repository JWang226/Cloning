import Cloning.PhysicalFlatConverseReduction
import Cloning.PhysicalFlatConverseOrbitAverage
import Cloning.PhysicalFlatConverseMoments
import Cloning.PhysicalFlatPinchingBlocks

/-! The finite-sample all-channel physical converse for a rank-flat orbit.
All Haar integrals, block identities, and dimension moments are derived
from the literal tensor states and arbitrary competing quantum channels. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical ComplexOrder Matrix Topology
open MeasureTheory
namespace Cloning.PhysicalFlatConverse
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
open Cloning.PCTPhysicalState Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite
variable (r k : ℕ) (hr : 0 < r)

set_option maxHeartbeats 300000 in
theorem canonicalBlock_orbit_tensor (m : ℕ) (H : PhysicalHighestTensor m (r+k))
    (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) :
    letI : Nonempty (Fin (r+k)) := ⟨⟨0,Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
    Cloning.InfiniteFiniteCorner.matrixOf (partitionBasis H.weight H.weight_antitone)
      (conjugationLinearMap H.canonicalEmbedding.toContinuousLinearMap.adjoint
        (tensorState (orbitState r k hr U) m).1).1 =
      partitionActionMatrix H.weight H.weight_antitone U *
        (((1/(r:ℝ))^m) • partitionCoordinateProjection H.weight H.weight_antitone) *
          (partitionActionMatrix H.weight H.weight_antitone U)ᴴ := by
  letI : Nonempty (Fin (r+k)) := ⟨⟨0,Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
  have hc := congrArg
    (fun T : TraceClass H.CanonicalSector => Cloning.InfiniteFiniteCorner.matrixOf
      (partitionBasis H.weight H.weight_antitone) T.1)
    (matrixTensorPower_canonical_block H (orbitState r k hr U).matrix)
  exact hc.trans (canonicalTensorWeight_rotated_rankFlat_matrix
    (n := m) (r := r) (k := k) H (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ))

theorem schurCopyMatrix_orbit_tensor (m : ℕ)
    (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) (i : SchurCopy m (r+k)) :
    letI : Nonempty (Fin (r+k)) := ⟨⟨0,Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
    schurCopyMatrix m (r+k) (tensorState (orbitState r k hr U) m).1 i =
      partitionActionMatrix ((recursivePhysicalDecomposition m (r+k)).get i).weight
        ((recursivePhysicalDecomposition m (r+k)).get i).weight_antitone U *
      (((1/(r:ℝ))^m) • partitionCoordinateProjection
        ((recursivePhysicalDecomposition m (r+k)).get i).weight
        ((recursivePhysicalDecomposition m (r+k)).get i).weight_antitone) *
      (partitionActionMatrix ((recursivePhysicalDecomposition m (r+k)).get i).weight
        ((recursivePhysicalDecomposition m (r+k)).get i).weight_antitone U)ᴴ := by
  letI : Nonempty (Fin (r+k)) := ⟨⟨0,Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
  exact canonicalBlock_orbit_tensor r k hr m ((recursivePhysicalDecomposition m (r+k)).get i) U

def channelOrbitMajorant (n m : ℕ)
    (Φ : QuantumChannel (TensorRegister n (Fin (r+k))) (TensorRegister m (Fin (r+k))))
    (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) : ℝ :=
  ∑ i : SchurCopy m (r+k), Cloning.MatrixFidelity.fidelity
    (schurCopyMatrix m (r+k) (Φ.toLinearMap (flatInflatedInput n r k)) i)
    (partitionActionMatrix ((recursivePhysicalDecomposition m (r+k)).get i).weight
      ((recursivePhysicalDecomposition m (r+k)).get i).weight_antitone
        ((U⁻¹ : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) : Matrix _ _ ℂ) *
      (((1/(r:ℝ))^m) • partitionCoordinateProjection
        ((recursivePhysicalDecomposition m (r+k)).get i).weight
        ((recursivePhysicalDecomposition m (r+k)).get i).weight_antitone) *
      (partitionActionMatrix ((recursivePhysicalDecomposition m (r+k)).get i).weight
        ((recursivePhysicalDecomposition m (r+k)).get i).weight_antitone
          ((U⁻¹ : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) : Matrix _ _ ℂ))ᴴ)

theorem payoff_inv_le_channelOrbitMajorant (n m : ℕ)
    (Φ : QuantumChannel (TensorRegister n (Fin (r+k))) (TensorRegister m (Fin (r+k))))
    (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) :
    payoff r k hr n m Φ U⁻¹ ≤ channelOrbitMajorant r k n m Φ U := by
  letI : Nonempty (Fin (r+k)) := ⟨⟨0,Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
  have hh := payoff_le_schurCopyMatrices r k hr n m Φ U⁻¹
  simpa only [schurCopyMatrix_orbit_tensor,channelOrbitMajorant] using hh

theorem channelOrbitMajorant_integrable (n m : ℕ)
    (Φ : QuantumChannel (TensorRegister n (Fin (r+k))) (TensorRegister m (Fin (r+k)))) :
    letI : Nonempty (Fin (r+k)) := ⟨⟨0,Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
    Integrable (channelOrbitMajorant r k n m Φ) unitaryHaar := by
  letI : Nonempty (Fin (r+k)) := ⟨⟨0,Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
  let A : PositiveTraceClass (TensorRegister m (Fin (r+k))) :=
    ⟨Φ.toLinearMap (flatInflatedInput n r k),
      Φ.toPositiveTracePreservingMap.map_nonneg _ (flatInflatedInput_nonneg n r k)⟩
  apply integrable_finset_sum
  intro i _
  exact integrable_partition_target_fidelity _ _ _ _
    (schurCopyMatrix_posSemidef m (r+k) A i)
    ((partitionCoordinateProjection_posSemidef _ _).smul (by positivity))

theorem integral_channelOrbitMajorant_le (n m : ℕ)
    (Φ : QuantumChannel (TensorRegister n (Fin (r+k))) (TensorRegister m (Fin (r+k)))) :
    letI : Nonempty (Fin (r+k)) := ⟨⟨0,Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
    (∫ U, channelOrbitMajorant r k n m Φ U ∂unitaryHaar) ≤ flatConverseBound r k hr n m := by
  letI : Nonempty (Fin (r+k)) := ⟨⟨0,Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
  let A : PositiveTraceClass (TensorRegister m (Fin (r+k))) :=
    ⟨Φ.toLinearMap (flatInflatedInput n r k),
      Φ.toPositiveTracePreservingMap.map_nonneg _ (flatInflatedInput_nonneg n r k)⟩
  have hh := integral_partition_copy_projectors_le
    (fun i : SchurCopy m (r+k) => ((recursivePhysicalDecomposition m (r+k)).get i).weight)
    (fun i => ((recursivePhysicalDecomposition m (r+k)).get i).weight_antitone)
    (schurCopyMatrix m (r+k) A.1)
    (fun i => partitionCoordinateProjection ((recursivePhysicalDecomposition m (r+k)).get i).weight
      ((recursivePhysicalDecomposition m (r+k)).get i).weight_antitone)
    (schurCopyMatrix_posSemidef m (r+k) A)
    (fun i => partitionCoordinateProjection_posSemidef _ _)
    (fun i => partitionCoordinateProjection_idempotent _ _)
    (fun _ => (1/(r:ℝ))^m) (fun _ => by positivity)
  change (∫ U, channelOrbitMajorant r k n m Φ U ∂unitaryHaar) ≤ _ at hh
  rw [sum_trace_schurCopyMatrix, flat_projection_output_inverse_moment m r k hr] at hh
  have ht : traceCLM A.1 = traceCLM (flatInflatedInput n r k) :=
    Φ.toPositiveTracePreservingMap.trace_preserving _
  rw [ht,flatInflatedInput_trace n r k hr] at hh
  exact hh

/-- Every physical channel is bounded by the exact pair of physical Young
dimension moments, including all multiplicity copies and unsupported sectors. -/
theorem minimaxValue_le_flatConverseBound (n m : ℕ) :
    minimaxValue r k hr n m ≤ flatConverseBound r k hr n m := by
  letI : Nonempty (Fin (r+k)) := ⟨⟨0,Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
  let w : Fin m → Fin (r+k) := fun _ => ⟨0,Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩
  let ρ := DensityState.pure (registerBasis (Fin m → Fin (r+k)) w)
    ((registerBasis (Fin m → Fin (r+k))).orthonormal.norm_eq_one w)
  letI : Nonempty (QuantumChannel (TensorRegister n (Fin (r+k))) (TensorRegister m (Fin (r+k)))) :=
    ⟨QuantumChannel.ofContraction 0 (by intro x; simp) ρ⟩
  simpa only [add_zero,minimaxValue] using
    LAN.minimax_le_average_bound unitaryHaar (payoff r k hr n m)
      (channelOrbitMajorant r k n m) Inv.inv id 0 (flatConverseBound r k hr n m)
      (payoff_nonneg r k hr n m)
      (fun Φ U => by simpa only [id_eq,add_zero] using payoff_inv_le_channelOrbitMajorant r k hr n m Φ U)
      (channelOrbitMajorant_integrable r k hr n m)
      (integral_channelOrbitMajorant_le r k hr n m)

end Cloning.PhysicalFlatConverse
