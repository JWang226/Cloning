import Cloning.TensorGibbsState
import Cloning.TensorPartitionHighest

/-! The canonical maximally mixed sector replacement state. It is invariant
under every unitary action, including sectors of arbitrary tensor degree. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Classical
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def partitionInvariantState {d : ℕ} (mu : Fin d → ℕ) (hmu : Antitone mu) :
    DensityState (cyclicSector (partitionHighestTensor mu hmu)) :=
  sectorGibbsState (partitionHighestTensor mu hmu) mu (partitionHighestTensor_cartan mu hmu)
    (partitionHighestTensor_raising_zero mu hmu) (partitionHighestTensor_norm mu hmu)
    (fun _ => 1) (fun _ => zero_lt_one)

theorem partitionInvariantState_op {d : ℕ} (mu : Fin d → ℕ) (hmu : Antitone mu) :
    (partitionInvariantState mu hmu).op =
      (((Module.finrank ℂ (cyclicSector (partitionHighestTensor mu hmu)) : ℝ)⁻¹ : ℝ) : ℂ) • 1 := by
  have hop : sectorGibbsOperator (partitionHighestTensor mu hmu) mu
      (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu)
      (fun _ => 1) = 1 := by
    simp only [sectorGibbsOperator, Complex.ofReal_one, Matrix.diagonal_one, cyclicTensorOperator_one]
  have hZ : sectorPartitionFunction (partitionHighestTensor mu hmu) mu
      (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu)
      (fun _ => 1) = (Module.finrank ℂ (cyclicSector (partitionHighestTensor mu hmu)) : ℝ) := by
    rw [sectorPartitionFunction_eq_linearMapTrace _ _ _ _ _ (fun _ => zero_le_one), hop]
    change (LinearMap.trace ℂ _ (LinearMap.id : cyclicSector (partitionHighestTensor mu hmu) →ₗ[ℂ] _)).re = _
    rw [LinearMap.trace_id]
    simp only [Complex.natCast_re]
  change _ • sectorGibbsOperator _ _ _ _ _ = _
  rw [hop, hZ]

end Cloning.TensorCloning
