import Cloning.TensorLANEmbeddingSectorUniform
import Cloning.TensorGibbsSchurBridge

/-! Uniform state normalization and the universal error bound for every
physical sector, including labels outside the typical window. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace ComplexOrder
open Filter NormedSpace
namespace Cloning.TensorLAN
open Cloning.PCT Cloning.TensorLie Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
open Cloning.TensorLocalUnitary Cloning.PCTLocalChart
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem rootDisplacedThermal_nonneg (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (hord : StrictAnti p) (z : PositiveRoot d → ℂ) :
    0 ≤ (rootDisplacedThermal p z).1 :=
  (displacementChannel (rootFockAmplitude z)).toPositiveTracePreservingMap.map_nonneg _
    (rootThermalState_nonneg p hp hord)

theorem rootDisplacedThermal_norm (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (hord : StrictAnti p) (z : PositiveRoot d → ℂ) :
    ‖rootDisplacedThermal p z‖ = 1 := by
  rw [rootDisplacedThermal,
    (displacementChannel (rootFockAmplitude z)).toPositiveTracePreservingMap.norm_map_of_nonneg _
      (rootThermalState_nonneg p hp hord),
    TraceClass.norm_eq_trace_re_of_nonneg _ (rootThermalState_nonneg p hp hord)]
  change (traceCLM (rootThermalState p)).re = 1
  rw [rootThermalState_trace p hp hord]
  rfl

theorem partitionPhysicalGibbs_nonneg (mu : Fin d → ℕ) (hmu : Antitone mu)
    (r p : Fin d → ℝ) (hr : ∀ a, 0 < r a) (z : PositiveRoot d → ℂ) :
    0 ≤ (partitionPhysicalGibbs mu hmu r p z).1 := by
  unfold partitionPhysicalGibbs sectorDisplacedGibbs
  apply PositiveTracePreservingMap.map_nonneg
  exact sectorGibbsDensity_nonneg _ _ _ _ (partitionHighestTensor_norm mu hmu) r hr

theorem partitionPhysicalGibbs_norm (mu : Fin d → ℕ) (hmu : Antitone mu)
    (r p : Fin d → ℝ) (hr : ∀ a, 0 < r a) (z : PositiveRoot d → ℂ) :
    ‖partitionPhysicalGibbs mu hmu r p z‖ = 1 := by
  unfold partitionPhysicalGibbs sectorDisplacedGibbs
  rw [PositiveTracePreservingMap.norm_map_of_nonneg _ _
    (sectorGibbsDensity_nonneg _ _ _ _ (partitionHighestTensor_norm mu hmu) r hr),
    TraceClass.norm_eq_trace_re_of_nonneg _
      (sectorGibbsDensity_nonneg _ _ _ _ (partitionHighestTensor_norm mu hmu) r hr)]
  change (traceCLM (sectorGibbsDensity (partitionHighestTensor mu hmu) mu
    (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) r)).re = 1
  rw [sectorGibbsDensity_trace _ _ _ _ (partitionHighestTensor_norm mu hmu) r hr]
  rfl

theorem physicalGibbsForwardError_le_two (mu : Fin d → ℕ) (hmu : Antitone mu)
    (r p : Fin d → ℝ) (hr : ∀ a, 0 < r a) (hp : ∀ a, 0 < p a)
    (hord : StrictAnti p) (z : PositiveRoot d → ℂ) (Q : ℕ) :
    physicalGibbsForwardError mu hmu r p z z Q ≤ 2 := by
  unfold physicalGibbsForwardError
  apply (norm_sub_le _ _).trans
  rw [(sectorToFockTotal (partitionHighestTensor mu hmu) mu Q).toPositiveTracePreservingMap.norm_map_of_nonneg _
      (partitionPhysicalGibbs_nonneg mu hmu r p hr z),
    partitionPhysicalGibbs_norm mu hmu r p hr z, rootDisplacedThermal_norm p hp hord z]
  norm_num

theorem physicalGibbsReverseError_le_two (mu : Fin d → ℕ) (hmu : Antitone mu)
    (r p : Fin d → ℝ) (hr : ∀ a, 0 < r a) (hp : ∀ a, 0 < p a)
    (hord : StrictAnti p) (z : PositiveRoot d → ℂ) (Q : ℕ) :
    physicalGibbsReverseError mu hmu r p z z Q ≤ 2 := by
  unfold physicalGibbsReverseError
  apply (norm_sub_le _ _).trans
  rw [(fockToSectorTotal (partitionHighestTensor mu hmu) mu Q
      (partitionHighestTensor_norm mu hmu)).toPositiveTracePreservingMap.norm_map_of_nonneg _
      (rootDisplacedThermal_nonneg p hp hord z),
    rootDisplacedThermal_norm p hp hord z, partitionPhysicalGibbs_norm mu hmu r p hr z]
  norm_num

end Cloning.TensorLAN
