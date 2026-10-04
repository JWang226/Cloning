import Cloning.TensorGibbsPhysicalLAN
import Cloning.TensorLocalUnitaryWeylUniform

/-! A compression cutoff chosen before all physical sequences, for bounded
limiting displacements. This is the sector estimate needed to pass from
sequential limits to compact uniform LAN. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology Matrix.Norms.L2Operator
open Filter NormedSpace
namespace Cloning.TensorLie
open Cloning.PCT Cloning.TensorLAN Cloning.TensorLocalUnitary Cloning.PCTLocalChart
open Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- The cutoff depends only on the limiting spectrum, the orbital bound and
accuracy. The arbitrary physical sequences are quantified after this choice. -/
theorem exists_uniform_cutoff_eventually_twoWay_physical_gibbs
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p)
    (B : ℝ) (hB : 0 ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q0 : ℕ, ∀ Q ≥ Q0,
      ∀ (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
        (δ : ℕ → ℝ), Tendsto δ atTop atTop →
        (∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a) →
      ∀ (r : ℕ → Fin d → ℝ),
        (∀ a, Tendsto (fun N => r N a) atTop (𝓝 (p a))) →
        Tendsto (fun N => fun a => (mu N a : ℝ)/((∑ b, mu N b : ℕ) : ℝ)) atTop (𝓝 p) →
      ∀ (z : ℕ → PositiveRoot d → ℂ) (z0 : PositiveRoot d → ℂ),
        Tendsto z atTop (𝓝 z0) → (∑ a, ‖z0 a‖) ≤ B →
      ∀ᶠ N in atTop,
        physicalGibbsForwardError (mu N) (hmu N) (r N) p (z N) z0 Q < ε ∧
        physicalGibbsReverseError (mu N) (hmu N) (r N) p (z N) z0 Q < ε := by
  have hη : 0 < ε/16 := by positivity
  obtain ⟨R,hR⟩ := ((rootThermalCutoff_error_tendsto_zero p hp hord).eventually
    (eventually_lt_nhds hη)).exists
  have hpGap : ∀ a : PositiveRoot d, 0 < p a.val.1-p a.val.2 := fun a => sub_pos.mpr (hord a.property)
  obtain ⟨Q0,_,hQ0⟩ := exists_uniform_cutoff_eventually_physical_orbital_frames B hB R (ε/16) hη
  refine ⟨Q0,?_⟩
  intro Q hQ mu hmu δ hδ hgap r hrlim hfreq z z0 hz hzB
  have hvec := hQ0 Q hQ p hpGap mu hmu δ hδ hgap hfreq z z0 hz hzB
  have hc := (gibbsThermalCutoffError_tendsto mu hmu δ hδ hgap r p hp hord hrlim R).eventually
    (eventually_lt_nhds (show 2 * ‖rootThermalState p-rootThermalCutoff p R‖ < ε/2 by linarith))
  have hrpos : ∀ᶠ N in atTop, ∀ a, 0 < r N a :=
    Filter.eventually_all.mpr (fun a => (hrlim a).eventually (eventually_gt_nhds (hp a)))
  filter_upwards [hc, hrpos, partition_eventually_CutoffReady mu hmu δ hδ hgap R,
    partition_eventually_CutoffReady mu hmu δ hδ hgap Q,
    hvec] with N hcN hrN hRN hQN hvN
  let Ω := partitionHighestTensor (mu N) (hmu N)
  let U := sectorOrbitalUnitary Ω (mu N) (partitionHighestTensor_cartan _ _)
    (partitionHighestTensor_raising_zero _ _) p (sampleScale (∑ j, mu N j)) (z N)
  let W := weylUnitary (rootFockAmplitude z0)
  have hvf : (∑ i : CutoffIndex d R, bosonicOccupationWeight p (cutoffOccupation d R i).val *
      ‖sectorFockTransport Ω (mu N) Q hQN (U (cutoffSectorFrame Ω (mu N) R i)) - W (cutoffNumberFrame d R i)‖) ≤ ε/16 := by
    apply weighted_finite_error_le _ _ (fun i => bosonicOccupationWeight_nonneg p hp hord _)
      (thermal_cutoff_mass_le_one p hp hord R) _ hη.le
    intro i
    rw [show U = sectorOrbitalUnitary Ω (mu N) (partitionHighestTensor_cartan _ _)
      (partitionHighestTensor_raising_zero _ _) p (sampleScale (∑ j, mu N j)) (z N) from rfl,
      show W (cutoffNumberFrame d R i) = displacement (rootFockAmplitude z0) (cutoffNumberFrame d R i) from rfl,
      sector_orbital_vector_error_eq_ambient]
    exact (hvN i).1.le
  have hvr : (∑ i : CutoffIndex d R, sectorOccupationWeight Ω (mu N) (partitionHighestTensor_cartan _ _)
      (partitionHighestTensor_raising_zero _ _) (r N) (cutoffOccupation d R i).val *
      ‖(sectorFockTransport Ω (mu N) Q hQN).adjoint (W (cutoffNumberFrame d R i)) - U (cutoffSectorFrame Ω (mu N) R i)‖) ≤ ε/16 := by
    apply weighted_finite_error_le _ _
      (fun i => sectorOccupationWeight_nonneg Ω (mu N) _ _ (partitionHighestTensor_norm _ _) (r N) hrN _)
      (physical_cutoff_mass_le_one Ω (mu N) _ _ (partitionHighestTensor_norm _ _) (r N) hrN R hRN) _ hη.le
    intro i
    rw [show U = sectorOrbitalUnitary Ω (mu N) (partitionHighestTensor_cartan _ _)
      (partitionHighestTensor_raising_zero _ _) p (sampleScale (∑ j, mu N j)) (z N) from rfl,
      show W (cutoffNumberFrame d R i) = displacement (rootFockAmplitude z0) (cutoffNumberFrame d R i) from rfl,
      sector_orbital_reverse_vector_error_eq_ambient]
    exact (hvN i).2.le
  have hf := sectorToFockTotal_displaced_gibbs_error Ω (mu N)
    (partitionHighestTensor_cartan _ _) (partitionHighestTensor_raising_zero _ _) (partitionHighestTensor_norm _ _)
    (r N) p hrN hp hord R Q hRN hQN U.toLinearIsometry W.toLinearIsometry
  have hb := fockToSectorTotal_displaced_gibbs_error Ω (mu N)
    (partitionHighestTensor_cartan _ _) (partitionHighestTensor_raising_zero _ _) (partitionHighestTensor_norm _ _)
    (r N) p hrN hp hord R Q hRN hQN U.toLinearIsometry W.toLinearIsometry
  change physicalGibbsForwardError (mu N) (hmu N) (r N) p (z N) z0 Q ≤ _ at hf
  change physicalGibbsReverseError (mu N) (hmu N) (r N) p (z N) z0 Q ≤ _ at hb
  dsimp only [LinearIsometryEquiv.coe_toLinearIsometry] at hf hb
  constructor <;> linarith


end Cloning.TensorLie
