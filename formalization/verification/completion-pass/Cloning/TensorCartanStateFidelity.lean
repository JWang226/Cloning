import Cloning.TensorCartanStateLimit
import Cloning.TensorCartanStateThermalFidelity

/-! Genuine Cartan sector fidelity convergence with all representation,
coefficient, dimension, and tail obligations discharged. -/
noncomputable section
open scoped BigOperators ComplexOrder InnerProductSpace Topology
open Filter
namespace Cloning.TensorLie
open Cloning.PCT Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
open Cloning.InfiniteFidelityCorner
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def partitionGibbsPositive (mu : Fin d → ℕ) (hmu : Antitone mu)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) :
    PositiveTraceClass (cyclicSector (partitionHighestTensor mu hmu)) :=
  ⟨sectorGibbsDensity (partitionHighestTensor mu hmu) mu
    (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) p,
    sectorGibbsDensity_nonneg _ _ _ _ (partitionHighestTensor_norm mu hmu) p hp⟩

def cartanGibbsPositive (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) :
    PositiveTraceClass (cyclicSector (partitionHighestTensor _ (sumPartition_antitone mu nu hmu hnu))) :=
  ⟨cartanGibbsOutput mu nu hmu hnu p, cartanGibbsOutput_nonneg mu nu hmu hnu p hp⟩

theorem partitionGibbsPositive_norm (mu : Fin d → ℕ) (hmu : Antitone mu)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) : ‖(partitionGibbsPositive mu hmu p hp).1‖ = 1 := by
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ (partitionGibbsPositive mu hmu p hp).2]
  change (traceCLM (sectorGibbsDensity (partitionHighestTensor mu hmu) mu
    (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) p)).re = 1
  rw [sectorGibbsDensity_trace _ _ _ _ (partitionHighestTensor_norm mu hmu) p hp]
  rfl

theorem cartanGibbsPositive_norm (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) : ‖(cartanGibbsPositive mu nu hmu hnu p hp).1‖ = 1 := by
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ (cartanGibbsPositive mu nu hmu hnu p hp).2]
  change (traceCLM (cartanGibbsOutput mu nu hmu hnu p)).re = 1
  rw [cartanGibbsOutput_trace mu nu hmu hnu p hp]
  rfl

theorem partitionGibbsPositive_cutoff_coefficient_tendsto
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a)
    (pN : ℕ → Fin d → ℝ) (hpN : ∀ N a, 0 < pN N a)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p)
    (hlim : ∀ a, Tendsto (fun N => pN N a) atTop (𝓝 (p a)))
    (R : ℕ) (i j : CutoffIndex d R) :
    Tendsto (fun N => ⟪cutoffSectorFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i,
      (partitionGibbsPositive (mu N) (hmu N) (pN N) (hpN N)).1.1
        (cutoffSectorFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R j)⟫_ℂ)
      atTop (𝓝 ⟪cutoffNumberFrame d R i, (rootThermalState p).1 (cutoffNumberFrame d R j)⟫_ℂ) := by
  rw [rootThermalState_cutoff_coefficient p hp hord]
  have he : ∀ᶠ N in atTop,
      ⟪cutoffSectorFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i,
        (partitionGibbsPositive (mu N) (hmu N) (pN N) (hpN N)).1.1
          (cutoffSectorFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R j)⟫_ℂ =
      if i = j then (sectorOccupationWeight (partitionHighestTensor (mu N) (hmu N)) (mu N)
        (partitionHighestTensor_cartan (mu N) (hmu N))
        (partitionHighestTensor_raising_zero (mu N) (hmu N)) (pN N)
        (cutoffOccupation d R i).val : ℂ) else 0 := by
    filter_upwards [partition_eventually_CutoffReady mu hmu δ hδ hgap R] with N hN
    change ⟪_, (sectorGibbsDensity _ _ _ _ _).1 _⟫_ℂ = _
    rw [sectorGibbsDensity_cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N)
      (partitionHighestTensor_cartan (mu N) (hmu N))
      (partitionHighestTensor_raising_zero (mu N) (hmu N)) (pN N) (hpN N) R j, inner_smul_right,
      orthonormal_iff_ite.mp (cutoffSectorFrame_orthonormal _ _ R hN.2)]
    split_ifs with hij
    · subst j; rw [mul_one]
    · rw [mul_zero]
  apply Filter.Tendsto.congr' (he.mono (fun N hN => hN.symm))
  split_ifs with hij
  · exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      (sectorOccupationWeight_tendsto mu hmu δ hδ hgap pN p hp hord hlim (cutoffOccupation d R i).val)
  · exact tendsto_const_nhds

/-- The actual physical Cartan channel has the claimed simple-spectrum sector
fidelity limit. No asymptotic output, dimension, frame, or tail premise remains. -/
theorem cartanGibbsPositive_rootFidelity_tendsto
    (mu nu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N)) (hnu : ∀ N, Antitone (nu N))
    (δmu δnu : ℕ → ℝ) (hδmu : Tendsto δmu atTop atTop) (hδnu : Tendsto δnu atTop atTop)
    (hmuGap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δmu N ≤ rootGap (mu N) a)
    (hnuGap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δnu N ≤ rootGap (nu N) a)
    (t : PositiveRoot d → ℝ) (ht0 : ∀ a, 0 < t a) (ht1 : ∀ a, t a ≤ 1)
    (ht : ∀ a, Tendsto (fun N => rootFraction (mu N) (nu N) a) atTop (𝓝 (t a)))
    (pN : ℕ → Fin d → ℝ) (hpN : ∀ N a, 0 < pN N a)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p)
    (hlim : ∀ a, Tendsto (fun N => pN N a) atTop (𝓝 (p a))) :
    Tendsto (fun N => (cartanGibbsPositive (mu N) (nu N) (hmu N) (hnu N) (pN N) (hpN N)).rootFidelity
      (partitionGibbsPositive (fun a => mu N a + nu N a)
        (sumPartition_antitone (mu N) (nu N) (hmu N) (hnu N)) (pN N) (hpN N))) atTop
      (𝓝 (∏ a : PositiveRoot d, Cloning.Thermal.fidelity
        (amplifiedRootParameter t (rootBoltzmann p) a) (rootBoltzmann p a))) := by
  let rho N := fun a => mu N a + nu N a
  have hrho N : Antitone (rho N) := sumPartition_antitone (mu N) (nu N) (hmu N) (hnu N)
  have hsumGap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δmu N ≤ rootGap (rho N) a := by
    filter_upwards [hmuGap] with N hN a
    have hn : (nu N a.val.2 : ℝ) ≤ nu N a.val.1 := by exact_mod_cast hnu N a.property.le
    have ha := hN a
    simp only [rootGap, rho, Nat.cast_add] at ha ⊢
    linarith
  have hq0 : ∀ a, 0 ≤ rootBoltzmann p a := fun a => (div_pos (hp _) (hp _)).le
  have hq1 : ∀ a, rootBoltzmann p a < 1 := rootBoltzmann_lt_one p hp hord
  let A N := cartanGibbsPositive (mu N) (nu N) (hmu N) (hnu N) (pN N) (hpN N)
  let B N := partitionGibbsPositive (rho N) (hrho N) (pN N) (hpN N)
  let C := cartanThermalPositive t (rootBoltzmann p) ht0 ht1 hq0 hq1
  let D := rootThermalPositive p hp hord
  have hf := tendsto_rootFidelity_of_corner_coefficients (fun R => CutoffIndex d R) A B C D
    (fun N => cartanGibbsPositive_norm _ _ _ _ _ _)
    (fun N => partitionGibbsPositive_norm _ _ _ _)
    (cartanThermalPositive_norm _ _ _ _ _ _) (rootThermalPositive_norm _ _ _)
    (fun N R => cutoffSectorFrame (partitionHighestTensor (rho N) (hrho N)) (rho N) R)
    (cutoffNumberFrame d)
    (fun R => (partition_eventually_CutoffReady rho hrho δmu hδmu hsumGap R).mono
      (fun N hN => cutoffSectorFrame_orthonormal _ _ R hN.2))
    (cutoffNumberFrame_orthonormal d)
    (fun R i j => ?_) (fun R i j => ?_)
    (cartanThermalOutput_cutoff_mass_tendsto _ _ ht0 ht1 hq0 hq1)
    (rootThermalState_cutoff_mass_tendsto p hp hord)
  · simpa only [A, B, C, D, cartanThermalPositive_rootFidelity] using hf
  · change Tendsto _ atTop (𝓝 ⟪_, (cartanThermalOutput t (rootBoltzmann p)).1 _⟫_ℂ)
    rw [cartanThermalOutput_cutoff_coefficient t (rootBoltzmann p) ht0 ht1 hq0 hq1]
    exact cartanGibbsOutput_cutoff_coefficient_tendsto mu nu hmu hnu δmu δnu hδmu hδnu
      hmuGap hnuGap t (fun a => (ht0 a).le) ht1 ht pN p hp hord hlim R i j
  · exact partitionGibbsPositive_cutoff_coefficient_tendsto rho hrho δmu hδmu hsumGap
      pN hpN p hp hord hlim R i j

end Cloning.TensorLie
