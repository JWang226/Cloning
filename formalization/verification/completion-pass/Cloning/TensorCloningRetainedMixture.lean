import Cloning.TensorCloningRetainedCoefficients
import Cloning.InfiniteFidelityCornerMixture

/-! Exact fidelity convergence for arbitrary normalized retained Cartan
mixtures sharing one actual physical output sector. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical Topology
open Filter
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
open Cloning.InfiniteFidelityCorner
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def partitionTransitionMixture {J : Type*} [Fintype J]
    (μ : J → Fin d → ℕ) (ν : Fin d → ℕ) (hμ : ∀ a, Antitone (μ a)) (hν : Antitone ν)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (q : J → ℝ) (hq : ∀ a, 0 ≤ q a) :
    PositiveTraceClass (cyclicSector (partitionHighestTensor ν hν)) :=
  PositiveTraceClass.finiteMixture q hq (fun a => partitionTransitionOutput (μ a) ν (hμ a) hν p hp)

/-- The mixture has its exact orbital fidelity limit for arbitrary varying
probability weights. Uniform source row frequencies and the common target
frequency are the only representation asymptotic hypotheses. -/
theorem partitionTransitionMixture_rootFidelity_tendsto
    {J : ℕ → Type*} [∀ N, Fintype (J N)]
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (μ : ∀ N, J N → Fin d → ℕ) (ν : ℕ → Fin d → ℕ)
    (hμ : ∀ N a, Antitone (μ N a)) (hν : ∀ N, Antitone (ν N))
    (pN : ℕ → Fin d → ℝ) (hpN : ∀ N a, 0 < pN N a)
    (p : SimpleSpectrum d) (hlim : ∀ a, Tendsto (fun N => pN N a) atTop (𝓝 (p.eigenvalue a)))
    (γ : ℝ) (hγ : 1 < γ)
    (hμlim : ∀ a ε, 0 < ε → ∀ᶠ N in atTop, ∀ j : J N,
      |(μ N j a : ℝ)/(n N : ℝ)-p.eigenvalue a| < ε)
    (hνlim : ∀ a, Tendsto (fun N => (ν N a : ℝ)/(n N : ℝ)) atTop (𝓝 (γ*p.eigenvalue a)))
    (q : ∀ N, J N → ℝ) (hq : ∀ N a, 0 ≤ q N a) (hs : ∀ N, ∑ a,q N a=1) :
    Tendsto (fun N => (partitionTransitionMixture (μ N) (ν N) (hμ N) (hν N)
      (pN N) (hpN N) (q N) (hq N)).rootFidelity
        (partitionGibbsPositive (ν N) (hν N) (pN N) (hpN N))) atTop (𝓝 (orbitalValue γ p)) := by
  obtain ⟨δν,hδν,hgν⟩ := exists_root_gap_of_scaled_limits n hn ν (fun a => γ*p.eigenvalue a)
    (fun a => mul_pos (by linarith) (p.positive a))
    (fun a b hab => mul_lt_mul_of_pos_left (p.strictAnti hab) (by linarith)) hνlim
  have ht0 : ∀ _ : PositiveRoot d, 0 < γ⁻¹ := fun _ => inv_pos.mpr (by linarith)
  have ht1 : ∀ _ : PositiveRoot d, γ⁻¹ ≤ 1 := fun _ => (inv_le_one₀ (by linarith : 0 < γ)).mpr hγ.le
  have hq0 : ∀ a, 0 ≤ rootBoltzmann p.eigenvalue a := fun a => (div_pos (p.positive _) (p.positive _)).le
  have hq1 : ∀ a, rootBoltzmann p.eigenvalue a < 1 := rootBoltzmann_lt_one p.eigenvalue p.positive p.strictAnti
  let A N a := partitionTransitionOutput (μ N a) (ν N) (hμ N a) (hν N) (pN N) (hpN N)
  let B N := partitionGibbsPositive (ν N) (hν N) (pN N) (hpN N)
  let C := cartanThermalPositive (fun _ => γ⁻¹) (rootBoltzmann p.eigenvalue) ht0 ht1 hq0 hq1
  let D := rootThermalPositive p.eigenvalue p.positive p.strictAnti
  have hf := tendsto_finiteMixture_rootFidelity_of_corner_coefficients (fun R => CutoffIndex d R)
    q hq hs A B C D
    (fun N a => partitionTransitionOutput_norm _ _ _ _ _ _)
    (fun N => partitionGibbsPositive_norm _ _ _ _)
    (cartanThermalPositive_norm _ _ _ _ _ _) (rootThermalPositive_norm _ _ _)
    (fun N R => cutoffSectorFrame (partitionHighestTensor (ν N) (hν N)) (ν N) R)
    (cutoffNumberFrame d)
    (fun R => (partition_eventually_CutoffReady ν hν δν hδν hgν R).mono
      (fun N hN => cutoffSectorFrame_orthonormal _ _ R hN.2))
    (cutoffNumberFrame_orthonormal d)
    (fun R i j => ?_) (fun R i j => ?_)
    (cartanThermalOutput_cutoff_mass_tendsto _ _ ht0 ht1 hq0 hq1)
    (rootThermalState_cutoff_mass_tendsto p.eigenvalue p.positive p.strictAnti)
  · change Tendsto _ atTop (𝓝 (C.rootFidelity D)) at hf
    dsimp only [C,D] at hf
    rw [cartanThermalPositive_rootFidelity, cartanThermalProduct_eq_orbitalValue p γ hγ] at hf
    exact hf
  · change ∀ ε, 0 < ε → ∀ᶠ N in atTop, ∀ a : J N,
      ‖partitionTransitionCoefficient (μ N a) (ν N) (hμ N a) (hν N) (pN N) (hpN N) R i j -
        ⟪cutoffNumberFrame d R i, (cartanThermalOutput (fun _ => γ⁻¹) (rootBoltzmann p.eigenvalue)).1
          (cutoffNumberFrame d R j)⟫_ℂ‖ < ε
    rw [cartanThermalOutput_cutoff_coefficient _ _ ht0 ht1 hq0 hq1]
    exact partitionTransitionCoefficient_uniform n hn μ ν hμ hν pN hpN p hlim γ hγ hμlim hνlim R i j
  · exact partitionGibbsPositive_cutoff_coefficient_tendsto ν hν δν hδν hgν pN hpN
      p.eigenvalue p.positive p.strictAnti hlim R i j

end Cloning.TensorCloning
