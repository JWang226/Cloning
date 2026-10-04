import Cloning.TensorCloningAchievabilitySector
import Cloning.TensorCloningAchievabilityUniform

/-! Actual common-target conditional output coefficients and their uniform
limits over arbitrary varying retained source families. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical Topology
open Filter
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def partitionTransitionOutput (μ ν : Fin d → ℕ) (hμ : Antitone μ) (hν : Antitone ν)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) :
    PositiveTraceClass (cyclicSector (partitionHighestTensor ν hν)) :=
  (partitionGibbsPositive μ hμ p hp).map (partitionTransitionChannel μ ν hμ hν).toPositiveTracePreservingMap

theorem partitionTransitionOutput_norm (μ ν : Fin d → ℕ) (hμ : Antitone μ) (hν : Antitone ν)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) : ‖(partitionTransitionOutput μ ν hμ hν p hp).1‖ = 1 := by
  rw [partitionTransitionOutput, PositiveTraceClass.norm_map, partitionGibbsPositive_norm]

def partitionTransitionCoefficient (μ ν : Fin d → ℕ) (hμ : Antitone μ) (hν : Antitone ν)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (R : ℕ) (i j : CutoffIndex d R) : ℂ :=
  ⟪cutoffSectorFrame (partitionHighestTensor ν hν) ν R i,
    (partitionTransitionOutput μ ν hμ hν p hp).1.1
      (cutoffSectorFrame (partitionHighestTensor ν hν) ν R j)⟫_ℂ

theorem partitionTransitionCoefficient_add (μ τ : Fin d → ℕ) (hμ : Antitone μ) (hτ : Antitone τ)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (R : ℕ) (i j : CutoffIndex d R) :
    partitionTransitionCoefficient μ (fun a => μ a+τ a) hμ (sumPartition_antitone μ τ hμ hτ) p hp R i j =
      ⟪cutoffSectorFrame (partitionHighestTensor _ (sumPartition_antitone μ τ hμ hτ)) (fun a => μ a+τ a) R i,
        (cartanGibbsOutput μ τ hμ hτ p).1
          (cutoffSectorFrame (partitionHighestTensor _ (sumPartition_antitone μ τ hμ hτ)) (fun a => μ a+τ a) R j)⟫_ℂ := by
  unfold partitionTransitionCoefficient partitionTransitionOutput
  rw [partitionTransitionChannel_add]
  rfl

/-- The row-frequency hypotheses alone imply the actual conditional output
coefficient limit, with finitely many incompatible indices handled internally. -/
theorem partitionTransitionCoefficient_tendsto_of_scaled
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (μ ν : ℕ → Fin d → ℕ) (hμ : ∀ N, Antitone (μ N)) (hν : ∀ N, Antitone (ν N))
    (pN : ℕ → Fin d → ℝ) (hpN : ∀ N a, 0 < pN N a)
    (p : SimpleSpectrum d) (hlim : ∀ a, Tendsto (fun N => pN N a) atTop (𝓝 (p.eigenvalue a)))
    (γ : ℝ) (hγ : 1 < γ)
    (hμlim : ∀ a, Tendsto (fun N => (μ N a : ℝ)/(n N : ℝ)) atTop (𝓝 (p.eigenvalue a)))
    (hνlim : ∀ a, Tendsto (fun N => (ν N a : ℝ)/(n N : ℝ)) atTop (𝓝 (γ*p.eigenvalue a)))
    (R : ℕ) (i j : CutoffIndex d R) :
    Tendsto (fun N => partitionTransitionCoefficient (μ N) (ν N) (hμ N) (hν N) (pN N) (hpN N) R i j)
      atTop (𝓝 (if i=j then
        (amplifiedOccupationWeight (fun _ => γ⁻¹) (rootBoltzmann p.eigenvalue) (cutoffOccupation d R i).val : ℂ) else 0)) := by
  have hc := eventually_partitionCompatible_of_scaled_limits n hn μ ν p.eigenvalue p.positive p.strictAnti
    γ hγ hμlim hνlim
  obtain ⟨δμ,hδμ,hgμ⟩ := exists_root_gap_of_scaled_limits n hn μ p.eigenvalue p.positive p.strictAnti hμlim
  obtain ⟨δτ,hδτ,hgτ⟩ := exists_root_gap_of_scaled_limits n hn (fun N a => ν N a-μ N a)
    (fun a => (γ-1)*p.eigenvalue a) (fun a => mul_pos (sub_pos.mpr hγ) (p.positive a))
    (fun a b hab => mul_lt_mul_of_pos_left (p.strictAnti hab) (sub_pos.mpr hγ))
    (difference_scaled_tendsto n μ ν p.eigenvalue γ hμlim hνlim hc)
  have ht := rootFraction_difference_tendsto n hn μ ν p.eigenvalue p.strictAnti γ (by linarith) hμlim hνlim hc
  let τ : ℕ → Fin d → ℕ := fun N => if Antitone (fun a => ν N a-μ N a) then
    (fun a => ν N a-μ N a) else fun _ => 0
  have hτ N : Antitone (τ N) := by
    dsimp only [τ]
    split_ifs with h
    · exact h
    · intro a b _; rfl
  have he : ∀ᶠ N in atTop, τ N = (fun a => ν N a-μ N a) :=
    hc.mono (fun N hN => by simp only [τ,if_pos hN.2])
  have hτgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δτ N ≤ rootGap (τ N) a := by
    filter_upwards [he,hgτ] with N hN hg
    simpa only [hN] using hg
  have hτfraction a : Tendsto (fun N => rootFraction (μ N) (τ N) a) atTop (𝓝 γ⁻¹) :=
    (ht a).congr' (he.mono (fun N hN => by
      change rootFraction (μ N) (fun a => ν N a-μ N a) a = rootFraction (μ N) (τ N) a
      rw [hN]))
  have hf := cartanGibbsOutput_cutoff_coefficient_tendsto μ τ hμ hτ δμ δτ hδμ hδτ hgμ hτgap
    (fun _ => γ⁻¹) (fun _ => (inv_pos.mpr (by linarith : 0 < γ)).le)
    (fun _ => (inv_le_one₀ (by linarith : 0 < γ)).mpr hγ.le) hτfraction
    pN p.eigenvalue p.positive p.strictAnti hlim R i j
  apply hf.congr'
  filter_upwards [he,hc] with N hN hNc
  have hs : (fun a => μ N a+τ N a) = ν N := by
    funext a
    rw [hN]
    exact Nat.add_sub_of_le (hNc.1 a)
  have hh := partitionTransitionCoefficient_add (μ N) (τ N) (hμ N) (hτ N) (pN N) (hpN N) R i j
  simpa only [hs] using hh.symm

/-- Uniformity over a varying source family follows from the physical row
frequencies. The cardinality of the retained family is unrestricted. -/
theorem partitionTransitionCoefficient_uniform
    {J : ℕ → Type*} (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (μ : ∀ N, J N → Fin d → ℕ) (ν : ℕ → Fin d → ℕ)
    (hμ : ∀ N a, Antitone (μ N a)) (hν : ∀ N, Antitone (ν N))
    (pN : ℕ → Fin d → ℝ) (hpN : ∀ N a, 0 < pN N a)
    (p : SimpleSpectrum d) (hlim : ∀ a, Tendsto (fun N => pN N a) atTop (𝓝 (p.eigenvalue a)))
    (γ : ℝ) (hγ : 1 < γ)
    (hμlim : ∀ a ε, 0 < ε → ∀ᶠ N in atTop, ∀ j : J N,
      |(μ N j a : ℝ)/(n N : ℝ)-p.eigenvalue a| < ε)
    (hνlim : ∀ a, Tendsto (fun N => (ν N a : ℝ)/(n N : ℝ)) atTop (𝓝 (γ*p.eigenvalue a)))
    (R : ℕ) (i j : CutoffIndex d R) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ a : J N,
      ‖partitionTransitionCoefficient (μ N a) (ν N) (hμ N a) (hν N) (pN N) (hpN N) R i j -
        (if i=j then (amplifiedOccupationWeight (fun _ => γ⁻¹) (rootBoltzmann p.eigenvalue)
          (cutoffOccupation d R i).val : ℂ) else 0)‖ < ε := by
  have hh := eventually_uniform_of_subsequences (fun N (_ : J N) => True)
    (fun N a => ‖partitionTransitionCoefficient (μ N a) (ν N) (hμ N a) (hν N) (pN N) (hpN N) R i j -
      (if i=j then (amplifiedOccupationWeight (fun _ => γ⁻¹) (rootBoltzmann p.eigenvalue)
        (cutoffOccupation d R i).val : ℂ) else 0)‖ < ε) (by
      intro φ hφ a _
      have hm b : Tendsto (fun k => (μ (φ k) (a k) b : ℝ)/(n (φ k) : ℝ)) atTop (𝓝 (p.eigenvalue b)) := by
        apply Metric.tendsto_nhds.mpr
        intro η hη
        filter_upwards [hφ.eventually (hμlim b η hη)] with k hk
        simpa only [Real.dist_eq] using hk (a k)
      have hf := partitionTransitionCoefficient_tendsto_of_scaled (fun k => n (φ k)) (hn.comp hφ)
        (fun k => μ (φ k) (a k)) (fun k => ν (φ k)) (fun k => hμ (φ k) (a k)) (fun k => hν (φ k))
        (fun k => pN (φ k)) (fun k => hpN (φ k)) p (fun b => (hlim b).comp hφ) γ hγ hm
        (fun b => (hνlim b).comp hφ) R i j
      simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp hf ε hε)
  exact hh.mono (fun N hN a => hN a trivial)

end Cloning.TensorCloning
