import Cloning.TensorCloningAchievabilitySector
import Cloning.TensorCloningAchievabilityUniform

/-! Unconditional known-spectrum achievability for the actual physical
cloning channel. All sector, concentration, compatibility and normalization
obligations are discharged by the constructed representations and states. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical Topology Matrix
open Filter
namespace Cloning.TensorCloning
open Cloning.TensorLie Cloning.TensorLAN
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The genuine conditional channel fidelity is uniformly bounded below on
all physical typical label pairs and the entire unitary orbit. -/
theorem eventually_uniform_typical_transitionFidelity {d : ℕ}
    (n m : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (p : SimpleSpectrum (d+1)) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun k => (m k : ℝ)/(n k : ℝ)) atTop (𝓝 γ))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ ij : SchurCopy (n k) (d+1) × SchurCopy (m k) (d+1),
      jointTypical (n k) (m k) (d+1) p.eigenvalue ij →
      ∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
        orbitalValue γ p-η ≤ transitionFidelity (n k) (m k) (d+1) p.eigenvalue p.positive U ij.1 ij.2 := by
  apply eventually_uniform_of_subsequences
  intro φ hφ ij htyp
  let μ k := ((recursivePhysicalDecomposition (n (φ k)) (d+1)).get (ij k).1).weight
  let ν k := ((recursivePhysicalDecomposition (m (φ k)) (d+1)).get (ij k).2).weight
  have hμ k : Antitone (μ k) := ((recursivePhysicalDecomposition (n (φ k)) (d+1)).get (ij k).1).weight_antitone
  have hν k : Antitone (ν k) := ((recursivePhysicalDecomposition (m (φ k)) (d+1)).get (ij k).2).weight_antitone
  have hμtyp : ∀ᶠ k in atTop, TypicalLabel (n (φ k)) p.eigenvalue (μ k) := htyp.mono (fun _ hk => hk.1)
  have hνtyp : ∀ᶠ k in atTop, TypicalLabel (m (φ k)) p.eigenvalue (ν k) := htyp.mono (fun _ hk => hk.2)
  have hf := partitionTransitionFidelity_tendsto_of_typical (fun k => n (φ k)) (fun k => m (φ k))
    (hn.comp hφ) (hm.comp hφ) μ ν hμ hν p γ hγ (hgain.comp hφ) hμtyp hνtyp
  obtain ⟨_,_,_,_,hc,_,_,_⟩ := typical_pair_cartan_parameters (fun k => n (φ k)) (fun k => m (φ k))
    (hn.comp hφ) (hm.comp hφ) μ ν p.eigenvalue p.positive p.strictAnti γ hγ (hgain.comp hφ) hμtyp hνtyp
  filter_upwards [hc, hf.eventually (eventually_gt_nhds (show orbitalValue γ p-η < orbitalValue γ p by linarith))]
    with k hck hfk U
  rw [transitionFidelity_unitary _ _ _ _ _ _ (Unitary.star_mul_self_of_mem U.property) _ _ hck,
    transitionFidelity_one_eq]
  exact hfk.le

/-- A concrete all-input CPTP map attains the orbital value asymptotically,
uniformly over the unknown eigenbasis. No LAN or sector-limit premise remains. -/
theorem eventually_knownSpectrumChannel_payoff_lower {d : ℕ}
    (n m : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (p : SimpleSpectrum (d+1)) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun k => (m k : ℝ)/(n k : ℝ)) atTop (𝓝 γ))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
      orbitalValue γ p-ε < spectrumPayoff (n k) (m k)
        (knownSpectrumChannel (n k) (m k) (d+1) p.eigenvalue
          (fun a => (p.positive a).le) p.normalized) p U :=
  eventually_knownSpectrumChannel_payoff_lower_of_typical n m hn hm p (orbitalValue γ p)
    (orbitalValue_le_one hγ p)
    (eventually_uniform_typical_transitionFidelity n m hn hm p γ hγ hgain) ε hε

/-- The genuine finite-sample optimization over every physical CPTP map has
the same eventual known-spectrum lower bound. -/
theorem eventually_knownSpectrumValue_lower {d : ℕ}
    (n m : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (p : SimpleSpectrum (d+1)) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun k => (m k : ℝ)/(n k : ℝ)) atTop (𝓝 γ))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, orbitalValue γ p-ε < knownSpectrumValue (n k) (m k) p := by
  filter_upwards [eventually_knownSpectrumChannel_payoff_lower n m hn hm p γ hγ hgain (ε/2) (by positivity)]
    with k hk
  have hh := LAN.candidate_le_minimaxValue
    (fun Φ U => spectrumPayoff (n k) (m k) Φ p U)
    (knownSpectrumChannel (n k) (m k) (d+1) p.eigenvalue (fun a => (p.positive a).le) p.normalized)
    (orbitalValue γ p-ε/2)
    (fun Φ U => spectrumPayoff_le_one _ _ Φ p U)
    (fun U => (hk U).le) (fun Φ U => spectrumPayoff_nonneg _ _ Φ p U)
  change orbitalValue γ p-ε/2 ≤ knownSpectrumValue (n k) (m k) p at hh
  linarith

end Cloning.TensorCloning
