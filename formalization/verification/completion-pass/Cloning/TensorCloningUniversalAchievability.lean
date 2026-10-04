import Cloning.TensorCloningUniversalClassical
import Cloning.TensorCloningUniversalSector
import Cloning.PhysicalCloningConverseUnknown

/-! Unconditional compact-uniform achievability for the actual universal
cloning channel, including its exact classical rounding cost. -/
noncomputable section
open scoped BigOperators Classical Topology Matrix
namespace Cloning.TensorCloning
open Cloning.TensorLie Cloning.TensorLAN Cloning.PhysicalCloningConverse Filter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem eventually_universalChannel_payoff_lower {d : ℕ} (hd : 1 ≤ d)
    (K : Set (SimpleSpectrum (d+1))) (hK : IsCompact K)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun n ↦ (m n : ℝ)/n) atTop (𝓝 γ))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ p ∈ K, ∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
      universalValue γ p-ε < spectrumPayoff n (m n) (universalChannel n (m n) d) p U :=
  eventually_universalChannel_payoff_lower_of_sector hd K hK m
    (output_size_tendsto m γ (by linarith) hgain) γ hγ hgain
    (eventually_uniform_universalKeep_transitionFidelity hd K hK m γ hγ hgain) ε hε

theorem eventually_unknownSpectrumValue_lower {d : ℕ} (hd : 1 ≤ d)
    (K : Set (SimpleSpectrum (d+1))) (hK : IsCompact K) (hKne : K.Nonempty)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun n ↦ (m n : ℝ)/n) atTop (𝓝 γ))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, (⨅ p : K, universalValue γ p.val)-ε < unknownSpectrumValue n (m n) K :=
  eventually_unknownSpectrumValue_lower_of_channel K hKne m γ hγ
    (eventually_universalChannel_payoff_lower hd K hK m γ hγ hgain) ε hε

end Cloning.TensorCloning
