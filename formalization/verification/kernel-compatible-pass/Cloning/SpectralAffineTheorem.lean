import Cloning.SpectralAffineTopology
import Cloning.PhysicalCloningUniversalTheorem

/-! The physical universal minimax theorem with the manuscript's regular
closure hypothesis stated in the full trace-one affine hyperplane. -/
noncomputable section
open scoped Topology
open Filter
namespace Cloning.TensorCloning
variable {d : ℕ}

theorem unknownSpectrumValue_tendsto_affine (hd : 1 ≤ d)
    (K : Set (SimpleSpectrum (d+1))) (hK : IsCompact K) (hKne : K.Nonempty)
    (hregular : closure (interior (SimpleSpectrum.toAffine '' K)) =
      SimpleSpectrum.toAffine '' K)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun n ↦ (m n : ℝ)/n) atTop (𝓝 γ)) :
    Tendsto (fun n ↦ unknownSpectrumValue n (m n) K) atTop
      (𝓝 (⨅ p : K, universalValue γ p.val)) :=
  unknownSpectrumValue_tendsto hd K hK hKne
    (SimpleSpectrum.regularClosure_of_affine K hregular) m γ hγ hgain

end Cloning.TensorCloning
