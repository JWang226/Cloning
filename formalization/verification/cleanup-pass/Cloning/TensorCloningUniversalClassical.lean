import Cloning.TensorCloningUniversalError
import Cloning.PhysicalCloningConverseSpectrum

/-! Uniform global payoff assembly for the actual universal cloning protocol,
combining its physical classical fidelity and its retained sector estimate. -/
noncomputable section
open scoped BigOperators Classical Topology Matrix
namespace Cloning.TensorCloning
open Cloning.TensorLie Cloning.TensorLAN Cloning.YoungGeneral Cloning.YoungCompatibility
open Cloning.YoungHyperplane Filter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem eventually_uniform_universalAffinity {d : ℕ} (hd : 1 ≤ d)
    (K : Set (SimpleSpectrum (d+1))) (hK : IsCompact K)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun n ↦ (m n : ℝ)/n) atTop (𝓝 γ)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ p ∈ K, |universalAffinity n (m n) d p - classicalValue γ (d+1)| < ε := by
  let J := SimpleSpectrum.eigenvalue '' K
  have hJ : IsCompact J := hK.image SimpleSpectrum.continuous_eigenvalue
  have hp : ∀ p ∈ J, ∑ a, p a = 1 := by
    rintro q ⟨p,hp,rfl⟩
    exact p.normalized
  have hp0 : ∀ p ∈ J, ∀ a, 0 < p a := by
    rintro q ⟨p,hp,rfl⟩
    exact p.positive
  have hord : ∀ p ∈ J, StrictAnti p := by
    rintro q ⟨p,hp,rfl⟩
    exact p.strictAnti
  obtain ⟨N,hN⟩ := uniform_tensorYoungFallbackOutput_affinity hd J hJ hp hp0 hord m hm γ hγ hgain ε hε
  filter_upwards [eventually_ge_atTop N] with n hn p hpK
  exact hN n hn p.eigenvalue ⟨p,hpK,rfl⟩

/-- Once the physical retained-sector bound is available uniformly, every
other global approximation term is a proved property of the actual protocol. -/
theorem eventually_universalChannel_payoff_lower_of_sector {d : ℕ} (hd : 1 ≤ d)
    (K : Set (SimpleSpectrum (d+1))) (hK : IsCompact K)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun n ↦ (m n : ℝ)/n) atTop (𝓝 γ))
    (hsector : ∀ η > 0, ∀ᶠ n in atTop, ∀ p ∈ K,
      ∀ (i : SchurCopy n (d+1)) (j : SchurCopy (m n) (d+1)),
        universalKeep n (m n) d p.eigenvalue i j →
      ∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
        orbitalValue γ p-η ≤ transitionFidelity n (m n) (d+1) p.eigenvalue p.positive U i j)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ p ∈ K, ∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
      universalValue γ p-ε < spectrumPayoff n (m n) (universalChannel n (m n) d) p U := by
  have ht : Tendsto (fun n ↦ Real.sqrt (universalTailEnvelope d n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (universalTailEnvelope_tendsto_zero d).sqrt
  filter_upwards [hsector (ε/3) (by positivity),
    eventually_uniform_universalAffinity hd K hK m hm γ hγ hgain (ε/3) (by positivity),
    ht.eventually (eventually_lt_nhds (show (0 : ℝ) < ε/3 by positivity)), eventually_ge_atTop 1]
    with n hn hc ht hn0 p hpK U
  have hf := universalChannel_payoff_lower_error n (m n) p U γ hγ (ε/3) (by positivity)
    (fun i j hij ↦ hn p hpK i j hij U)
  have hb := Real.sqrt_le_sqrt (copyBadMass_le_universalTailEnvelope n hn0 p)
  have ha := hc p hpK
  linarith

theorem eventually_unknownSpectrumValue_lower_of_channel {d : ℕ}
    (K : Set (SimpleSpectrum (d+1))) (hKne : K.Nonempty)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hchannel : ∀ ε > 0, ∀ᶠ n in atTop, ∀ p ∈ K,
      ∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
        universalValue γ p-ε < spectrumPayoff n (m n) (universalChannel n (m n) d) p U)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, (⨅ p : K, universalValue γ p.val)-ε < unknownSpectrumValue n (m n) K := by
  letI : Nonempty K := hKne.to_subtype
  have hbdd : BddBelow (Set.range (fun p : K ↦ universalValue γ p.val)) :=
    ⟨0, by rintro _ ⟨p,rfl⟩; exact (universalValue_pos hγ p.val).le⟩
  filter_upwards [hchannel (ε/2) (by positivity)] with n hn
  have hh := LAN.candidate_le_minimaxValue
    (fun Φ (θ : K × unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) ↦ spectrumPayoff n (m n) Φ θ.1.val θ.2)
    (universalChannel n (m n) d) ((⨅ p : K, universalValue γ p.val)-ε/2)
    (fun Φ θ ↦ spectrumPayoff_le_one _ _ Φ θ.1.val θ.2)
    (fun θ ↦ by
      have hI := ciInf_le hbdd θ.1
      have hp := hn θ.1.val θ.1.property θ.2
      linarith)
    (fun Φ θ ↦ spectrumPayoff_nonneg _ _ Φ θ.1.val θ.2)
  change (⨅ p : K, universalValue γ p.val)-ε/2 ≤ unknownSpectrumValue n (m n) K at hh
  linarith

end Cloning.TensorCloning
