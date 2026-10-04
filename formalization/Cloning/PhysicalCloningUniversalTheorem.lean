import Cloning.TensorCloningUniversalAchievability
import Cloning.PhysicalCloningConverseUnconditional

/-! The unconditional asymptotic universal mixed-state cloning theorem for
the genuine optimization over all physical CPTP maps. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ}

theorem unknownSpectrumValue_le_one (n m : ℕ) (K : Set (SimpleSpectrum (d+1)))
    (hKne : K.Nonempty) : unknownSpectrumValue n m K ≤ 1 := by
  letI : Nonempty (QuantumChannel (Register (Fin n → Fin (d+1)))
      (Register (Fin m → Fin (d+1)))) := ⟨universalChannel n m d⟩
  obtain ⟨p,hp⟩ := hKne
  unfold unknownSpectrumValue LAN.minimaxValue
  apply ciSup_le
  intro Φ
  have hb : BddBelow (Set.range (fun θ : K × unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ) ↦
      spectrumPayoff n m Φ θ.1.val θ.2)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨θ,rfl⟩
    exact spectrumPayoff_nonneg n m Φ θ.1.val θ.2
  exact (ciInf_le hb (⟨p,hp⟩,1)).trans (spectrumPayoff_le_one n m Φ p 1)

/-- The exact limiting optimal root fidelity for a compact nonempty regular
closed set of simple positive spectra. The same explicit universal channel
achieves the bound uniformly over every spectrum and eigenbasis in the set. -/
theorem unknownSpectrumValue_tendsto (hd : 1 ≤ d)
    (K : Set (SimpleSpectrum (d+1))) (hK : IsCompact K) (hKne : K.Nonempty)
    (hregular : closure (interior K) = K)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun n ↦ (m n : ℝ)/n) atTop (𝓝 γ)) :
    Tendsto (fun n ↦ unknownSpectrumValue n (m n) K) atTop
      (𝓝 (⨅ p : K, universalValue γ p.val)) := by
  have hu := PhysicalCloningConverse.limsup_unknownSpectrumValue_infimum K hKne hregular m γ hγ hgain
  have hb : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) (fun n ↦ unknownSpectrumValue n (m n) K) := by
    exact Filter.isBoundedUnder_of_eventually_le
      (Eventually.of_forall (fun n : ℕ ↦ unknownSpectrumValue_le_one n (m n) K hKne))
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have h := eventually_unknownSpectrumValue_lower hd K hK hKne m γ hγ hgain
      ((⨅ p : K, universalValue γ p.val)-a) (sub_pos.mpr ha)
    simpa only [sub_sub_cancel] using h
  · intro a ha
    exact eventually_lt_of_limsup_lt (hu.trans_lt ha) hb

end Cloning.TensorCloning
