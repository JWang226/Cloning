import Cloning.TensorLANEmbeddingLocalSpectrum
import Cloning.TensorGibbsPhysicalLANUniform
import Cloning.WeylMultimodeChannel
import Mathlib.Topology.Sequences

/-! Uniform physical sector estimates on typical Young labels. The compression
cutoff is chosen before the sample size, label and local parameter. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace
open Filter
namespace Cloning.TensorLAN
open Cloning.PCT Cloning.TensorLie Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
open Cloning.TensorLocalUnitary
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

 theorem continuous_rootDisplacedThermal (p : Fin d → ℝ) :
    Continuous (rootDisplacedThermal p) := by
  have h : Continuous (rootFockAmplitude : (PositiveRoot d → ℂ) → _) := by
    apply continuous_pi
    intro a
    exact continuous_apply _
  simpa only [Function.comp_def, displacementTraceMap_eq_channel, rootDisplacedThermal] using
    (continuous_displacementTraceMap (rootThermalState p)).comp h

 theorem physicalGibbsForwardError_change_target (mu : Fin d → ℕ) (hmu : Antitone mu)
    (r p : Fin d → ℝ) (z z₀ z₁ : PositiveRoot d → ℂ) (Q : ℕ) :
    physicalGibbsForwardError mu hmu r p z z₁ Q ≤
      physicalGibbsForwardError mu hmu r p z z₀ Q +
        ‖rootDisplacedThermal p z₀-rootDisplacedThermal p z₁‖ :=
  norm_sub_le_norm_sub_add_norm_sub _ _ _

 theorem physicalGibbsReverseError_change_target (mu : Fin d → ℕ) (hmu : Antitone mu)
    (r p : Fin d → ℝ) (z z₀ z₁ : PositiveRoot d → ℂ) (Q : ℕ) :
    physicalGibbsReverseError mu hmu r p z z₁ Q ≤
      physicalGibbsReverseError mu hmu r p z z₀ Q +
        2*‖rootDisplacedThermal p z₀-rootDisplacedThermal p z₁‖ := by
  let Φ := fockToSectorTotal (partitionHighestTensor mu hmu) mu Q (partitionHighestTensor_norm mu hmu)
  have h := norm_sub_le_norm_sub_add_norm_sub (Φ.toLinearMap (rootDisplacedThermal p z₁))
    (Φ.toLinearMap (rootDisplacedThermal p z₀)) (partitionPhysicalGibbs mu hmu r p z)
  have hn := Φ.toPositiveTracePreservingMap.norm_map_le_two_mul
    (rootDisplacedThermal p z₁-rootDisplacedThermal p z₀)
  rw [map_sub, norm_sub_rev (rootDisplacedThermal p z₁)] at hn
  change physicalGibbsReverseError mu hmu r p z z₁ Q ≤ _
  change _ ≤ 2 * _ at hn
  change physicalGibbsReverseError mu hmu r p z z₁ Q ≤
    _ + physicalGibbsReverseError mu hmu r p z z₀ Q at h
  linarith

/-- The actual two-way sector errors are uniformly small on all typical labels
and bounded local spectral perturbations, for every fixed sufficiently large
compression cutoff. No partition frequency or root-gap premise remains. -/
theorem exists_cutoff_uniform_typical_physical_gibbs
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p)
    (B : ℝ) (K : Set (PositiveRoot d → ℂ)) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ Q ≥ Q₀, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (mu : Fin d → ℕ) (hmu : Antitone mu), (∑ a, mu a) = N →
      ∀ h : Fin d → ℝ, ‖h‖ ≤ B → ∀ z ∈ K,
      TypicalLabel N (localSpectrum p h N) mu →
      physicalGibbsForwardError mu hmu (localSpectrum p h N) p z z Q < ε ∧
      physicalGibbsReverseError mu hmu (localSpectrum p h N) p z z Q < ε := by
  obtain ⟨C,hC,hKC⟩ := hK.isBounded.exists_pos_norm_le
  have hCZ : ∀ z ∈ K, (∑ a, ‖z a‖) ≤ (Fintype.card (PositiveRoot d) : ℝ)*C := by
    intro z hz
    calc
      (∑ a, ‖z a‖) ≤ ∑ _a : PositiveRoot d, C :=
        Finset.sum_le_sum fun a _ => (norm_le_pi_norm z a).trans (hKC z hz)
      _ = _ := by simp
  obtain ⟨Q₀,hQ₀⟩ := exists_uniform_cutoff_eventually_twoWay_physical_gibbs p hp hord
    ((Fintype.card (PositiveRoot d) : ℝ)*C) (by positivity) (ε/4) (by positivity)
  refine ⟨Q₀,?_⟩
  intro Q hQ
  by_contra hbad
  push_neg at hbad
  choose n hn mu hmu hsum h hh z hz htyp hfail using hbad
  obtain ⟨z₀,hz₀,φ,hφ,hzlim⟩ := hK.tendsto_subseq hz
  have hnlim : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  have hnφ : Tendsto (fun k => n (φ k)) atTop atTop := hnlim.comp hφ.tendsto_atTop
  have hr (a : Fin d) : Tendsto
      (fun k => localSpectrum p (h (φ k)) (n (φ k)) a) atTop (𝓝 (p a)) :=
    localSpectrum_tendsto_of_bounded p _ hnφ _ B (Eventually.of_forall fun k => hh (φ k)) a
  have htypφ : ∀ᶠ k in atTop, TypicalLabel (n (φ k))
      (localSpectrum p (h (φ k)) (n (φ k))) (mu (φ k)) :=
    Eventually.of_forall fun k => htyp (φ k)
  have hfreq : Tendsto (fun k => fun a => (mu (φ k) a : ℝ) /
      ((∑ b, mu (φ k) b : ℕ) : ℝ)) atTop (𝓝 p) := by
    apply tendsto_pi_nhds.mpr
    intro a
    simpa only [hsum] using typicalLabel_ratio_tendsto _ hnφ _ _ p hr htypφ a
  obtain ⟨c,hc,hgap⟩ := typicalLabel_uniform_root_gap p hord
  have hδ : Tendsto (fun k => c*(n (φ k) : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).mpr (tendsto_natCast_atTop_atTop.comp hnφ)
  have hg : ∀ᶠ k in atTop, ∀ a : PositiveRoot d,
      c*(n (φ k) : ℝ) ≤ rootGap (mu (φ k)) a := by
    simpa only [rootGap] using hgap _ hnφ _ _ hr htypφ
  have he := hQ₀ Q hQ (fun k => mu (φ k)) (fun k => hmu (φ k))
    _ hδ hg _ hr hfreq _ z₀ hzlim (hCZ z₀ hz₀)
  have hthermal : Tendsto (fun k =>
      ‖rootDisplacedThermal p z₀-rootDisplacedThermal p (z (φ k))‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds (x := rootDisplacedThermal p z₀)).sub
        ((continuous_rootDisplacedThermal p).tendsto z₀ |>.comp hzlim)).norm
  obtain ⟨k,hkf,hkt⟩ := (he.and (hthermal.eventually (eventually_lt_nhds
    (show 0 < ε/4 by positivity)))).exists
  dsimp only [Function.comp_def] at hkf
  have hforward := physicalGibbsForwardError_change_target (mu (φ k)) (hmu (φ k))
    (localSpectrum p (h (φ k)) (n (φ k))) p (z (φ k)) z₀ (z (φ k)) Q
  have hreverse := physicalGibbsReverseError_change_target (mu (φ k)) (hmu (φ k))
    (localSpectrum p (h (φ k)) (n (φ k))) p (z (φ k)) z₀ (z (φ k)) Q
  have hf : physicalGibbsForwardError (mu (φ k)) (hmu (φ k))
      (localSpectrum p (h (φ k)) (n (φ k))) p (z (φ k)) (z (φ k)) Q < ε := by
    linarith [hkf.1]
  have hr := hfail (φ k) hf
  linarith [hkf.2]

end Cloning.TensorLAN
