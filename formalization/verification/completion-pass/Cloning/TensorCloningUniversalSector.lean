import Cloning.TensorCloningUniversalFrequencies
import Cloning.TensorCloningAchievabilitySector
import Cloning.PhysicalCloningConverseSpectrum

/-! Compact-uniform fidelity of the actual retained universal sector
transitions. The physical rounding support and Cartan state limit discharge
all compatibility, root-gap and conditional-fidelity hypotheses. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical Topology Matrix
open Filter
namespace Cloning.TensorCloning
open Cloning.TensorLie Cloning.TensorLAN
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Along every retained physical transition and converging moving spectrum,
the actual centered conditional fidelity has the orbital limit. -/
theorem universalKeep_transitionFidelity_tendsto {d : ℕ} (hd : 1 ≤ d)
    (K : Set (SimpleSpectrum (d+1))) (hK : IsCompact K)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (pN : ℕ → SimpleSpectrum (d+1)) (hpK : ∀ k, pN k ∈ K)
    (p : SimpleSpectrum (d+1))
    (hlim : ∀ a, Tendsto (fun k => (pN k).eigenvalue a) atTop (𝓝 (p.eigenvalue a)))
    (i : (k : ℕ) → SchurCopy (n k) (d+1))
    (j : (k : ℕ) → SchurCopy (m (n k)) (d+1))
    (hkeep : ∀ k, universalKeep (n k) (m (n k)) d (pN k).eigenvalue (i k) (j k)) :
    Tendsto (fun k => transitionFidelity (n k) (m (n k)) (d+1)
      (pN k).eigenvalue (pN k).positive 1 (i k) (j k)) atTop (𝓝 (orbitalValue γ p)) := by
  let E := SimpleSpectrum.eigenvalue '' K
  have hEc : IsCompact E := hK.image SimpleSpectrum.continuous_eigenvalue
  have hEp : ∀ q ∈ E, ∀ a, 0 < q a := by
    rintro q ⟨s,hs,rfl⟩
    exact s.positive
  have hEo : ∀ q ∈ E, StrictAnti q := by
    rintro q ⟨s,hs,rfl⟩
    exact s.strictAnti
  let μ k := ((recursivePhysicalDecomposition (n k) (d+1)).get (i k)).weight
  let ν k := ((recursivePhysicalDecomposition (m (n k)) (d+1)).get (j k)).weight
  have hμ k : Antitone (μ k) := ((recursivePhysicalDecomposition (n k) (d+1)).get (i k)).weight_antitone
  have hν k : Antitone (ν k) := ((recursivePhysicalDecomposition (m (n k)) (d+1)).get (j k)).weight_antitone
  obtain ⟨hμlim,hνlim⟩ := universalKeep_scaled_limits hd E hEc hEp hEo m γ hγ hgain n hn
    (fun k => (pN k).eigenvalue) (fun k => ⟨pN k,hpK k,rfl⟩) p.eigenvalue hlim i j hkeep
  have hc := eventually_partitionCompatible_of_scaled_limits n hn μ ν p.eigenvalue p.positive p.strictAnti
    γ hγ hμlim hνlim
  obtain ⟨δμ,hδμ,hgμ⟩ := exists_root_gap_of_scaled_limits n hn μ p.eigenvalue p.positive p.strictAnti hμlim
  obtain ⟨δτ,hδτ,hgτ⟩ := exists_root_gap_of_scaled_limits n hn (fun k a => ν k a-μ k a)
    (fun a => (γ-1)*p.eigenvalue a) (fun a => mul_pos (sub_pos.mpr hγ) (p.positive a))
    (fun a b hab => mul_lt_mul_of_pos_left (p.strictAnti hab) (sub_pos.mpr hγ))
    (difference_scaled_tendsto n μ ν p.eigenvalue γ hμlim hνlim hc)
  have ht := rootFraction_difference_tendsto n hn μ ν p.eigenvalue p.strictAnti γ
    (by linarith) hμlim hνlim hc
  have hf := partitionTransitionFidelity_tendsto_moving μ ν hμ hν δμ δτ hδμ hδτ hc hgμ hgτ
    (fun k => (pN k).eigenvalue) (fun k => (pN k).positive) p hlim γ hγ ht
  simpa only [transitionFidelity_one_eq, μ, ν] using hf

/-- Uniform absolute convergence of centered sector fidelities over every
compact family of strict positive normalized spectra. -/
theorem eventually_uniform_universalKeep_transitionFidelity_one_abs {d : ℕ} (hd : 1 ≤ d)
    (K : Set (SimpleSpectrum (d+1))) (hK : IsCompact K)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ p ∈ K, ∀ (i : SchurCopy n (d+1)) (j : SchurCopy (m n) (d+1)),
      universalKeep n (m n) d p.eigenvalue i j →
      |transitionFidelity n (m n) (d+1) p.eigenvalue p.positive 1 i j - orbitalValue γ p| < ε := by
  rw [eventually_atTop]
  by_contra h
  push_neg at h
  choose n hn p hpK i j hkeep hb using h
  have hnlim : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  have hE := hK.image SimpleSpectrum.continuous_eigenvalue
  obtain ⟨q,hq,φ,hφ,hconv⟩ := hE.tendsto_subseq
    (fun k => show (p k).eigenvalue ∈ SimpleSpectrum.eigenvalue '' K from ⟨p k,hpK k,rfl⟩)
  obtain ⟨p₀,hp₀,rfl⟩ := hq
  have hlim a : Tendsto (fun k => (p (φ k)).eigenvalue a) atTop (𝓝 (p₀.eigenvalue a)) :=
    (continuous_apply a).continuousAt.tendsto.comp hconv
  have hf := universalKeep_transitionFidelity_tendsto hd K hK m γ hγ hgain
    (fun k => n (φ k)) (hnlim.comp hφ.tendsto_atTop) (fun k => p (φ k))
    (fun k => hpK (φ k)) p₀ hlim (fun k => i (φ k)) (fun k => j (φ k)) (fun k => hkeep (φ k))
  have hpconv : Tendsto (fun k => p (φ k)) atTop (𝓝 p₀) :=
    SimpleSpectrum.isEmbedding_eigenvalue.tendsto_nhds_iff.mpr hconv
  have ho := (continuous_orbitalValue (by linarith : 0 < γ)).continuousAt.tendsto.comp hpconv
  have he := hf.sub ho
  rw [sub_self] at he
  obtain ⟨k,hk⟩ := (Metric.tendsto_nhds.mp he ε hε).exists
  rw [Real.dist_eq, sub_zero] at hk
  exact (not_lt_of_ge (hb (φ k))) hk

/-- The same absolute estimate holds on the entire unknown unitary orbit,
because every retained physical transition is eventually compatible. -/
theorem eventually_uniform_universalKeep_transitionFidelity_abs {d : ℕ} (hd : 1 ≤ d)
    (K : Set (SimpleSpectrum (d+1))) (hK : IsCompact K)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ p ∈ K, ∀ (i : SchurCopy n (d+1)) (j : SchurCopy (m n) (d+1)),
      universalKeep n (m n) d p.eigenvalue i j →
      ∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
      |transitionFidelity n (m n) (d+1) p.eigenvalue p.positive U i j - orbitalValue γ p| < ε := by
  let E := SimpleSpectrum.eigenvalue '' K
  have hEc : IsCompact E := hK.image SimpleSpectrum.continuous_eigenvalue
  have hEp : ∀ q ∈ E, ∀ a, 0 < q a := by
    rintro q ⟨s,hs,rfl⟩
    exact s.positive
  have hEo : ∀ q ∈ E, StrictAnti q := by
    rintro q ⟨s,hs,rfl⟩
    exact s.strictAnti
  filter_upwards [eventually_uniform_universalKeep_transitionFidelity_one_abs hd K hK m γ hγ hgain ε hε,
    eventually_universalKeep_support hd E hEc hEp hEo m γ hγ hgain] with n hf hs
  intro p hp i j hkeep U
  have hc := (hs p.eigenvalue ⟨p,hp,rfl⟩ i j hkeep).1
  rw [transitionFidelity_unitary _ _ _ _ _ _ (Unitary.star_mul_self_of_mem U.property) _ _ hc]
  exact hf p hp i j hkeep

/-- The retained-sector lower bound needed by the concrete universal
physical channel, uniformly over all spectra in a compact set. -/
theorem eventually_uniform_universalKeep_transitionFidelity {d : ℕ} (hd : 1 ≤ d)
    (K : Set (SimpleSpectrum (d+1))) (hK : IsCompact K)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ p ∈ K, ∀ (i : SchurCopy n (d+1)) (j : SchurCopy (m n) (d+1)),
      universalKeep n (m n) d p.eigenvalue i j →
      ∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
      orbitalValue γ p-η ≤ transitionFidelity n (m n) (d+1) p.eigenvalue p.positive U i j := by
  filter_upwards [eventually_uniform_universalKeep_transitionFidelity_abs hd K hK m γ hγ hgain η hη]
    with n hn p hp i j hkeep U
  have hh := (abs_lt.mp (hn p hp i j hkeep U)).1
  linarith

end Cloning.TensorCloning
