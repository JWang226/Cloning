import Cloning.TensorCloningRetainedTypical
import Cloning.TensorCloningUniversalFrequencies

/-! Exact compact-uniform conditional fidelity for every normalized retained
mixture of the literal universal physical transition kernel. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical Topology
open Filter
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- A normalized retained mixture automatically has a supported source
component. Its genuine randomized rounding support forces the common output
frequency, so no separate target-window assumption is needed. -/
theorem eventually_uniform_universal_retainedCopyFidelity {d : ℕ} (hd : 1 ≤ d)
    (K : Set (SimpleSpectrum (d+1))) (hK : IsCompact K)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ p ∈ K, ∀ j : SchurCopy (m n) (d+1),
      ∀ (q : {i : SchurCopy n (d+1) // universalKeep n (m n) d p.eigenvalue i j} → ℝ)
        (hq : ∀ i, 0 ≤ q i), (∑ i,q i)=1 →
      |retainedCopyFidelity n (m n) (d+1) p.eigenvalue p.positive j
        (fun i => universalKeep n (m n) d p.eigenvalue i j) q hq - orbitalValue γ p| < ε := by
  rw [eventually_atTop]
  by_contra h
  push_neg at h
  choose n hn p hpK j q hq hs hb using h
  have hnlim : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  let E := SimpleSpectrum.eigenvalue '' K
  have hEc : IsCompact E := hK.image SimpleSpectrum.continuous_eigenvalue
  have hEp : ∀ s ∈ E, ∀ a, 0 < s a := by
    rintro s ⟨p,hp,rfl⟩
    exact p.positive
  have hEo : ∀ s ∈ E, StrictAnti s := by
    rintro s ⟨p,hp,rfl⟩
    exact p.strictAnti
  obtain ⟨p₀,hp₀,φ,hφ,hconv⟩ := hEc.tendsto_subseq
    (fun N => show (p N).eigenvalue ∈ E from ⟨p N,hpK N,rfl⟩)
  obtain ⟨p₁,hp₁,rfl⟩ := hp₀
  have hlim a : Tendsto (fun N => (p (φ N)).eigenvalue a) atTop (𝓝 (p₁.eigenvalue a)) :=
    (continuous_apply a).continuousAt.tendsto.comp hconv
  let J N := {i : SchurCopy (n (φ N)) (d+1) //
    universalKeep (n (φ N)) (m (n (φ N))) d (p (φ N)).eigenvalue i (j (φ N))}
  have hJ N : Nonempty (J N) := by
    by_contra hne
    haveI : IsEmpty (J N) := not_nonempty_iff.mp hne
    have hh : (∑ a : J N,q (φ N) a)=1 := hs (φ N)
    simpa using hh
  let a₀ N : J N := Classical.choice (hJ N)
  let μ N (i : J N) := ((recursivePhysicalDecomposition (n (φ N)) (d+1)).get i.val).weight
  let ν N := ((recursivePhysicalDecomposition (m (n (φ N))) (d+1)).get (j (φ N))).weight
  have hμ N (i : J N) : Antitone (μ N i) :=
    ((recursivePhysicalDecomposition (n (φ N)) (d+1)).get i.val).weight_antitone
  have hν N : Antitone (ν N) := ((recursivePhysicalDecomposition (m (n (φ N))) (d+1)).get (j (φ N))).weight_antitone
  have hμlim := uniform_typical_scaled (fun N => n (φ N)) (hnlim.comp hφ.tendsto_atTop) μ
    (fun N => (p (φ N)).eigenvalue) p₁.eigenvalue hlim
    (Eventually.of_forall (fun N (i : J N) => i.property.1))
  obtain ⟨_,hνlim⟩ := universalKeep_scaled_limits hd E hEc hEp hEo m γ hγ hgain
    (fun N => n (φ N)) (hnlim.comp hφ.tendsto_atTop)
    (fun N => (p (φ N)).eigenvalue) (fun N => ⟨p (φ N),hpK (φ N),rfl⟩)
    p₁.eigenvalue hlim (fun N => (a₀ N).val) (fun N => j (φ N)) (fun N => (a₀ N).property)
  have hf := partitionTransitionMixture_rootFidelity_tendsto
    (fun N => n (φ N)) (hnlim.comp hφ.tendsto_atTop) μ ν hμ hν
    (fun N => (p (φ N)).eigenvalue) (fun N => (p (φ N)).positive) p₁ hlim γ hγ hμlim hνlim
    (fun N => q (φ N)) (fun N => hq (φ N)) (fun N => hs (φ N))
  have hpconv : Tendsto (fun N => p (φ N)) atTop (𝓝 p₁) :=
    SimpleSpectrum.isEmbedding_eigenvalue.tendsto_nhds_iff.mpr hconv
  have ho := (continuous_orbitalValue (by linarith : 0 < γ)).continuousAt.tendsto.comp hpconv
  have he := hf.sub ho
  rw [sub_self] at he
  obtain ⟨N,hN⟩ := (Metric.tendsto_nhds.mp he ε hε).exists
  rw [Real.dist_eq,sub_zero] at hN
  exact (not_lt_of_ge (hb (φ N))) hN

end Cloning.TensorCloning
