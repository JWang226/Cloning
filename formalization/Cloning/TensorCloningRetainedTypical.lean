import Cloning.TensorCloningRetainedMixture
import Cloning.PhysicalCloningConverseSpectrum

/-! Physical typical windows imply the uniform row frequencies needed for
arbitrary normalized common-target conditional mixtures. -/
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

theorem uniform_typical_scaled {J : ℕ → Type*}
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (μ : ∀ N, J N → Fin d → ℕ)
    (pN : ℕ → Fin d → ℝ) (p : Fin d → ℝ)
    (hlim : ∀ a, Tendsto (fun N => pN N a) atTop (𝓝 (p a)))
    (htyp : ∀ᶠ N in atTop, ∀ j : J N, TypicalLabel (n N) (pN N) (μ N j))
    (a : Fin d) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ j : J N, |(μ N j a : ℝ)/(n N : ℝ)-p a| < ε := by
  have hh := eventually_uniform_of_subsequences (fun N (_ : J N) => True)
    (fun N j => |(μ N j a : ℝ)/(n N : ℝ)-p a| < ε) (by
      intro φ hφ j _
      have ht : ∀ᶠ k in atTop, TypicalLabel (n (φ k)) (pN (φ k)) (μ (φ k) (j k)) :=
        (hφ.eventually htyp).mono (fun k hk => hk (j k))
      have hf := typicalLabel_ratio_tendsto (fun k => n (φ k)) (hn.comp hφ)
        (fun k => μ (φ k) (j k)) (fun k => pN (φ k)) p (fun b => (hlim b).comp hφ) ht a
      simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp hf ε hε)
  exact hh.mono (fun N hN j => hN j trivial)

theorem target_typical_scaled (n m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (ν : ℕ → Fin d → ℕ) (pN : ℕ → Fin d → ℝ) (p : Fin d → ℝ)
    (hlim : ∀ a, Tendsto (fun N => pN N a) atTop (𝓝 (p a)))
    (γ : ℝ) (hgain : Tendsto (fun N => (m N : ℝ)/(n N : ℝ)) atTop (𝓝 γ))
    (htyp : ∀ᶠ N in atTop, TypicalLabel (m N) (pN N) (ν N)) (a : Fin d) :
    Tendsto (fun N => (ν N a : ℝ)/(n N : ℝ)) atTop (𝓝 (γ*p a)) := by
  have hf := hgain.mul (typicalLabel_ratio_tendsto m hm ν pN p hlim htyp a)
  apply hf.congr'
  filter_upwards [hm.eventually (eventually_gt_atTop 0)] with N hN
  have hm0 : (m N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem partitionTransitionMixture_rootFidelity_tendsto_of_typical
    {J : ℕ → Type*} [∀ N, Fintype (J N)]
    (n m : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (μ : ∀ N, J N → Fin d → ℕ) (ν : ℕ → Fin d → ℕ)
    (hμ : ∀ N a, Antitone (μ N a)) (hν : ∀ N, Antitone (ν N))
    (pN : ℕ → Fin d → ℝ) (hpN : ∀ N a, 0 < pN N a)
    (p : SimpleSpectrum d) (hlim : ∀ a, Tendsto (fun N => pN N a) atTop (𝓝 (p.eigenvalue a)))
    (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun N => (m N : ℝ)/(n N : ℝ)) atTop (𝓝 γ))
    (hμtyp : ∀ᶠ N in atTop, ∀ a : J N, TypicalLabel (n N) (pN N) (μ N a))
    (hνtyp : ∀ᶠ N in atTop, TypicalLabel (m N) (pN N) (ν N))
    (q : ∀ N, J N → ℝ) (hq : ∀ N a, 0 ≤ q N a) (hs : ∀ N, ∑ a,q N a=1) :
    Tendsto (fun N => (partitionTransitionMixture (μ N) (ν N) (hμ N) (hν N)
      (pN N) (hpN N) (q N) (hq N)).rootFidelity
        (partitionGibbsPositive (ν N) (hν N) (pN N) (hpN N))) atTop (𝓝 (orbitalValue γ p)) :=
  partitionTransitionMixture_rootFidelity_tendsto n hn μ ν hμ hν pN hpN p hlim γ hγ
    (uniform_typical_scaled n hn μ pN p.eigenvalue hlim hμtyp)
    (target_typical_scaled n m hm ν pN p.eigenvalue hlim γ hgain hνtyp) q hq hs

def retainedCopyMixture (n m d : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (j : SchurCopy m d) (keep : SchurCopy n d → Prop)
    (q : {i : SchurCopy n d // keep i} → ℝ) (hq : ∀ i, 0 ≤ q i) :
    PositiveTraceClass ((recursivePhysicalDecomposition m d).get j).CanonicalSector :=
  partitionTransitionMixture
    (fun i : {i : SchurCopy n d // keep i} => ((recursivePhysicalDecomposition n d).get i.val).weight)
    ((recursivePhysicalDecomposition m d).get j).weight
    (fun i => ((recursivePhysicalDecomposition n d).get i.val).weight_antitone)
    ((recursivePhysicalDecomposition m d).get j).weight_antitone p hp q hq

def retainedCopyFidelity (n m d : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (j : SchurCopy m d) (keep : SchurCopy n d → Prop)
    (q : {i : SchurCopy n d // keep i} → ℝ) (hq : ∀ i, 0 ≤ q i) : ℝ :=
  (retainedCopyMixture n m d p hp j keep q hq).rootFidelity
    (partitionGibbsPositive ((recursivePhysicalDecomposition m d).get j).weight
      ((recursivePhysicalDecomposition m d).get j).weight_antitone p hp)

/-- Exact conditional-mixture fidelity is compact-uniform for every
probability mixture over all physically typical source copies. -/
theorem eventually_uniform_known_retainedCopyFidelity
    (K : Set (SimpleSpectrum d)) (hK : IsCompact K)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ p ∈ K, ∀ j : SchurCopy (m n) d,
      copyTypical (m n) d p.eigenvalue j →
      ∀ (q : {i : SchurCopy n d // copyTypical n d p.eigenvalue i} → ℝ)
        (hq : ∀ i, 0 ≤ q i), (∑ i,q i)=1 →
      |retainedCopyFidelity n (m n) d p.eigenvalue p.positive j
        (copyTypical n d p.eigenvalue) q hq - orbitalValue γ p| < ε := by
  rw [eventually_atTop]
  by_contra h
  push_neg at h
  choose n hn p hpK j hj q hq hs hb using h
  have hnlim : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  obtain ⟨p₀,hp₀,φ,hφ,hconv⟩ := (hK.image SimpleSpectrum.continuous_eigenvalue).tendsto_subseq
    (fun N => show (p N).eigenvalue ∈ SimpleSpectrum.eigenvalue '' K from ⟨p N,hpK N,rfl⟩)
  obtain ⟨p₁,hp₁,rfl⟩ := hp₀
  have hlim a : Tendsto (fun N => (p (φ N)).eigenvalue a) atTop (𝓝 (p₁.eigenvalue a)) :=
    (continuous_apply a).continuousAt.tendsto.comp hconv
  let J N := {i : SchurCopy (n (φ N)) d // copyTypical (n (φ N)) d (p (φ N)).eigenvalue i}
  let μ N (i : J N) := ((recursivePhysicalDecomposition (n (φ N)) d).get i.val).weight
  let ν N := ((recursivePhysicalDecomposition (m (n (φ N))) d).get (j (φ N))).weight
  have hμ N (i : J N) : Antitone (μ N i) :=
    ((recursivePhysicalDecomposition (n (φ N)) d).get i.val).weight_antitone
  have hν N : Antitone (ν N) := ((recursivePhysicalDecomposition (m (n (φ N))) d).get (j (φ N))).weight_antitone
  have hf := partitionTransitionMixture_rootFidelity_tendsto_of_typical
    (fun N => n (φ N)) (fun N => m (n (φ N))) (hnlim.comp hφ.tendsto_atTop)
    (hm.comp (hnlim.comp hφ.tendsto_atTop)) μ ν hμ hν
    (fun N => (p (φ N)).eigenvalue) (fun N => (p (φ N)).positive) p₁ hlim γ hγ
    (hgain.comp (hnlim.comp hφ.tendsto_atTop))
    (Eventually.of_forall (fun N (i : J N) => i.property))
    (Eventually.of_forall (fun N => hj (φ N)))
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
