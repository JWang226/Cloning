import Cloning.TensorCloningRetainedTypical
import Cloning.PhysicalCloningConverseUnknown

/-! Arbitrary shrinking windows in the uniform Cartan-sector estimate.
Mixture cardinalities and probabilities are unrestricted. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical Topology
open Filter
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
open Cloning.YoungCompatibility
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Vanishing coordinate errors give uniform convergence of varying families. -/
theorem uniform_coordinates_of_shrinking {J : ℕ → Type*}
    (x : ∀ N, J N → Fin d → ℝ) (pN : ℕ → Fin d → ℝ) (p : Fin d → ℝ)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hp : ∀ a, Tendsto (fun N => pN N a) atTop (𝓝 (p a)))
    (hx : ∀ N j a, |x N j a-pN N a| ≤ δ N)
    (a : Fin d) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N in atTop, ∀ j : J N, |x N j a-p a|<ε := by
  filter_upwards [hδ.eventually (eventually_lt_nhds (show (0:ℝ)<ε/2 by positivity)),
    (Metric.tendsto_nhds.mp (hp a) (ε/2) (by positivity))] with N hN hpN j
  rw [Real.dist_eq] at hpN
  have h := abs_sub_le (x N j a) (pN N a) (p a)
  have hb := hx N j a
  linarith

/-- One threshold works for every spectrum, target, finite source family and
probability law in an arbitrary shrinking window. This is actual root fidelity
of the physical Cartan mixture, with no typical-window restriction. -/
theorem eventually_uniform_shrinkingWindow_mixture_fidelity
    (K : Set (SimpleSpectrum d)) (hK : IsCompact K)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ (n : ℕ) in atTop, ∀ p∈K, ∀ s : ℕ,
      ∀ (μ : Fin s → Fin d → ℕ) (ν : Fin d → ℕ)
        (hμ : ∀ j, Antitone (μ j)) (hν : Antitone ν),
      (∀ j a, |(μ j a : ℝ)/n-p.eigenvalue a|≤δ n) →
      (∀ a, |(ν a : ℝ)/(m n : ℝ)-p.eigenvalue a|≤δ n) →
      ∀ (q : Fin s → ℝ) (hq : ∀ j, 0≤q j), (∑ j,q j)=1 →
      |(partitionTransitionMixture μ ν hμ hν p.eigenvalue p.positive q hq).rootFidelity
        (partitionGibbsPositive ν hν p.eigenvalue p.positive)-orbitalValue γ p|<ε := by
  rw [eventually_atTop]
  by_contra h
  push_neg at h
  choose n hn p hpK s μ ν hμ hν hμclose hνclose q hq hs hb using h
  have hnlim : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  obtain ⟨p₀,hp₀,φ,hφ,hconv⟩ := (hK.image SimpleSpectrum.continuous_eigenvalue).tendsto_subseq
    (fun N => show (p N).eigenvalue ∈ SimpleSpectrum.eigenvalue '' K from ⟨p N,hpK N,rfl⟩)
  obtain ⟨p₁,hp₁,rfl⟩ := hp₀
  have hlim a : Tendsto (fun N => (p (φ N)).eigenvalue a) atTop (𝓝 (p₁.eigenvalue a)) :=
    (continuous_apply a).continuousAt.tendsto.comp hconv
  have hsample := hnlim.comp hφ.tendsto_atTop
  have hμlim := uniform_coordinates_of_shrinking
    (fun N (j : Fin (s (φ N))) a => (μ (φ N) j a : ℝ)/(n (φ N) : ℝ))
    (fun N => (p (φ N)).eigenvalue) p₁.eigenvalue
    (fun N => δ (n (φ N))) (hδ.comp hsample) hlim (fun N => hμclose (φ N))
  have hνscaled (a : Fin d) :
      Tendsto (fun N => (ν (φ N) a : ℝ)/(m (n (φ N)) : ℝ)) atTop (𝓝 (p₁.eigenvalue a)) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    have hh := uniform_coordinates_of_shrinking (J := fun _ => Unit)
      (fun N _ a => (ν (φ N) a : ℝ)/(m (n (φ N)) : ℝ))
      (fun N => (p (φ N)).eigenvalue) p₁.eigenvalue
      (fun N => δ (n (φ N))) (hδ.comp hsample) hlim
      (fun N _ => hνclose (φ N)) a η hη
    exact hh.mono (fun N hN => by simpa only [Real.dist_eq] using hN ())
  have hm := PhysicalCloningConverse.output_size_tendsto m γ (by linarith) hgain
  have hνlim (a : Fin d) :
      Tendsto (fun N => (ν (φ N) a : ℝ)/(n (φ N) : ℝ)) atTop (𝓝 (γ*p₁.eigenvalue a)) := by
    have hh := (hgain.comp hsample).mul (hνscaled a)
    apply hh.congr'
    filter_upwards [(hm.comp hsample).eventually (eventually_gt_atTop 0)] with N hN
    have hm0 : (m (n (φ N)) : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    dsimp only [Function.comp_apply]
    field_simp
  have hf := partitionTransitionMixture_rootFidelity_tendsto
    (fun N => n (φ N)) hsample (fun N => μ (φ N)) (fun N => ν (φ N))
    (fun N => hμ (φ N)) (fun N => hν (φ N))
    (fun N => (p (φ N)).eigenvalue) (fun N => (p (φ N)).positive) p₁ hlim γ hγ hμlim hνlim
    (fun N => q (φ N)) (fun N => hq (φ N)) (fun N => hs (φ N))
  have hpconv : Tendsto (fun N => p (φ N)) atTop (𝓝 p₁) :=
    SimpleSpectrum.isEmbedding_eigenvalue.tendsto_nhds_iff.mpr hconv
  have ho := (continuous_orbitalValue (by linarith : 0<γ)).continuousAt.tendsto.comp hpconv
  have he := hf.sub ho
  rw [sub_self] at he
  obtain ⟨N,hN⟩ := (Metric.tendsto_nhds.mp he ε hε).exists
  rw [Real.dist_eq,sub_zero] at hN
  exact (not_lt_of_ge (hb (φ N))) hN

/-- Signed lattice compatibility follows from scaled row limits; output
nonnegativity and dominance are not assumptions. -/
theorem eventually_intCompatible_of_scaled_limits
    (n m : ℕ → ℕ) (hn : Tendsto n atTop atTop) (μ ν : ℕ → Fin d → ℤ)
    (hμmass : ∀ N, ∑ a,μ N a=(n N : ℤ)) (hνmass : ∀ N, ∑ a,ν N a=(m N : ℤ))
    (p : Fin d → ℝ) (hp : ∀ a,0<p a) (hord : StrictAnti p)
    (γ : ℝ) (hγ : 1<γ)
    (hμ : ∀ a,Tendsto (fun N => (μ N a : ℝ)/(n N : ℝ)) atTop (𝓝 (p a)))
    (hν : ∀ a,Tendsto (fun N => (ν N a : ℝ)/(n N : ℝ)) atTop (𝓝 (γ*p a))) :
    ∀ᶠ N in atTop,Compatible (n N : ℤ) (m N : ℤ) (μ N) (ν N) := by
  have hd (a : Fin d) : Tendsto
      (fun N => (ν N a : ℝ)/(n N : ℝ)-(μ N a : ℝ)/(n N : ℝ)) atTop (𝓝 ((γ-1)*p a)) := by
    have he : γ*p a-p a=(γ-1)*p a := by ring
    simpa only [he] using (hν a).sub (hμ a)
  have hpos : ∀ᶠ N in atTop,∀ a,
      0<(ν N a : ℝ)/(n N : ℝ)-(μ N a : ℝ)/(n N : ℝ) :=
    eventually_all.mpr (fun a => (hd a).eventually (eventually_gt_nhds (mul_pos (sub_pos.mpr hγ) (hp a))))
  have hgap : ∀ᶠ N in atTop,∀ r : PositiveRoot d,
      0<((ν N r.val.1 : ℝ)/(n N : ℝ)-(μ N r.val.1 : ℝ)/(n N : ℝ))-
        ((ν N r.val.2 : ℝ)/(n N : ℝ)-(μ N r.val.2 : ℝ)/(n N : ℝ)) := by
    apply eventually_all.mpr
    intro r
    apply ((hd r.val.1).sub (hd r.val.2)).eventually
    apply eventually_gt_nhds
    nlinarith [hord r.property]
  filter_upwards [hpos,hgap,hn.eventually (eventually_gt_atTop 0)] with N hN hg hN0
  have hnreal : (0:ℝ)<n N := by exact_mod_cast hN0
  refine ⟨?_,?_,?_⟩
  · intro a
    have hh := hN a
    rw [← sub_div,div_pos_iff_of_pos_right hnreal] at hh
    exact_mod_cast hh.le
  · intro a b hab
    rcases hab.eq_or_lt with rfl | hab
    · exact le_rfl
    have hh := hg ⟨(a,b),hab⟩
    simp only at hh
    rw [← sub_div,← sub_div,← sub_div,div_pos_iff_of_pos_right hnreal] at hh
    have hreal : (ν N b : ℝ)-(μ N b : ℝ)≤(ν N a : ℝ)-(μ N a : ℝ) := by linarith
    exact_mod_cast hreal
  · rw [Finset.sum_sub_distrib,hμmass,hνmass]

/-- Arbitrary shrinking windows make the signed output lattice label and its
source difference Young labels, uniformly over both labels and the spectrum. -/
theorem eventually_uniform_shrinkingWindow_compatible
    (K : Set (SimpleSpectrum d)) (hK : IsCompact K)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ᶠ (n : ℕ) in atTop,∀ p∈K,∀ μ ν : Fin d → ℤ,
      IsYoung (n : ℤ) μ → (∑ a,ν a)=(m n : ℤ) →
      (∀ a,|(μ a : ℝ)/n-p.eigenvalue a|≤δ n) →
      (∀ a,|(ν a : ℝ)/(m n : ℝ)-p.eigenvalue a|≤δ n) →
      Compatible (n : ℤ) (m n : ℤ) μ ν ∧ IsYoung (m n : ℤ) ν := by
  rw [eventually_atTop]
  by_contra h
  push_neg at h
  choose n hn p hpK μ ν hμ hνmass hμclose hνclose hb using h
  have hnlim : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  obtain ⟨p₀,hp₀,φ,hφ,hconv⟩ := (hK.image SimpleSpectrum.continuous_eigenvalue).tendsto_subseq
    (fun N => show (p N).eigenvalue ∈ SimpleSpectrum.eigenvalue '' K from ⟨p N,hpK N,rfl⟩)
  obtain ⟨p₁,hp₁,rfl⟩ := hp₀
  have hlim a : Tendsto (fun N => (p (φ N)).eigenvalue a) atTop (𝓝 (p₁.eigenvalue a)) :=
    (continuous_apply a).continuousAt.tendsto.comp hconv
  have hsample := hnlim.comp hφ.tendsto_atTop
  have hsource (a : Fin d) : Tendsto
      (fun N => (μ (φ N) a : ℝ)/(n (φ N) : ℝ)) atTop (𝓝 (p₁.eigenvalue a)) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    have hh := uniform_coordinates_of_shrinking (J:=fun _ => Unit)
      (fun N _ a => (μ (φ N) a : ℝ)/(n (φ N) : ℝ))
      (fun N => (p (φ N)).eigenvalue) p₁.eigenvalue
      (fun N => δ (n (φ N))) (hδ.comp hsample) hlim (fun N _ => hμclose (φ N)) a η hη
    exact hh.mono (fun N hN => by simpa only [Real.dist_eq] using hN ())
  have htarget (a : Fin d) : Tendsto
      (fun N => (ν (φ N) a : ℝ)/(m (n (φ N)) : ℝ)) atTop (𝓝 (p₁.eigenvalue a)) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    have hh := uniform_coordinates_of_shrinking (J:=fun _ => Unit)
      (fun N _ a => (ν (φ N) a : ℝ)/(m (n (φ N)) : ℝ))
      (fun N => (p (φ N)).eigenvalue) p₁.eigenvalue
      (fun N => δ (n (φ N))) (hδ.comp hsample) hlim (fun N _ => hνclose (φ N)) a η hη
    exact hh.mono (fun N hN => by simpa only [Real.dist_eq] using hN ())
  have hm := PhysicalCloningConverse.output_size_tendsto m γ (by linarith) hgain
  have htarget' (a : Fin d) : Tendsto
      (fun N => (ν (φ N) a : ℝ)/(n (φ N) : ℝ)) atTop (𝓝 (γ*p₁.eigenvalue a)) := by
    have hh := (hgain.comp hsample).mul (htarget a)
    apply hh.congr'
    filter_upwards [(hm.comp hsample).eventually (eventually_gt_atTop 0)] with N hN
    have hm0 : (m (n (φ N)) : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    dsimp only [Function.comp_apply]
    field_simp
  have hc := eventually_intCompatible_of_scaled_limits
    (fun N => n (φ N)) (fun N => m (n (φ N))) hsample
    (fun N => μ (φ N)) (fun N => ν (φ N))
    (fun N => (hμ (φ N)).2.2) (fun N => hνmass (φ N))
    p₁.eigenvalue p₁.positive p₁.strictAnti γ hγ hsource htarget'
  obtain ⟨N,hN⟩ := hc.exists
  have hy := compatible_isYoung (hμ (φ N)) hN
  exact hb (φ N) hN hy

/-- The single-sector assertion is included with the same arbitrary window. -/
theorem eventually_uniform_shrinkingWindow_sector_fidelity
    (K : Set (SimpleSpectrum d)) (hK : IsCompact K)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ (n : ℕ) in atTop,∀ p∈K,
      ∀ (μ ν : Fin d → ℕ) (hμ : Antitone μ) (hν : Antitone ν),
      (∀ a,|(μ a : ℝ)/n-p.eigenvalue a|≤δ n) →
      (∀ a,|(ν a : ℝ)/(m n : ℝ)-p.eigenvalue a|≤δ n) →
      |(partitionTransitionOutput μ ν hμ hν p.eigenvalue p.positive).rootFidelity
        (partitionGibbsPositive ν hν p.eigenvalue p.positive)-orbitalValue γ p|<ε := by
  filter_upwards [eventually_uniform_shrinkingWindow_mixture_fidelity K hK m γ hγ hgain δ hδ ε hε]
    with n hn p hp μ ν hμ hν hμclose hνclose
  have hh := hn p hp 1 (fun _ => μ) ν (fun _ => hμ) hν
    (fun _ => hμclose) hνclose (fun _ => 1) (fun _ => by norm_num) (by simp)
  have he : partitionTransitionMixture (fun _ : Fin 1 => μ) ν (fun _ => hμ) hν
      p.eigenvalue p.positive (fun _ => 1) (fun _ => by norm_num) =
      partitionTransitionOutput μ ν hμ hν p.eigenvalue p.positive := by
    apply Subtype.ext
    simp only [partitionTransitionMixture,PositiveTraceClass.finiteMixture_val,Fin.sum_univ_one,
      Complex.ofReal_one,one_smul]
  simpa only [he] using hh

end Cloning.TensorCloning
