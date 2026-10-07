import Cloning.YoungPhysicalRoundingLimit

/-! Compact-uniform L1 convergence of the raw rounded physical Young law,
with the Gaussian covariance evaluated at the current spectrum. -/
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory Filter
namespace Cloning.YoungHyperplane
open Cloning.YoungRounding Cloning.YoungGeneral Cloning.YoungCompatibility
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Gaussian continuity survives the coordinate Jacobian and fixed dilation. -/
theorem dilated_headGaussian_l1_tendsto (d : ℕ)
    (p : ℕ → Fin (d+1) → ℝ) (p₀ : Fin (d+1) → ℝ)
    (hp : ∀ k,∑ i,p k i=1) (hs₀ : ∑ i,p₀ i=1)
    (hp0 : ∀ k i,0<p k i) (hp₀ : ∀ i,0<p₀ i)
    (hlim : ∀ i,Tendsto (fun k => p k i) atTop (𝓝 (p₀ i)))
    (γ : ℝ) (hγ : 0<γ) :
    Tendsto (fun k => ∫ x,|affineDensity (Real.sqrt γ) 0 (headGaussian d (p k) (hp k)) x-
      affineDensity (Real.sqrt γ) 0 (headGaussian d p₀ hs₀) x|) atTop (𝓝 0) := by
  simpa only [affineDensity_l1_isometry (Real.sqrt γ) (Real.sqrt_pos.mpr hγ),
    headGaussian,coordinateDensity_l1_isometry] using
    covarianceGaussian_l1_tendsto d p p₀ hp hs₀ hp0 hp₀ hlim

/-- The sequential raw rounded-density limit with a moving covariance. -/
theorem rounded_tensorYoungDensity_l1_moving_gaussian (d : ℕ) (n m : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (hn0 : ∀ k,0<n k) (hm0 : ∀ k,0<m k)
    (γ : ℝ) (hγ : 0<γ) (hratio : Tendsto (fun k => (m k : ℝ)/n k) atTop (𝓝 γ))
    (p : ℕ → Fin (d+1) → ℝ) (hp : ∀ k,∑ i,p k i=1)
    (hp0 : ∀ k i,0<p k i) (p₀ : Fin (d+1) → ℝ) (hs₀ : ∑ i,p₀ i=1)
    (hp₀ : ∀ i,0<p₀ i) (hord : StrictAnti p₀)
    (hlim : ∀ i,Tendsto (fun k => p k i) atTop (𝓝 (p₀ i))) :
    Tendsto (fun k => ∫ x,|roundedDensity (Real.sqrt (m k : ℝ))⁻¹ (headAnchor d (m k) (p k))
      ((m k : ℝ)/n k) (tensorYoungHeadPMF d (n k) (p k) (fun i => (hp0 k i).le) (hp k)) x-
      affineDensity (Real.sqrt γ) 0 (headGaussian d (p k) (hp k)) x|) atTop (𝓝 0) := by
  have hf := rounded_tensorYoungDensity_l1_tendsto d n m hn hm hn0 hm0 γ hγ hratio
    p hp hp0 p₀ hs₀ hp₀ hord hlim
  have hg := dilated_headGaussian_l1_tendsto d p p₀ hp hs₀ hp0 hp₀ hlim γ hγ
  have ht := hf.add hg
  simp only [zero_add] at ht
  apply squeeze_zero (fun k => integral_nonneg (fun _ => abs_nonneg _)) ?_ ht
  intro k
  let F := roundedDensity (Real.sqrt (m k : ℝ))⁻¹ (headAnchor d (m k) (p k))
    ((m k : ℝ)/n k) (tensorYoungHeadPMF d (n k) (p k) (fun i => (hp0 k i).le) (hp k))
  let G := affineDensity (Real.sqrt γ) 0 (headGaussian d (p k) (hp k))
  let Z := affineDensity (Real.sqrt γ) 0 (headGaussian d p₀ hs₀)
  have hfi : Integrable F := integrable_affineDensity _ (by positivity [hm0 k]) _
    (integrable_interpolate (hasSum_probability _).summable)
  have hgi : Integrable G := integrable_affineDensity _ (by positivity) _
    (integrable_headGaussian d (p k) (hp k) (hp0 k))
  have hzi : Integrable Z := integrable_affineDensity _ (by positivity) _
    (integrable_headGaussian d p₀ hs₀ hp₀)
  change (∫ x,|F x-G x|)≤(∫ x,|F x-Z x|)+(∫ x,|G x-Z x|)
  erw [← integral_add (hfi.sub hzi).abs (hgi.sub hzi).abs]
  apply integral_mono (hfi.sub hgi).abs ((hfi.sub hzi).abs.add (hgi.sub hzi).abs)
  intro x
  simpa only [abs_sub_comm (Z x)] using abs_sub_le (F x) (Z x) (G x)

/-- The first conclusion of `lem:randomized-dilation`: one sample threshold
works for every spectrum in the compact simple chamber. The law is the raw
physical rounding before fallback, and the comparison covariance is γΣ_p. -/
theorem uniform_rounded_tensorYoungDensity_l1 (d : ℕ)
    (K : Set (Fin (d+1) → ℝ)) (hK : IsCompact K)
    (hp : ∀ p∈K,∑ i,p i=1) (hp0 : ∀ p∈K,∀ i,0<p i)
    (hord : ∀ p∈K,StrictAnti p)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (γ : ℝ) (hγ : 0<γ) (hratio : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ))
    (ε : ℝ) (hε : 0<ε) :
    ∃ N₀ : ℕ,∀ N≥N₀,∀ (p : Fin (d+1) → ℝ) (hpK : p∈K),
      (∫ x,|roundedDensity (Real.sqrt (m N : ℝ))⁻¹ (headAnchor d (m N) p)
        ((m N : ℝ)/N) (tensorYoungHeadPMF d N p (fun i => (hp0 p hpK i).le) (hp p hpK)) x-
        affineDensity (Real.sqrt γ) 0 (headGaussian d p (hp p hpK)) x|)<ε := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hm.eventually (eventually_ge_atTop 1))
  by_contra h
  push_neg at h
  have hbad k := h (max k (max M 1))
  choose n hn p hpK hb using hbad
  obtain ⟨p₀,hp₀K,φ,hφ,hconv⟩ := hK.tendsto_subseq hpK
  have hnlim : Tendsto n atTop atTop :=
    tendsto_atTop_mono (fun k => (le_max_left k _).trans (hn k)) tendsto_id
  have hn0 k : 0<n (φ k) := by have h := hn (φ k); omega
  have hm0 k : 0<m (n (φ k)) := by
    have hh : M≤n (φ k) := by have h := hn (φ k); omega
    exact Nat.lt_of_lt_of_le (by omega) (hM _ hh)
  have hlim i : Tendsto (fun k => p (φ k) i) atTop (𝓝 (p₀ i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hconv
  have ht := rounded_tensorYoungDensity_l1_moving_gaussian d (fun k => n (φ k))
    (fun k => m (n (φ k))) (hnlim.comp hφ.tendsto_atTop)
    (hm.comp (hnlim.comp hφ.tendsto_atTop)) hn0 hm0 γ hγ
    (hratio.comp (hnlim.comp hφ.tendsto_atTop)) (fun k => p (φ k))
    (fun k => hp _ (hpK (φ k))) (fun k => hp0 _ (hpK (φ k)))
    p₀ (hp p₀ hp₀K) (hp0 p₀ hp₀K) (hord p₀ hp₀K) hlim
  obtain ⟨k,hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge (hb (φ k))) hk

end Cloning.YoungHyperplane
