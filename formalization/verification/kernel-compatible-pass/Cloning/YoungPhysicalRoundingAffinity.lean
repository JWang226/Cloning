import Cloning.YoungPhysicalRoundingGaussian
import Cloning.YoungPhysicalRoundingLabels

/-! Exact asymptotic label affinity for the actual physical randomized Young output. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter MeasureTheory
namespace Cloning.YoungHyperplane
open Cloning.TensorLie Cloning.YoungGeneral Cloning.YoungCompatibility Cloning.YoungRounding
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Physical lattice affinity is exactly the continuous affinity of the actual output cells. -/
theorem tensorYoungRawOutput_affinity_eq_integral (d n m : ℕ) (hm : 0 < m) (γ : ℝ)
    (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    CountableScheffe.affinity (probability (tensorYoungRawOutput d n m γ p hp hs))
      (probability (tensorYoungIntegerPMF d m p hp hs)) =
    ∫ x, Real.sqrt (roundedDensity (Real.sqrt (m : ℝ))⁻¹ (headAnchor d m p) γ
      (tensorYoungHeadPMF d n p hp hs) x)*Real.sqrt (headDensity d m p hp hs x) := by
  rw [tensorYoungRawOutput_affinity, roundedDensity, headDensity,
    affineDensity_affinity d _ (by positivity)]
  exact (YoungRounding.interpolate_affinity
    (probability_nonneg (transport γ (tensorYoungHeadPMF d n p hp hs)))
    (probability_nonneg (tensorYoungHeadPMF d m p hp hs))
    (hasSum_probability (transport γ (tensorYoungHeadPMF d n p hp hs))).summable
    (hasSum_probability (tensorYoungHeadPMF d m p hp hs)).summable).symm

/-- For moving spectra and arbitrary divergent sizes the literal raw kernel attains the
classical Gaussian fidelity factor. -/
theorem tensorYoungRawOutput_affinity_tendsto (d : ℕ) (n m : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (hn0 : ∀ k, 0 < n k) (hm0 : ∀ k, 0 < m k)
    (γ : ℝ) (hγ : 0 < γ) (hratio : Tendsto (fun k ↦ (m k : ℝ)/n k) atTop (𝓝 γ))
    (p : ℕ → Fin (d + 1) → ℝ) (hp : ∀ k, ∑ i, p k i = 1)
    (hp0 : ∀ k i, 0 < p k i) (p₀ : Fin (d + 1) → ℝ) (hs₀ : ∑ i, p₀ i = 1)
    (hp₀ : ∀ i, 0 < p₀ i) (hord : StrictAnti p₀)
    (hlim : ∀ i, Tendsto (fun k ↦ p k i) atTop (𝓝 (p₀ i))) :
    Tendsto (fun k ↦ CountableScheffe.affinity
      (probability (tensorYoungRawOutput d (n k) (m k) ((m k : ℝ)/n k) (p k)
        (fun i ↦ (hp0 k i).le) (hp k)))
      (probability (tensorYoungIntegerPMF d (m k) (p k) (fun i ↦ (hp0 k i).le) (hp k))))
      atTop (𝓝 (Cloning.classicalValue γ (d+1))) := by
  have hfr := rounded_tensorYoungDensity_l1_tendsto d n m hn hm hn0 hm0 γ hγ hratio
    p hp hp0 p₀ hs₀ hp₀ hord hlim
  have hgr := headDensity_l1_tendsto d m hm hm0 p hp hp0 p₀ hs₀ hp₀ hord hlim
  let F := fun k ↦ roundedDensity (Real.sqrt (m k : ℝ))⁻¹ (headAnchor d (m k) (p k))
    ((m k : ℝ)/n k) (tensorYoungHeadPMF d (n k) (p k) (fun i ↦ (hp0 k i).le) (hp k))
  let G := fun k ↦ headDensity d (m k) (p k) (fun i ↦ (hp0 k i).le) (hp k)
  let F₀ := affineDensity (Real.sqrt γ) 0 (headGaussian d p₀ hs₀)
  let G₀ := headGaussian d p₀ hs₀
  have hFi k : Integrable (F k) :=
    integrable_affineDensity _ (by positivity [hm0 k]) _
      (integrable_interpolate (hasSum_probability _).summable)
  have hGi k : Integrable (G k) := integrable_headDensity d _ (hm0 k) _ _ _
  have hF₀i : Integrable F₀ := integrable_affineDensity _ (by positivity) _
    (integrable_headGaussian d p₀ hs₀ hp₀)
  have hG₀i : Integrable G₀ := integrable_headGaussian d p₀ hs₀ hp₀
  have hF0 k x : 0 ≤ F k x := by
    dsimp [F, roundedDensity, affineDensity, YoungRounding.interpolate]
    positivity
  have hF₀0 x : 0 ≤ F₀ x :=
    mul_nonneg (by positivity) (headGaussian_nonneg d p₀ hs₀ _)
  have hFmass : (∫ x, F₀ x) = 1 := by
    rw [integral_affineDensity _ (by positivity), integral_headGaussian d p₀ hs₀ hp₀]
  have h := density_affinity_tendsto volume F G F₀ G₀ hFi hGi hF₀i hG₀i hF0
    (fun k ↦ headDensity_nonneg d _ _ _ _) hF₀0 (headGaussian_nonneg d p₀ hs₀)
    hFmass (fun k ↦ integral_headDensity d _ (hm0 k) _ _ _) hfr hgr
  have hc : (∫ x, Real.sqrt (F₀ x)*Real.sqrt (G₀ x)) = Cloning.classicalValue γ (d+1) := by
    simpa only [F₀, G₀, mul_comm] using headGaussian_dilation_affinity d p₀ hs₀ hp₀ γ hγ
  rw [hc] at h
  simpa only [tensorYoungRawOutput_affinity_eq_integral d _ _ (hm0 _), F, G] using h

/-- Uniformity over every compact subset of the positive ordered simplex. -/
theorem uniform_tensorYoungRawOutput_affinity (d : ℕ)
    (K : Set (Fin (d+1) → ℝ)) (hK : IsCompact K)
    (hp : ∀ p ∈ K, ∑ i, p i = 1) (hp0 : ∀ p ∈ K, ∀ i, 0 < p i)
    (hord : ∀ p ∈ K, StrictAnti p)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (γ : ℝ) (hγ : 0 < γ) (hratio : Tendsto (fun n ↦ (m n : ℝ)/n) atTop (𝓝 γ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (p : Fin (d+1) → ℝ) (hpK : p ∈ K),
      |CountableScheffe.affinity
        (probability (tensorYoungRawOutput d N (m N) ((m N : ℝ)/N) p
          (fun i ↦ (hp0 p hpK i).le) (hp p hpK)))
        (probability (tensorYoungIntegerPMF d (m N) p
          (fun i ↦ (hp0 p hpK i).le) (hp p hpK))) - Cloning.classicalValue γ (d+1)| < ε := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hm.eventually (eventually_ge_atTop 1))
  by_contra h
  push_neg at h
  have hbad k := h (max k (max M 1))
  choose n hn p hpK hb using hbad
  obtain ⟨p₀, hp₀K, φ, hφ, hconv⟩ := hK.tendsto_subseq hpK
  have hnlim : Tendsto n atTop atTop :=
    tendsto_atTop_mono (fun k ↦ (le_max_left k _).trans (hn k)) tendsto_id
  have hn0 k : 0 < n (φ k) := by have h := hn (φ k); omega
  have hm0 k : 0 < m (n (φ k)) := by
    have hh : M ≤ n (φ k) := by have h := hn (φ k); omega
    exact Nat.lt_of_lt_of_le (by omega) (hM _ hh)
  have hlim i : Tendsto (fun k ↦ p (φ k) i) atTop (𝓝 (p₀ i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hconv
  have ht := tensorYoungRawOutput_affinity_tendsto d (fun k ↦ n (φ k))
    (fun k ↦ m (n (φ k))) (hnlim.comp hφ.tendsto_atTop)
    (hm.comp (hnlim.comp hφ.tendsto_atTop)) hn0 hm0 γ hγ
    (hratio.comp (hnlim.comp hφ.tendsto_atTop)) (fun k ↦ p (φ k))
    (fun k ↦ hp _ (hpK (φ k))) (fun k ↦ hp0 _ (hpK (φ k)))
    p₀ (hp p₀ hp₀K) (hp0 p₀ hp₀K) (hord p₀ hp₀K) hlim
  have he := (Metric.tendsto_nhds.mp ht ε hε)
  obtain ⟨k, hk⟩ := he.exists
  rw [Real.dist_eq] at hk
  exact (not_lt_of_ge (hb (φ k))) hk

end Cloning.YoungHyperplane
