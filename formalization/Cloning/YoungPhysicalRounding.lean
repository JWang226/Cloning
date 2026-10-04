import Cloning.YoungPhysicalRoundingAffinity

/-! Compact-uniform classical cloning cost of the actual physical Young kernel,
including the specified compatibility fallback. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter MeasureTheory
namespace Cloning.YoungHyperplane
open Cloning.TensorLie Cloning.YoungGeneral Cloning.YoungCompatibility
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Compact-uniform invisibility of the actual fallback, against any normalized target. -/
theorem uniform_tensorYoungFallback_affinity_error {d : ℕ} (hd : 1 ≤ d)
    (K : Set (Fin (d+1) → ℝ)) (hK : IsCompact K)
    (hp : ∀ p ∈ K, ∑ i, p i = 1) (hp0 : ∀ p ∈ K, ∀ i, 0 < p i)
    (hord : ∀ p ∈ K, StrictAnti p)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hratio : Tendsto (fun n ↦ (m n : ℝ)/n) atTop (𝓝 γ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (p : Fin (d+1) → ℝ) (hpK : p ∈ K),
      ∀ Q : PMF (Fin (d+1) → ℤ),
      |CountableScheffe.affinity
        (probability (tensorYoungFallbackOutput d N (m N) ((m N : ℝ)/N) p
          (fun i ↦ (hp0 p hpK i).le) (hp p hpK))) (probability Q) -
       CountableScheffe.affinity
        (probability (tensorYoungRawOutput d N (m N) ((m N : ℝ)/N) p
          (fun i ↦ (hp0 p hpK i).le) (hp p hpK))) (probability Q)| < ε := by
  let mz : ℕ → ℤ := fun n ↦ if n = 0 then 0 else m n
  have hmz n : (mz n : ℝ) = ((m n : ℝ)/n)*(n : ℝ) := by
    by_cases hn : n = 0
    · simp [mz, hn]
    · simp [mz, hn, div_mul_cancel₀ _ (by exact_mod_cast hn : (n : ℝ) ≠ 0)]
  obtain ⟨a, ha, hpK, hgap⟩ := compact_spectra_positive_gap K hK hp0 hord
  have he := eventually_rounding_support_compatible hd mz (fun n ↦ (m n : ℝ)/n)
    shrinkingRadius γ a ha hγ hratio shrinkingRadius_tendsto_zero hmz
  let s := Fintype.card (PositiveRoot (d+1))
  let B := fun n : ℕ ↦ (((d+1 : ℕ) : ℝ)+1)^s *
    (((n : ℝ)+1)^s * concentrationEnvelope (d+1) n)
  have hB : Tendsto B atTop (𝓝 0) := by
    simpa only [B, mul_zero] using
      (polynomial_concentrationEnvelope_tendsto_zero (d+1) s).const_mul
        ((((d+1 : ℕ) : ℝ)+1)^s)
  have hcost : Tendsto (fun n ↦ Real.sqrt (2*B n)) atTop (𝓝 0) := by
    simpa only [mul_zero, Real.sqrt_zero] using (hB.const_mul 2).sqrt
  have hev : ∀ᶠ N : ℕ in atTop, ∀ (p : Fin (d+1) → ℝ) (hpIn : p ∈ K),
      ∀ Q : PMF (Fin (d+1) → ℤ),
      |CountableScheffe.affinity
        (probability (tensorYoungFallbackOutput d N (m N) ((m N : ℝ)/N) p
          (fun i ↦ (hp0 p hpIn i).le) (hp p hpIn))) (probability Q) -
       CountableScheffe.affinity
        (probability (tensorYoungRawOutput d N (m N) ((m N : ℝ)/N) p
          (fun i ↦ (hp0 p hpIn i).le) (hp p hpIn))) (probability Q)| < ε := by
    filter_upwards [he, hcost.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with N hN hc hN0
    intro p hpIn Q
    let P := tensorYoungPMF N (d+1) p (fun i ↦ (hp0 p hpIn i).le) (hp p hpIn)
    have hsame (μ : Shape (d+1) N)
        (hμ : Typical N p (shrinkingRadius N) (integerShape μ)) :
        fallbackKernel ((m N : ℝ)/N) N (m N) (integerShape μ) =
          rawKernel ((m N : ℝ)/N) (m N) (integerShape μ) := by
      apply fallbackKernel_eq_raw_of_support
      have hh := hN p (hpK p hpIn) (hgap p hpIn) (integerShape μ) hμ.1.2.2 hμ.2
      simpa only [mz, if_neg (by omega : N ≠ 0)] using hh
    have hb := bind_fallback_affinity_bound P _ _
      (fun μ ↦ Typical N p (shrinkingRadius N) (integerShape μ)) hsame Q
    have hbad := tensorYoung_badMass_le_tail (N := N) p (fun i ↦ (hp0 p hpIn i).le)
      (hp p hpIn) (shrinkingRadius N)
    have htail := tensorYoungPMF_tail_shrinking_le N hN0 p (fun i ↦ (hp0 p hpIn i).le)
      (hp p hpIn) (hord p hpIn).antitone
    exact (hb.trans (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hbad.trans htail) (by norm_num)))).trans_lt hc
  exact eventually_atTop.mp hev

/-- The manuscript's actual normalized fallback kernel has exactly the Gaussian
classical cloning cost, uniformly on compact strictly ordered positive spectra.
All physical Young-law, concentration, cell, Jacobian, and rounding estimates are proved. -/
theorem uniform_tensorYoungFallbackOutput_affinity {d : ℕ} (hd : 1 ≤ d)
    (K : Set (Fin (d+1) → ℝ)) (hK : IsCompact K)
    (hp : ∀ p ∈ K, ∑ i, p i = 1) (hp0 : ∀ p ∈ K, ∀ i, 0 < p i)
    (hord : ∀ p ∈ K, StrictAnti p)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (γ : ℝ) (hγ : 1 < γ) (hratio : Tendsto (fun n ↦ (m n : ℝ)/n) atTop (𝓝 γ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (p : Fin (d+1) → ℝ) (hpK : p ∈ K),
      |CountableScheffe.affinity
        (probability (tensorYoungFallbackOutput d N (m N) ((m N : ℝ)/N) p
          (fun i ↦ (hp0 p hpK i).le) (hp p hpK)))
        (probability (tensorYoungIntegerPMF d (m N) p
          (fun i ↦ (hp0 p hpK i).le) (hp p hpK))) - Cloning.classicalValue γ (d+1)| < ε := by
  obtain ⟨N₁, hN₁⟩ := uniform_tensorYoungRawOutput_affinity d K hK hp hp0 hord
    m hm γ (by linarith) hratio (ε/2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := uniform_tensorYoungFallback_affinity_error hd K hK hp hp0 hord
    m γ hγ hratio (ε/2) (by positivity)
  refine ⟨max N₁ N₂, fun N hN p hpK ↦ ?_⟩
  have h1 := hN₁ N ((le_max_left _ _).trans hN) p hpK
  have h2 := hN₂ N ((le_max_right _ _).trans hN) p hpK
    (tensorYoungIntegerPMF d (m N) p (fun i ↦ (hp0 p hpK i).le) (hp p hpK))
  have ht := abs_sub_le
    (CountableScheffe.affinity
      (probability (tensorYoungFallbackOutput d N (m N) ((m N : ℝ)/N) p
        (fun i ↦ (hp0 p hpK i).le) (hp p hpK)))
      (probability (tensorYoungIntegerPMF d (m N) p (fun i ↦ (hp0 p hpK i).le) (hp p hpK))))
    (CountableScheffe.affinity
      (probability (tensorYoungRawOutput d N (m N) ((m N : ℝ)/N) p
        (fun i ↦ (hp0 p hpK i).le) (hp p hpK)))
      (probability (tensorYoungIntegerPMF d (m N) p (fun i ↦ (hp0 p hpK i).le) (hp p hpK))))
    (Cloning.classicalValue γ (d+1))
  linarith

end Cloning.YoungHyperplane
