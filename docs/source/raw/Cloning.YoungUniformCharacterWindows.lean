import Cloning.YoungUniformLocalCharacter
import Cloning.PhysicalCloningConverseSpectrum

/-! Literal compact-uniform character normalization for arbitrary shrinking
spectral windows, with the numerator orientation used in the manuscript. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace Cloning.YoungMultinomial
open Cloning.TensorLie Cloning.YoungGeneral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ}

theorem spectralCorrection_tendsto (pN : ℕ→Fin d→ℝ) (p : Fin d→ℝ)
    (hp : ∀ i, 0<p i)
    (hlim : ∀ i, Tendsto (fun n => pN n i) atTop (𝓝 (p i))) :
    Tendsto (fun n => spectralCorrection (pN n)) atTop (𝓝 (spectralCorrection p)) := by
  unfold spectralCorrection
  apply tendsto_finset_prod
  intro i _
  apply tendsto_finset_prod
  intro j _
  exact tendsto_const_nhds.sub ((hlim j).div (hlim i) (hp i).ne')

/-- No prescribed rate for the shrinking window is required. In particular,
the uniformity ranges over all partitions and every spectrum in the compact set. -/
theorem eventually_uniform_character_normalization
    (K : Set (SimpleSpectrum d)) (hK : IsCompact K)
    (δ : ℕ→ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ (N : ℕ) in atTop, ∀ p∈K, ∀ μ : Fin d→ℕ, Antitone μ →
      (∀ i, |(μ i:ℝ)/(N:ℝ)-p.eigenvalue i|≤δ N) →
      |(∏ i, p.eigenvalue i ^ μ i)/physicalSectorCharacter μ p.eigenvalue -
        spectralCorrection p.eigenvalue|<ε := by
  rw [eventually_atTop]
  by_contra h
  push_neg at h
  choose n hn p hpK μ hμ hclose hbad using h
  have hnlim : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  obtain ⟨p₀,hp₀,φ,hφ,hconv⟩ := (hK.image SimpleSpectrum.continuous_eigenvalue).tendsto_subseq
    (fun N => show (p N).eigenvalue ∈ SimpleSpectrum.eigenvalue '' K from ⟨p N,hpK N,rfl⟩)
  obtain ⟨p₁,hp₁,rfl⟩ := hp₀
  have hlim i : Tendsto (fun N => (p (φ N)).eigenvalue i) atTop (𝓝 (p₁.eigenvalue i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hconv
  have hnφ := hnlim.comp hφ.tendsto_atTop
  have hdφ := hδ.comp hnφ
  have hcount i : Tendsto (fun N => (μ (φ N) i:ℝ)/(n (φ N):ℝ)) atTop
      (𝓝 (p₁.eigenvalue i)) := by
    have hlo : ∀ N, (p (φ N)).eigenvalue i - δ (n (φ N)) ≤
        (μ (φ N) i:ℝ)/(n (φ N):ℝ) := fun N => by
      have ht := (abs_le.mp (hclose (φ N) i)).1
      linarith
    have hhi : ∀ N, (μ (φ N) i:ℝ)/(n (φ N):ℝ) ≤
        (p (φ N)).eigenvalue i + δ (n (φ N)) := fun N => by
      have ht := (abs_le.mp (hclose (φ N) i)).2
      linarith
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using (hlim i).sub hdφ) (by simpa using (hlim i).add hdφ) hlo hhi
  have ht := physicalSectorCharacter_div_highest_tendsto
    (fun N => n (φ N)) hnφ (fun N => μ (φ N))
    (Eventually.of_forall (fun N => hμ (φ N)))
    (fun N => (p (φ N)).eigenvalue) p₁.eigenvalue p₁.positive p₁.strictAnti hlim hcount
  have hc := spectralCorrection_pos p₁.eigenvalue p₁.positive p₁.strictAnti
  have ht' := ht.inv₀ (inv_ne_zero hc.ne')
  simp only [inv_div,inv_inv] at ht'
  have he := ht'.sub (spectralCorrection_tendsto _ _ p₁.positive hlim)
  rw [sub_self] at he
  obtain ⟨N,hN⟩ := (Metric.tendsto_nhds.mp he ε hε).exists
  rw [Real.dist_eq,sub_zero] at hN
  exact (not_lt_of_ge (hbad (φ N))) hN

end Cloning.YoungMultinomial
