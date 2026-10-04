import Cloning.CountMultinomialLocal

/-! Global L¹ conditional count CLT, with no strict positivity premise on the finite samples. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter MeasureTheory
namespace Cloning.CountMultinomial
open Cloning.YoungGeneral Cloning.YoungHyperplane
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

def shiftedGaussian (d : ℕ) (h : rootSpace d) (x : rootSpace d) : ℝ :=
  covarianceGaussian d (flatSpectrum (d+1)) (flatSpectrum_sum _ (by omega)) (x-h)

theorem integral_shiftedGaussian (d : ℕ) (h : rootSpace d) :
    (∫ x, shiftedGaussian d h x)=1 := by
  unfold shiftedGaussian
  rw [integral_sub_right_eq_self]
  exact integral_covarianceGaussian d _ _ (fun _ ↦ by unfold flatSpectrum; positivity)

theorem integrable_shiftedGaussian (d : ℕ) (h : rootSpace d) :
    Integrable (shiftedGaussian d h) := by
  by_contra hi
  have hh := integral_shiftedGaussian d h
  rw [integral_undef hi] at hh
  norm_num at hh

theorem shiftedGaussian_nonneg (d : ℕ) (h x : rootSpace d) : 0≤shiftedGaussian d h x :=
  covarianceGaussian_nonneg _ _ _ _

theorem density_l1_tendsto_of_positive (d : ℕ) (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (hn0 : ∀ k, 0<n k)
    (p : ℕ → Fin (d+1) → ℝ) (hp : ∀ k i, 0≤p k i) (hs : ∀ k, ∑ i, p k i=1)
    (hp0 : ∀ k i, 0<p k i)
    (hlim : ∀ i, Tendsto (fun k ↦ p k i) atTop (𝓝 (flatSpectrum (d+1) i)))
    (h : rootSpace d)
    (hshift : ∀ i, Tendsto (fun k ↦ Real.sqrt (n k : ℝ)*(p k i-flatSpectrum (d+1) i))
      atTop (𝓝 (h.1 i))) :
    Tendsto (fun k ↦ ∫ x, |density d (n k) (p k) (hp k) (hs k) x-shiftedGaussian d h x|)
      atTop (𝓝 0) := by
  apply density_scheffe volume _ _
    (fun k ↦ integrable_density d (n k) (hn0 k) (p k) (hp k) (hs k))
    (integrable_shiftedGaussian d h) (fun k ↦ density_nonneg d (n k) (p k) (hp k) (hs k))
    (shiftedGaussian_nonneg d h)
  · intro k
    rw [integral_density d (n k) (hn0 k), integral_shiftedGaussian]
  · exact ae_of_all _ (density_moving_tendsto_of_positive d n hn hn0 p hp hs hp0 hlim h hshift)

/-- The true independent-word count densities converge in L¹ under any local
moving probabilities; zeros at finitely many sample sizes cause no restriction. -/
theorem density_l1_tendsto (d : ℕ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (p : ℕ → Fin (d+1) → ℝ) (hp : ∀ k i, 0≤p k i) (hs : ∀ k, ∑ i, p k i=1)
    (hlim : ∀ i, Tendsto (fun k ↦ p k i) atTop (𝓝 (flatSpectrum (d+1) i)))
    (h : rootSpace d)
    (hshift : ∀ i, Tendsto (fun k ↦ Real.sqrt (n k : ℝ)*(p k i-flatSpectrum (d+1) i))
      atTop (𝓝 (h.1 i))) :
    Tendsto (fun k ↦ ∫ x, |density d (n k) (p k) (hp k) (hs k) x-shiftedGaussian d h x|)
      atTop (𝓝 0) := by
  have hp0 : ∀ᶠ k in atTop, ∀ i, 0<p k i :=
    eventually_all.mpr fun i ↦ (hlim i).eventually (eventually_gt_nhds (by unfold flatSpectrum; positivity))
  obtain ⟨K,hK⟩ := eventually_atTop.mp ((hn.eventually (eventually_gt_atTop 0)).and hp0)
  have hk : Tendsto (fun j : ℕ ↦ j+K) atTop atTop :=
    tendsto_atTop_mono (fun j ↦ Nat.le_add_right j K) tendsto_id
  apply (tendsto_add_atTop_iff_nat K).mp
  exact density_l1_tendsto_of_positive d (fun j ↦ n (j+K)) (hn.comp hk)
    (fun j ↦ (hK (j+K) (by omega)).1) (fun j ↦ p (j+K)) (fun j ↦ hp (j+K))
    (fun j ↦ hs (j+K)) (fun j ↦ (hK (j+K) (by omega)).2)
    (fun i ↦ (hlim i).comp hk) h (fun i ↦ (hshift i).comp hk)

end Cloning.CountMultinomial
