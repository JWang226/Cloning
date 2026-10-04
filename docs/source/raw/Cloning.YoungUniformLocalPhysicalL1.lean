import Cloning.YoungUniformLocalPhysicalLimit
import Mathlib.Topology.Sequences

/-! The uniform Young local limit for the actual physical Schur law,
smoothed on the complete rescaled affine lattice. -/

noncomputable section
open scoped BigOperators Topology Classical
open Filter MeasureTheory
namespace Cloning.YoungHyperplane
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Global L¹ convergence of the actual physical densities to the limiting
covariance Gaussian, with moving positive spectra. -/
theorem tensorYoungDensity_l1_tendsto (d : ℕ) (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (hn0 : ∀ k, 0 < n k)
    (p : ℕ → Fin (d + 1) → ℝ) (hp : ∀ k, ∑ i, p k i = 1)
    (hp0 : ∀ k i, 0 < p k i) (p₀ : Fin (d + 1) → ℝ) (hs₀ : ∑ i, p₀ i = 1)
    (hp₀ : ∀ i, 0 < p₀ i) (hord : StrictAnti p₀)
    (hlim : ∀ i, Tendsto (fun k ↦ p k i) atTop (𝓝 (p₀ i))) :
    Tendsto (fun k ↦ ∫ x, |tensorYoungDensity d (n k) (p k) (fun i ↦ (hp0 k i).le) (hp k) x -
      covarianceGaussian d p₀ hs₀ x| ∂volume) atTop (𝓝 0) := by
  apply density_scheffe volume
    (fun k ↦ tensorYoungDensity d (n k) (p k) (fun i ↦ (hp0 k i).le) (hp k))
    (covarianceGaussian d p₀ hs₀)
    (fun k ↦ integrable_tensorYoungDensity d (n k) (hn0 k) (p k) _ (hp k))
    (integrable_covarianceGaussian d p₀ hs₀ hp₀)
    (fun k ↦ tensorYoungDensity_nonneg d (n k) (p k) _ (hp k))
    (covarianceGaussian_nonneg d p₀ hs₀)
  · intro k
    rw [integral_tensorYoungDensity d (n k) (hn0 k), integral_covarianceGaussian d p₀ hs₀ hp₀]
  · exact ae_of_all volume fun x ↦ tensorYoungDensity_tendsto d n hn hn0 p hp hp0 p₀ hs₀ hp₀ hord hlim x

/-- The reference Gaussian can move with the spectrum at every sample size. -/
theorem tensorYoungDensity_l1_moving_gaussian (d : ℕ) (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (hn0 : ∀ k, 0 < n k)
    (p : ℕ → Fin (d + 1) → ℝ) (hp : ∀ k, ∑ i, p k i = 1)
    (hp0 : ∀ k i, 0 < p k i) (p₀ : Fin (d + 1) → ℝ) (hs₀ : ∑ i, p₀ i = 1)
    (hp₀ : ∀ i, 0 < p₀ i) (hord : StrictAnti p₀)
    (hlim : ∀ i, Tendsto (fun k ↦ p k i) atTop (𝓝 (p₀ i))) :
    Tendsto (fun k ↦ ∫ x, |tensorYoungDensity d (n k) (p k) (fun i ↦ (hp0 k i).le) (hp k) x -
      covarianceGaussian d (p k) (hp k) x| ∂volume) atTop (𝓝 0) := by
  have hf := tensorYoungDensity_l1_tendsto d n hn hn0 p hp hp0 p₀ hs₀ hp₀ hord hlim
  have hg := covarianceGaussian_l1_tendsto d p p₀ hp hs₀ hp0 hp₀ hlim
  have ht := hf.add hg
  simp only [zero_add] at ht
  apply squeeze_zero (fun k ↦ integral_nonneg (fun _ ↦ abs_nonneg _)) ?_ ht
  intro k
  have hfi := integrable_tensorYoungDensity d (n k) (hn0 k) (p k) (fun i ↦ (hp0 k i).le) (hp k)
  have hgi := integrable_covarianceGaussian d (p k) (hp k) (hp0 k)
  have hzi := integrable_covarianceGaussian d p₀ hs₀ hp₀
  erw [← integral_add (hfi.sub hzi).abs (hgi.sub hzi).abs]
  apply integral_mono (hfi.sub hgi).abs ((hfi.sub hzi).abs.add (hgi.sub hzi).abs)
  intro x
  simpa only [abs_sub_comm (covarianceGaussian d p₀ hs₀ x)] using
    abs_sub_le (tensorYoungDensity d (n k) (p k) (fun i ↦ (hp0 k i).le) (hp k) x)
      (covarianceGaussian d p₀ hs₀ x) (covarianceGaussian d (p k) (hp k) x)

/-- The manuscript's uniform Young local limit on every compact subset of
the strictly ordered positive simplex, for the actual normalized physical
Schur measurement. No local limit, character limit or physical block law is
assumed. -/
theorem uniform_tensorYoungDensity_l1 (d : ℕ) (K : Set (Fin (d + 1) → ℝ))
    (hK : IsCompact K) (hp : ∀ p ∈ K, ∑ i, p i = 1)
    (hp0 : ∀ p ∈ K, ∀ i, 0 < p i) (hord : ∀ p ∈ K, StrictAnti p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (p : Fin (d + 1) → ℝ) (hpK : p ∈ K),
      (∫ x, |tensorYoungDensity d N p (fun i ↦ (hp0 p hpK i).le) (hp p hpK) x -
        covarianceGaussian d p (hp p hpK) x| ∂volume) < ε := by
  classical
  by_contra h
  push_neg at h
  have hbad (k : ℕ) := h (max k 1)
  choose n hn p hpK hb using hbad
  obtain ⟨p₀, hp₀K, φ, hφ, hconv⟩ := hK.tendsto_subseq hpK
  have hnlim : Tendsto n atTop atTop :=
    tendsto_atTop_mono (fun k ↦ (le_max_left k 1).trans (hn k)) tendsto_id
  have hn0 : ∀ k, 0 < n (φ k) := fun k ↦ by have h := hn (φ k); omega
  have hlim i : Tendsto (fun k ↦ p (φ k) i) atTop (𝓝 (p₀ i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hconv
  have ht := tensorYoungDensity_l1_moving_gaussian d (fun k ↦ n (φ k))
    (hnlim.comp hφ.tendsto_atTop) hn0 (fun k ↦ p (φ k))
    (fun k ↦ hp _ (hpK (φ k))) (fun k ↦ hp0 _ (hpK (φ k)))
    p₀ (hp p₀ hp₀K) (hp0 p₀ hp₀K) (hord p₀ hp₀K) hlim
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge (hb (φ k))) hk

end Cloning.YoungHyperplane
