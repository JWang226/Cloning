import Cloning.TensorLANEmbeddingClassicalLimit
import Cloning.TensorLANEmbeddingLocalSpectrum

/-! Compact-uniform physical Young convergence in the exact fixed classical
coordinates of the LAN model. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace
open Filter MeasureTheory
namespace Cloning.TensorLAN
open Cloning.YoungHyperplane Cloning.PCTJointGaussianWhitening Cloning.PCTLocalChart
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ}

theorem whiten_spectralCenterShift_local (N : ℕ) (hN : 0 < N)
    (p : Fin (d+1) → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (d+1)) ℝ (EuclideanSpace ℝ (Fin (d+1))))
    (hb : b 0 = sqrtSpectrum p) (h : Fin (d+1) → ℝ) (hh : ∑ a, h a = 0) :
    rootWhitening p hp b hb (spectralCenterShift d N p (localSpectrum p h N)) =
      whiten p b h := by
  let v : rootSpace d := ⟨WithLp.toLp 2 h, hh⟩
  have he : localSpectrum p h N = fun a => p a + (Real.sqrt (N : ℝ))⁻¹ * v.1 a := by
    funext a
    simp [localSpectrum, sampleScale, v, one_div]
  rw [he, spectralCenterShift_local N hN]
  rfl

/-- Positivity is an explicit finite-sample side condition, which the uniform
admissibility theorem discharges on every bounded trace-zero window. -/
theorem uniform_whitened_local_Young_l1
    (p : Fin (d+1) → ℝ) (hp : ∀ a, 0 < p a)
    (hs : ∑ a, p a = 1) (hord : StrictAnti p)
    (b : OrthonormalBasis (Fin (d+1)) ℝ (EuclideanSpace ℝ (Fin (d+1))))
    (hb : b 0 = sqrtSpectrum p) (B : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : Fin (d+1) → ℝ, ‖h‖ ≤ B →
      ∀ hh : ∑ a, h a = 0, ∀ hpos : ∀ a, 0 < localSpectrum p h N a,
      (∫ y, |whiteningDensity (rootWhitening p hp b hb)
        (fixedBaseYoungDensity d N p (localSpectrum p h N)
          (fun a => (hpos a).le) (localSpectrum_sum p h hs hh N)) y -
        GaussianAffinity.productDensity (fun _ : Fin d => (1/2 : ℝ))
          (y-whiten p b h)|) < ε := by
  by_contra hbad
  push_neg at hbad
  have hbad' (k : ℕ) := hbad (max k 1)
  choose n hn h hh hzero hpos hfail using hbad'
  have hnlim : Tendsto n atTop atTop := tendsto_atTop_mono
    (fun k => (le_max_left k 1).trans (hn k)) tendsto_id
  have hn0 : ∀ k, 0 < n k := fun k => by have h := hn k; omega
  have hr (a : Fin (d+1)) : Tendsto (fun k => localSpectrum p (h k) (n k) a)
      atTop (𝓝 (p a)) :=
    localSpectrum_tendsto_of_bounded p n hnlim h B (Eventually.of_forall hh) a
  have ht := whitenedFixedBaseYoungDensity_l1_tendsto n hnlim hn0
    (fun k => localSpectrum p (h k) (n k))
    (fun k => localSpectrum_sum p (h k) hs (hzero k) (n k)) hpos p hs hp hord hr b hb
  simp_rw [whiten_spectralCenterShift_local _ (hn0 _) p hp b hb _ (hzero _)] at ht
  obtain ⟨k,hk⟩ := (ht.eventually (eventually_lt_nhds hε)).exists
  exact (not_lt_of_ge (hfail k)) hk

end Cloning.TensorLAN
