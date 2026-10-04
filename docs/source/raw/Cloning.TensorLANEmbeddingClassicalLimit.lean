import Cloning.TensorLANEmbeddingWhiteningGaussian
import Cloning.PCTLocalChartCoordinates

/-! The actual physical classical L1 limit in the fixed whitening coordinates
of the compact-window LAN target. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace NNReal ENNReal
open MeasureTheory Filter
namespace Cloning.TensorLAN
open Cloning.YoungHyperplane Cloning.PCTJointGaussianWhitening
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ}

/-- Physical local spectral perturbations give exactly their tangent shift,
without an asymptotic or sample-size normalization error. -/
theorem spectralCenterShift_local (N : ℕ) (hN : 0 < N)
    (p : Fin (d+1) → ℝ) (h : rootSpace d) :
    spectralCenterShift d N p
      (fun a => p a + (Real.sqrt (N : ℝ))⁻¹ * h.1 a) = h := by
  apply (coordinates d).symm.injective
  funext i
  simp only [spectralCenterShift, LinearEquiv.symm_apply_apply, coordinates_symm_apply, coordinates_head]
  have hn : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  field_simp
  ring

/-- The physical label law converges in total L1 error to the exact translated
precision-1/2 Gaussian in any allowed whitening frame. -/
theorem whitenedFixedBaseYoungDensity_l1_tendsto
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn0 : ∀ k, 0 < n k)
    (pN : ℕ → Fin (d+1) → ℝ) (hsN : ∀ k, ∑ a, pN k a = 1)
    (hpN : ∀ k a, 0 < pN k a) (p : Fin (d+1) → ℝ)
    (hs : ∑ a, p a = 1) (hp : ∀ a, 0 < p a) (hord : StrictAnti p)
    (hlim : ∀ a, Tendsto (fun k => pN k a) atTop (𝓝 (p a)))
    (b : OrthonormalBasis (Fin (d+1)) ℝ (EuclideanSpace ℝ (Fin (d+1))))
    (hb : b 0 = sqrtSpectrum p) :
    Tendsto (fun k => ∫ y,
      |whiteningDensity (rootWhitening p hp b hb)
          (fixedBaseYoungDensity d (n k) p (pN k) (fun a => (hpN k a).le) (hsN k)) y -
        GaussianAffinity.productDensity (fun _ : Fin d => (1/2 : ℝ))
          (y - rootWhitening p hp b hb (spectralCenterShift d (n k) p (pN k)))|)
      atTop (𝓝 0) := by
  have h := fixedBaseYoungDensity_l1_tendsto d n hn hn0 pN hsN hpN p hs hp hord hlim
  have he (k : ℕ) :
      (∫ y, |whiteningDensity (rootWhitening p hp b hb)
          (fixedBaseYoungDensity d (n k) p (pN k) (fun a => (hpN k a).le) (hsN k)) y -
        GaussianAffinity.productDensity (fun _ : Fin d => (1/2 : ℝ))
          (y - rootWhitening p hp b hb (spectralCenterShift d (n k) p (pN k)))|) =
      ∫ x, |fixedBaseYoungDensity d (n k) p (pN k) (fun a => (hpN k a).le) (hsN k) x -
        covarianceGaussian d p hs (x - spectralCenterShift d (n k) p (pN k))| := by
    simp_rw [← whiteningDensity_translated_covarianceGaussian p hp hs b hb]
    exact whiteningDensity_l1 _ _ _
  simpa only [he] using h

end Cloning.TensorLAN
