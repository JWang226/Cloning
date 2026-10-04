import Cloning.TensorLANEmbeddingWhitening

/-! Whitening sends the actual normalized root covariance Gaussian to the
literal standard Gaussian used in physical mixed LAN. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace NNReal ENNReal
open MeasureTheory Filter
namespace Cloning.TensorLAN
open Cloning.YoungHyperplane Cloning.PCTJointGaussianWhitening
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ}

private theorem standardGaussian_profile (y : Fin d → ℝ) :
    GaussianAffinity.productDensity (fun _ : Fin d => (1/2 : ℝ)) y =
      GaussianAffinity.productDensity (fun _ : Fin d => (1/2 : ℝ)) 0 *
        Real.exp (-(1/2 : ℝ) * ∑ i, (y i)^2) := by
  simp only [GaussianAffinity.productDensity, GaussianAffinity.density, Pi.zero_apply,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, Real.exp_zero, mul_one]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]

private theorem covarianceGaussian_profile (p : Fin (d+1) → ℝ)
    (hp : ∀ a, 0 < p a) (hs : ∑ a, p a = 1)
    (b : OrthonormalBasis (Fin (d+1)) ℝ (EuclideanSpace ℝ (Fin (d+1))))
    (hb : b 0 = sqrtSpectrum p) (x : rootSpace d) :
    covarianceGaussian d p hs x = covarianceGaussian d p hs 0 *
      Real.exp (-(1/2 : ℝ) * ∑ i, (rootWhitening p hp b hb x i)^2) := by
  rw [rootWhitening_norm_sq, covarianceGaussian_eq_exp d p hs hp x,
    covarianceGaussian_eq_exp d p hs hp 0, ← Real.exp_add]
  simp only [Submodule.coe_zero, PiLp.zero_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_div, Finset.sum_const_zero, mul_zero, sub_zero]
  congr 1
  ring

/-- Exact density equality with every allowed whitening frame. The scalar
Jacobian is fixed by the already proved normalization of both actual densities. -/
theorem whiteningDensity_covarianceGaussian (p : Fin (d+1) → ℝ)
    (hp : ∀ a, 0 < p a) (hs : ∑ a, p a = 1)
    (b : OrthonormalBasis (Fin (d+1)) ℝ (EuclideanSpace ℝ (Fin (d+1))))
    (hb : b 0 = sqrtSpectrum p) (y : Fin d → ℝ) :
    whiteningDensity (rootWhitening p hp b hb) (covarianceGaussian d p hs) y =
      GaussianAffinity.productDensity (fun _ : Fin d => (1/2 : ℝ)) y := by
  let W := rootWhitening p hp b hb
  let g := GaussianAffinity.productDensity (fun _ : Fin d => (1/2 : ℝ))
  have hg0 : 0 < g 0 := by
    unfold g GaussianAffinity.productDensity GaussianAffinity.density
    positivity
  let c : ℝ := (whiteningJacobian W : ℝ) * covarianceGaussian d p hs 0 / g 0
  have he (z : Fin d → ℝ) :
      whiteningDensity W (covarianceGaussian d p hs) z = c * g z := by
    unfold whiteningDensity
    rw [covarianceGaussian_profile p hp hs b hb (W.symm z)]
    change (whiteningJacobian W : ℝ) *
      (covarianceGaussian d p hs 0 * Real.exp (-(1/2 : ℝ) * ∑ i, (W (W.symm z) i)^2)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    dsimp only [c, g]
    rw [standardGaussian_profile z]
    change (whiteningJacobian W : ℝ) *
      (covarianceGaussian d p hs 0 * Real.exp (-(1/2 : ℝ) * ∑ i, (z i)^2)) =
      ((whiteningJacobian W : ℝ) * covarianceGaussian d p hs 0 / g 0) *
        (g 0 * Real.exp (-(1/2 : ℝ) * ∑ i, (z i)^2))
    field_simp [hg0.ne']
  have hint := whiteningDensity_integral W (covarianceGaussian d p hs)
  simp_rw [he] at hint
  rw [integral_const_mul, integral_covarianceGaussian d p hs hp] at hint
  have hgint : (∫ z, g z) = 1 := GaussianAffinity.integral_productDensity _ (fun _ => by norm_num)
  rw [hgint, mul_one] at hint
  simpa only [hint, one_mul] using he y

/-- The exact classical LAN Gaussian translation in the final whitening
coordinates, with no additional rescaling. -/
theorem whiteningDensity_translated_covarianceGaussian (p : Fin (d+1) → ℝ)
    (hp : ∀ a, 0 < p a) (hs : ∑ a, p a = 1)
    (b : OrthonormalBasis (Fin (d+1)) ℝ (EuclideanSpace ℝ (Fin (d+1))))
    (hb : b 0 = sqrtSpectrum p) (h : rootSpace d) (y : Fin d → ℝ) :
    whiteningDensity (rootWhitening p hp b hb)
      (fun x => covarianceGaussian d p hs (x - h)) y =
      GaussianAffinity.productDensity (fun _ : Fin d => (1/2 : ℝ))
        (y - rootWhitening p hp b hb h) := by
  have he := whiteningDensity_covarianceGaussian p hp hs b hb
    (y - rootWhitening p hp b hb h)
  simpa only [whiteningDensity, map_sub, ContinuousLinearEquiv.symm_apply_apply] using he

end Cloning.TensorLAN
