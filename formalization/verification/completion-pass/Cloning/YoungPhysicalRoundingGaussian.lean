import Cloning.YoungPhysicalRoundingLimit

/-! Exact Gaussian affinity for randomized Young-label dilation. -/
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory Filter
namespace Cloning.YoungHyperplane
open Cloning.YoungRounding
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem sqrt_scale (c x y : ℝ) (hc : 0 ≤ c) :
    Real.sqrt (c*x)*Real.sqrt (c*y) = c*(Real.sqrt x*Real.sqrt y) := by
  rw [Real.sqrt_mul hc, Real.sqrt_mul hc]
  calc
    _ = (Real.sqrt c)^2*(Real.sqrt x*Real.sqrt y) := by ring
    _ = _ := by rw [Real.sq_sqrt hc]

theorem coordinateDensity_affinity (d : ℕ) (f g : rootSpace d → ℝ) :
    (∫ x, Real.sqrt (coordinateDensity d f x)*Real.sqrt (coordinateDensity d g x)) =
      ∫ x, Real.sqrt (f x)*Real.sqrt (g x) := by
  have he : (fun x ↦ Real.sqrt (coordinateDensity d f x)*Real.sqrt (coordinateDensity d g x)) =
      coordinateDensity d (fun x ↦ Real.sqrt (f x)*Real.sqrt (g x)) := by
    funext x
    exact sqrt_scale _ _ _ (Real.sqrt_nonneg _)
  rw [he, integral_coordinateDensity]

private theorem gaussian_density_scale (a h x : ℝ) (ha : 0 ≤ a) (hh : 0 < h) :
    GaussianAffinity.density (a/(h*h)) x = h⁻¹ * GaussianAffinity.density a (h⁻¹*x) := by
  unfold GaussianAffinity.density
  rw [Real.sqrt_div ha, Real.sqrt_mul_self hh.le]
  have he : -(a/(h*h))*x^2 = -a*(h⁻¹*x)^2 := by ring
  rw [he]
  ring

/-- Covariance-dilated Gaussian on the orthonormal physical root coordinates. -/
def dilatedCovarianceGaussian (d : ℕ) (p : Fin (d+1) → ℝ) (hp : ∑ i, p i = 1)
    (γ : ℝ) (x : rootSpace d) : ℝ :=
  GaussianAffinity.productDensity (fun i ↦ (1/(2*covarianceEigenvalues d p hp i))/γ)
    (fun i ↦ (covarianceEigenbasis d p hp).repr x i)

/-- The coordinate Gaussian dilation includes exactly the scalar density Jacobian. -/
theorem affineDensity_headGaussian (d : ℕ) (p : Fin (d+1) → ℝ) (hp : ∑ i, p i = 1)
    (hp0 : ∀ i, 0 < p i) (γ : ℝ) (hγ : 0 < γ) :
    affineDensity (Real.sqrt γ) 0 (headGaussian d p hp) =
      coordinateDensity d (dilatedCovarianceGaussian d p hp γ) := by
  have hs : 0 < Real.sqrt γ := by positivity
  have hss : Real.sqrt γ*Real.sqrt γ = γ := Real.mul_self_sqrt hγ.le
  have hi i : 0 ≤ 1/(2*covarianceEigenvalues d p hp i) := by
    positivity [covarianceEigenvalues_pos d p hp hp0 i]
  have hden (i : Fin d) (y : ℝ) :
      GaussianAffinity.density ((1/(2*covarianceEigenvalues d p hp i))/γ) y =
        (Real.sqrt γ)⁻¹ * GaussianAffinity.density (1/(2*covarianceEigenvalues d p hp i))
          ((Real.sqrt γ)⁻¹*y) := by
    convert gaussian_density_scale (1/(2*covarianceEigenvalues d p hp i)) (Real.sqrt γ) y (hi i) hs using 1 <;> rw [hss]
  funext x
  simp only [affineDensity, headGaussian, coordinateDensity, dilatedCovarianceGaussian,
    covarianceGaussian, GaussianAffinity.productDensity, sub_zero, map_smul,
    PiLp.smul_apply, smul_eq_mul, Fintype.card_fin]
  simp_rw [hden]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
  ring

/-- The actual covariance and root-space Jacobians cancel in the Gaussian affinity. -/
theorem headGaussian_dilation_affinity (d : ℕ) (p : Fin (d+1) → ℝ) (hp : ∑ i, p i = 1)
    (hp0 : ∀ i, 0 < p i) (γ : ℝ) (hγ : 0 < γ) :
    (∫ x, Real.sqrt (headGaussian d p hp x) *
      Real.sqrt (affineDensity (Real.sqrt γ) 0 (headGaussian d p hp) x)) =
      Cloning.classicalValue γ (d+1) := by
  rw [affineDensity_headGaussian d p hp hp0 γ hγ]
  change (∫ x, Real.sqrt (coordinateDensity d (covarianceGaussian d p hp) x)*
    Real.sqrt (coordinateDensity d (dilatedCovarianceGaussian d p hp γ) x)) = _
  rw [coordinateDensity_affinity]
  let b := covarianceEigenbasis d p hp
  let a := fun i ↦ 1/(2*covarianceEigenvalues d p hp i)
  have ha i : 0 < a i := by
    dsimp [a]
    positivity [covarianceEigenvalues_pos d p hp hp0 i]
  have he := (PiLp.volume_preserving_toLp (Fin d)).symm (MeasurableEquiv.toLp 2 (Fin d → ℝ))
  have hb := b.repr.measurePreserving
  have h := (he.comp hb).integral_comp
    ((MeasurableEquiv.toLp 2 _).symm.measurableEmbedding.comp b.repr.toHomeomorph.measurableEmbedding)
    (fun x ↦ Real.sqrt (GaussianAffinity.productDensity a x)*
      Real.sqrt (GaussianAffinity.productDensity (fun i ↦ a i/γ) x))
  change (∫ x, Real.sqrt (covarianceGaussian d p hp x)*
    Real.sqrt (dilatedCovarianceGaussian d p hp γ x)) = _ at h ⊢
  rw [h, GaussianAffinity.integral_product_dilation a ha hγ]
  simp [Cloning.classicalValue]

end Cloning.YoungHyperplane
