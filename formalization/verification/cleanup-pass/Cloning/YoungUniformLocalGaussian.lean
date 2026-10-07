import Cloning.YoungHyperplaneCovariance
import Cloning.GaussianAffinity
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# The normalized Gaussian on the actual Young root hyperplane

The density is constructed in an orthonormal eigenbasis of the proved
positive covariance. Its normalization uses actual Euclidean volume.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory
namespace Cloning.YoungHyperplane

variable (d : ℕ) (p : Fin (d + 1) → ℝ) (hp : ∑ i, p i = 1)

def covarianceEigenbasis : OrthonormalBasis (Fin d) ℝ (rootSpace d) :=
  (rootCovariance_isSymmetric d p hp).eigenvectorBasis (rootSpace_finrank d)

def covarianceEigenvalues : Fin d → ℝ :=
  (rootCovariance_isSymmetric d p hp).eigenvalues (rootSpace_finrank d)

theorem covariance_eigenvector (i : Fin d) :
    rootCovariance d p (covarianceEigenbasis d p hp i) =
      covarianceEigenvalues d p hp i • covarianceEigenbasis d p hp i :=
  (rootCovariance_isSymmetric d p hp).apply_eigenvectorBasis (rootSpace_finrank d) i

theorem covarianceEigenvalues_pos (hp0 : ∀ i, 0 < p i) (i : Fin d) :
    0 < covarianceEigenvalues d p hp i := by
  have hv : covarianceEigenbasis d p hp i ≠ 0 :=
    (covarianceEigenbasis d p hp).orthonormal.ne_zero i
  have h := rootCovariance_quadratic_pos d p hp hp0 _ hv
  rw [covariance_eigenvector, real_inner_smul_right] at h
  simpa using h

theorem covariance_eigen_coordinates (x : rootSpace d) (i : Fin d) :
    (covarianceEigenbasis d p hp).repr (rootCovariance d p x) i =
      covarianceEigenvalues d p hp i * (covarianceEigenbasis d p hp).repr x i :=
  (rootCovariance_isSymmetric d p hp).eigenvectorBasis_apply_self_apply
    (rootSpace_finrank d) x i

theorem covariance_eigenvalue_product :
    (∏ i, covarianceEigenvalues d p hp i) = ((d : ℝ) + 1) * ∏ i, p i := by
  let b := covarianceEigenbasis d p hp
  have hm : LinearMap.toMatrix b.toBasis b.toBasis (rootCovariance d p) =
      Matrix.diagonal (covarianceEigenvalues d p hp) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change (b.repr (rootCovariance d p (b j))) i = _
    rw [covariance_eigen_coordinates]
    simp only [b, OrthonormalBasis.repr_self, EuclideanSpace.single_apply,
      Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst j; simp
    · simp [hij, Ne.symm hij]
  have hd := congrArg Matrix.det hm
  rw [LinearMap.det_toMatrix, Matrix.det_diagonal, rootCovariance_det d p hp] at hd
  exact hd.symm

/-- The reciprocal covariance quadratic form in orthonormal eigen-coordinates. -/
theorem covariance_inverse_quadratic_eigen (hp0 : ∀ i, 0 < p i) (x : rootSpace d) :
    (∑ i, ((covarianceEigenbasis d p hp).repr x i) ^ 2 /
      covarianceEigenvalues d p hp i) = ∑ i, (x.1 i) ^ 2 / p i := by
  let b := covarianceEigenbasis d p hp
  let y := inverseCovarianceVector d p x
  have hy i : b.repr y i = b.repr x i / covarianceEigenvalues d p hp i := by
    have h := covariance_eigen_coordinates d p hp y i
    rw [rootCovariance_inverseVector d p hp (fun i ↦ (hp0 i).ne') x] at h
    change b.repr x i = covarianceEigenvalues d p hp i * b.repr y i at h
    exact (eq_div_iff (covarianceEigenvalues_pos d p hp hp0 i).ne').mpr (by linarith)
  have hi := b.repr.inner_map_map x y
  rw [EuclideanSpace.inner_eq_star_dotProduct] at hi
  simp only [dotProduct, Pi.star_apply, star_trivial, hy] at hi
  rw [← inverseCovariance_quadratic d p x]
  change _ = inner ℝ x y
  rw [← hi]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Positive normalized covariance Gaussian, on induced hyperplane volume. -/
def covarianceGaussian (x : rootSpace d) : ℝ :=
  GaussianAffinity.productDensity (fun i ↦ 1 / (2 * covarianceEigenvalues d p hp i))
    (fun i ↦ (covarianceEigenbasis d p hp).repr x i)

theorem covarianceGaussian_nonneg (x : rootSpace d) :
    0 ≤ covarianceGaussian d p hp x :=
  GaussianAffinity.productDensity_nonneg _ _

theorem integrable_covarianceGaussian (hp0 : ∀ i, 0 < p i) :
    Integrable (covarianceGaussian d p hp) volume := by
  let b := covarianceEigenbasis d p hp
  have hprec i : 0 < 1 / (2 * covarianceEigenvalues d p hp i) := by
    positivity [covarianceEigenvalues_pos d p hp hp0 i]
  have hi : Integrable (GaussianAffinity.productDensity
      (fun i ↦ 1 / (2 * covarianceEigenvalues d p hp i))) :=
    Integrable.fintype_prod fun i ↦ GaussianAffinity.integrable_density (hprec i)
  have he := (PiLp.volume_preserving_toLp (Fin d)).symm (MeasurableEquiv.toLp 2 (Fin d → ℝ))
  have hb := b.repr.measurePreserving
  exact ((he.comp hb).integrable_comp_emb
    ((MeasurableEquiv.toLp 2 _).symm.measurableEmbedding.comp b.repr.toHomeomorph.measurableEmbedding)).mpr hi

theorem integral_covarianceGaussian (hp0 : ∀ i, 0 < p i) :
    (∫ x, covarianceGaussian d p hp x ∂volume) = 1 := by
  let b := covarianceEigenbasis d p hp
  have hprec i : 0 < 1 / (2 * covarianceEigenvalues d p hp i) := by
    positivity [covarianceEigenvalues_pos d p hp hp0 i]
  have he := (PiLp.volume_preserving_toLp (Fin d)).symm (MeasurableEquiv.toLp 2 (Fin d → ℝ))
  have hb := b.repr.measurePreserving
  have h := (he.comp hb).integral_comp
    ((MeasurableEquiv.toLp 2 _).symm.measurableEmbedding.comp b.repr.toHomeomorph.measurableEmbedding)
    (GaussianAffinity.productDensity (fun i ↦ 1 / (2 * covarianceEigenvalues d p hp i)))
  exact h.trans (GaussianAffinity.integral_productDensity _ hprec)


theorem covarianceGaussian_pos (hp0 : ∀ i, 0 < p i) (x : rootSpace d) :
    0 < covarianceGaussian d p hp x := by
  unfold covarianceGaussian GaussianAffinity.productDensity
  apply Finset.prod_pos
  intro i _
  have hi := covarianceEigenvalues_pos d p hp hp0 i
  unfold GaussianAffinity.density
  positivity

private theorem log_density_reciprocal {v : ℝ} (hv : 0 < v) (y : ℝ) :
    Real.log (GaussianAffinity.density (1 / (2 * v)) y) =
      -(1 / 2) * Real.log (2 * Real.pi) - 1 / 2 * Real.log v - y ^ 2 / (2 * v) := by
  unfold GaussianAffinity.density
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp,
    Real.log_div (by positivity) (by positivity),
    Real.log_sqrt (by positivity), Real.log_sqrt Real.pi_pos.le,
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by positivity), Real.log_one,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hv.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  ring

/-- Explicit logarithm, including the root-space determinant `d+1`. -/
theorem log_covarianceGaussian (hp0 : ∀ i, 0 < p i) (x : rootSpace d) :
    Real.log (covarianceGaussian d p hp x) =
      -(d : ℝ) / 2 * Real.log (2 * Real.pi) - 1 / 2 * Real.log ((d : ℝ) + 1) -
      1 / 2 * (∑ i, Real.log (p i)) - 1 / 2 * (∑ i, (x.1 i) ^ 2 / p i) := by
  have hprod : (∑ i, Real.log (covarianceEigenvalues d p hp i)) =
      Real.log ((d : ℝ) + 1) + ∑ i, Real.log (p i) := by
    rw [← Real.log_prod (fun i _ ↦ (covarianceEigenvalues_pos d p hp hp0 i).ne'),
      covariance_eigenvalue_product d p hp,
      Real.log_mul (by positivity) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ (hp0 i).ne')),
      Real.log_prod (fun i _ ↦ (hp0 i).ne')]
  have hquad : (∑ i, ((covarianceEigenbasis d p hp).repr x i) ^ 2 /
      (2 * covarianceEigenvalues d p hp i)) = 1 / 2 * ∑ i, (x.1 i) ^ 2 / p i := by
    rw [← covariance_inverse_quadratic_eigen d p hp hp0 x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold covarianceGaussian GaussianAffinity.productDensity
  rw [Real.log_prod (fun i _ ↦ by
    have hi := covarianceEigenvalues_pos d p hp hp0 i
    unfold GaussianAffinity.density
    positivity)]
  simp_rw [log_density_reciprocal (covarianceEigenvalues_pos d p hp hp0 _)]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hprod, hquad]
  ring

/-- The normalized Gaussian has exactly the covariance density required by
Stirling's central-window formula on the induced Euclidean hyperplane. -/
theorem covarianceGaussian_eq_exp (hp0 : ∀ i, 0 < p i) (x : rootSpace d) :
    covarianceGaussian d p hp x = Real.exp
      (-(d : ℝ) / 2 * Real.log (2 * Real.pi) - 1 / 2 * Real.log ((d : ℝ) + 1) -
      1 / 2 * (∑ i, Real.log (p i)) - 1 / 2 * (∑ i, (x.1 i) ^ 2 / p i)) := by
  rw [← log_covarianceGaussian d p hp hp0 x, Real.exp_log (covarianceGaussian_pos d p hp hp0 x)]

end Cloning.YoungHyperplane
