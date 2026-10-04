import Cloning.PCTGaussianCovarianceClassical
import Cloning.PCTGaussianOutput

/-! Exact circular Gaussian orbital marginals of the reduced purification
differential, with the thermal convention used by the actual Weyl operators. -/
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.PCTGaussianCovariance
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [DecidableEq A] {s : ℕ}

/-- The orbital displacement coordinate of the reduced-state differential. -/
def orbitalCoordinate (p : A → ℝ) (Z : Matrix A A ℂ) (i j : A) : ℂ :=
  ((Real.sqrt (p i) : ℂ) * Z j i + (Real.sqrt (p j) : ℂ) * star (Z i j)) /
    (Real.sqrt (p i - p j) : ℂ)

lemma orbitalCoordinate_differential (p : A → ℝ) (Z : Matrix A A ℂ) (i j : A) :
    orbitalCoordinate p Z i j = partialTraceDifferential p Z j i /
      (Real.sqrt (p i - p j) : ℂ) := by
  rw [partialTraceDifferential_apply]
  unfold orbitalCoordinate
  ring

def orbitalTest (p : A → ℝ) (i j : A) (ξ : ℂ) : Register (A × A) :=
  (star ξ * (Real.sqrt (p j) : ℂ) / (Real.sqrt (p i - p j) : ℂ)) •
    registerBasis (A × A) (i,j) +
  (-ξ * (Real.sqrt (p i) : ℂ) / (Real.sqrt (p i - p j) : ℂ)) •
    registerBasis (A × A) (j,i)

lemma orbitalTest_phase (p : A → ℝ) (i j : A) (ξ : ℂ) (Z : Matrix A A ℂ) :
    ⟪orbitalTest p i j ξ, coefficientVector Z⟫_ℂ -
      ⟪coefficientVector Z, orbitalTest p i j ξ⟫_ℂ =
      ξ * star (orbitalCoordinate p Z i j) - star ξ * orbitalCoordinate p Z i j := by
  have hi (a b : A) : ⟪coefficientVector Z, lp.single 2 (a,b) 1⟫_ℂ =
      star (Z a b) := by
    rw [← inner_conj_symm]
    simp only [registerBasis_apply, register_inner_single, coefficientVector_apply]
    rfl
  simp only [orbitalTest, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, hi, registerBasis_apply, register_inner_single, coefficientVector_apply,
    orbitalCoordinate, map_div₀, map_mul, map_neg, star_star,
    star_add, star_mul, star_div₀, star_neg, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  ring

lemma orbitalTest_orthogonal_reference (p : A → ℝ) (i j : A) (hij : i ≠ j) (ξ : ℂ) :
    ⟪coefficientVector (schmidtCoefficients p), orbitalTest p i j ξ⟫_ℂ = 0 := by
  have hi (a b : A) (hab : a ≠ b) :
      ⟪coefficientVector (schmidtCoefficients p), registerBasis (A × A) (a,b)⟫_ℂ = 0 := by
    rw [← inner_conj_symm]
    simp [registerBasis_apply, register_inner_single, coefficientVector_apply,
      schmidtCoefficients, Matrix.diagonal_apply, hab]
  simp only [orbitalTest, inner_add_right, inner_smul_right, hi i j hij, hi j i hij.symm,
    mul_zero, add_zero]

lemma orbitalTest_norm_sq (p : A → ℝ) (i j : A) (hij : i ≠ j)
    (hpi : 0 ≤ p i) (hpj : 0 ≤ p j) (hgap : 0 < p i - p j) (ξ : ℂ) :
    ‖orbitalTest p i j ξ‖ ^ 2 = (p i + p j) / (p i - p j) * ‖ξ‖ ^ 2 := by
  have horth : ⟪registerBasis (A × A) (i,j), registerBasis (A × A) (j,i)⟫_ℂ = 0 := by
    exact (registerBasis (A × A)).orthonormal.inner_eq_zero (by simp [hij])
  rw [orbitalTest, norm_add_sq (𝕜 := ℂ)]
  simp only [inner_smul_left, inner_smul_right, horth, mul_zero, map_zero,
    mul_zero, add_zero, norm_smul, norm_div, norm_mul, norm_star, norm_neg,
    (registerBasis (A × A)).orthonormal.norm_eq_one, mul_one, Complex.norm_real,
    Real.norm_eq_abs, div_pow, mul_pow, sq_abs, Real.sq_sqrt hpi,
    Real.sq_sqrt hpj, Real.sq_sqrt hgap.le]
  ring

/-- The full one-pair circular Gaussian characteristic with variance
`v (pᵢ+pⱼ)/(pᵢ-pⱼ)`. It is derived from the actual frame tangent law. -/
theorem orbitalCoordinate_characteristic
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hu : u 0 = coefficientVector (schmidtCoefficients p))
    (i j : A) (hij : i ≠ j) (hpi : 0 ≤ p i) (hpj : 0 ≤ p j)
    (hgap : 0 < p i - p j) {v : ℝ} (hv : 0 < v) (ξ : ℂ) :
    (∫ z, Complex.exp (ξ * star (orbitalCoordinate p (frameTangentMatrix u z) i j) -
      star ξ * orbitalCoordinate p (frameTangentMatrix u z) i j)
      ∂gaussianProductMeasure (fun _ : Fin s => v)) =
      Complex.exp (-((v * ((p i + p j) / (p i - p j)) * ‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
  simp_rw [← orbitalTest_phase, coefficientVector_frameTangentMatrix]
  rw [frameTangent_characteristic u hv, hu, orbitalTest_orthogonal_reference p i j hij,
    norm_zero, zero_pow (by omega : 2 ≠ 0), sub_zero,
    orbitalTest_norm_sq p i j hij hpi hpj hgap]
  congr 1
  push_cast
  ring

/-- The orbital variance is precisely the displacement variance producing
the `Thermal.pct` output parameter. -/
theorem orbitalVariance_eq_pctDisplacementVariance (g pi pj : ℝ)
    (hpi : 0 < pi) (hgap : pj < pi) :
    (g - 1) * (pi + pj) / (pi - pj) =
      Cloning.PCTGaussianOutput.pctDisplacementVariance g (pj / pi) := by
  unfold Cloning.PCTGaussianOutput.pctDisplacementVariance
  have hden : pi - pj ≠ 0 := (sub_pos.mpr hgap).ne'
  field_simp [hpi.ne', hden]
  <;> ring

end Cloning.PCTGaussianCovariance
