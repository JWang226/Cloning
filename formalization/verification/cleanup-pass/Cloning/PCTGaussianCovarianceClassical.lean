import Cloning.PCTGaussianCovariance

/-! The classical marginal of the actual purification tangent Gaussian has
covariance `2 v (diag p - p pᵀ)`, proved by its characteristic function. -/
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.PCTGaussianCovariance
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [DecidableEq A] {s : ℕ}

lemma coefficientVector_inner (M N : Matrix A A ℂ) :
    ⟪coefficientVector M, coefficientVector N⟫_ℂ =
      ∑ a, ∑ b, star (M a b) * N a b := by
  simp [lp.inner_eq_tsum, tsum_fintype, Fintype.sum_prod_type, coefficientVector,
    RCLike.inner_apply, mul_comm]

/-- Classical score coordinate of the literal reduced-state differential. -/
def classicalCoordinate (p : A → ℝ) (Z : Matrix A A ℂ) (a : A) : ℝ :=
  2 * Real.sqrt (p a) * (Z a a).re

lemma classicalCoordinate_sum_zero (p : A → ℝ) (Z : Matrix A A ℂ)
    (horth : ⟪coefficientVector (schmidtCoefficients p), coefficientVector Z⟫_ℂ = 0) :
    ∑ a, classicalCoordinate p Z a = 0 := by
  have h := congrArg Complex.re (partialTraceDifferential_trace_zero p Z horth)
  simpa [Matrix.trace, Matrix.diag, partialTraceDifferential_diagonal, classicalCoordinate] using h

/-- The imaginary diagonal test matrix representing a classical Fourier test. -/
def classicalTest (p t : A → ℝ) : Matrix A A ℂ :=
  Matrix.diagonal (fun a => -Complex.I * (Real.sqrt (p a) : ℂ) * (t a : ℂ))

lemma classicalTest_phase (p t : A → ℝ) (Z : Matrix A A ℂ) :
    ⟪coefficientVector (classicalTest p t), coefficientVector Z⟫_ℂ -
      ⟪coefficientVector Z, coefficientVector (classicalTest p t)⟫_ℂ =
        Complex.I * ((∑ a, t a * classicalCoordinate p Z a : ℝ) : ℂ) := by
  simp only [coefficientVector_inner, classicalTest, Matrix.diagonal_apply]
  simp only [apply_ite, star_zero, zero_mul, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [← Finset.sum_sub_distrib, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Complex.ext <;> simp [classicalCoordinate, Complex.mul_re, Complex.mul_im] <;> ring

lemma classicalTest_norm_sq (p t : A → ℝ) (hp : ∀ a, 0 ≤ p a) :
    ‖coefficientVector (classicalTest p t)‖ ^ 2 = ∑ a, p a * (t a) ^ 2 := by
  rw [coefficientVector_norm_sq]
  simp only [classicalTest, Matrix.diagonal_apply, apply_ite, norm_zero, zero_pow (by omega : 2 ≠ 0),
    ite_pow, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro a _
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (hp a)]
  simp

lemma classicalTest_reference_sq (p t : A → ℝ) (hp : ∀ a, 0 ≤ p a) :
    ‖⟪coefficientVector (schmidtCoefficients p), coefficientVector (classicalTest p t)⟫_ℂ‖ ^ 2 =
      (∑ a, p a * t a) ^ 2 := by
  rw [schmidt_inner_tangent]
  have he : (∑ a, (Real.sqrt (p a) : ℂ) * classicalTest p t a a) =
      -Complex.I * ((∑ a, p a * t a : ℝ) : ℂ) := by
    simp only [classicalTest, Matrix.diagonal_apply_eq, Complex.ofReal_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    have hs : (Real.sqrt (p a) : ℂ) ^ 2 = (p a : ℂ) := by
      exact_mod_cast Real.sq_sqrt (hp a)
    push_cast
    linear_combination -Complex.I * (t a : ℂ) * hs
  rw [he]
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- Joint classical characteristic. Its exponent is exactly minus `v` times
the multinomial quadratic form, hence covariance `2 v Σp`. -/
theorem classicalCoordinate_characteristic
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p))
    {v : ℝ} (hv : 0 < v) (t : A → ℝ) :
    (∫ z, Complex.exp (Complex.I * ((∑ a,
      t a * classicalCoordinate p (frameTangentMatrix u z) a : ℝ) : ℂ))
      ∂gaussianProductMeasure (fun _ : Fin s => v)) =
      Complex.exp (-((v * ((∑ a, p a * (t a) ^ 2) - (∑ a, p a * t a) ^ 2) : ℝ) : ℂ)) := by
  simp_rw [← classicalTest_phase, coefficientVector_frameTangentMatrix]
  rw [frameTangent_characteristic u hv, hu, classicalTest_norm_sq p t hp,
    classicalTest_reference_sq p t hp]

end Cloning.PCTGaussianCovariance
