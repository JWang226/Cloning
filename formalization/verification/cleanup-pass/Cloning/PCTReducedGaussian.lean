import Cloning.PCTGaussianAssembly
import Cloning.MatrixFidelityBounds
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

/-!
# Physical reduced-purification differential

The Schmidt purification, its normalized tangent perturbations and their
literal reduced density matrices are constructed in the finite computational
basis. The differential and quadratic remainder follow from exact matrix
identities, before invoking any LAN approximation.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder InnerProductSpace Matrix.Norms.L2Operator
open Matrix MeasureTheory Filter

namespace Cloning.PCTReducedGaussian

open Cloning.PCT

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- A coefficient matrix interpreted as a bipartite vector in the physical register. -/
def coefficientVector (M : Matrix A B ℂ) : Register (A × B) :=
  ⟨fun ab => M ab.1 ab.2, memℓp_gen (by
    simp only [ENNReal.toReal_ofNat]; exact (hasSum_fintype _).summable)⟩

@[simp] theorem coefficientVector_apply (M : Matrix A B ℂ) (a : A) (b : B) :
    coefficientVector M (a, b) = M a b := rfl

theorem reducedDensityMatrix_coefficientVector (M : Matrix A B ℂ) :
    reducedDensityMatrix (coefficientVector M) = M * Mᴴ := rfl

theorem reducedDensityMatrix_smul (c : ℂ) (ψ : Register (A × B)) :
    reducedDensityMatrix (c • ψ) = (c * star c) • reducedDensityMatrix ψ := by
  ext a d
  simp only [reducedDensityMatrix, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    StarMul.star_mul, Matrix.smul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The positive diagonal Schmidt coefficient matrix. -/
def schmidtCoefficients (p : A → ℝ) : Matrix A A ℂ :=
  Matrix.diagonal (fun a => (Real.sqrt (p a) : ℂ))

theorem schmidtCoefficients_star (p : A → ℝ) :
    (schmidtCoefficients p)ᴴ = schmidtCoefficients p := by
  simp [schmidtCoefficients, Matrix.diagonal_conjTranspose]

theorem schmidtCoefficients_square (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) :
    schmidtCoefficients p * schmidtCoefficients p =
      Matrix.diagonal (fun a => (p a : ℂ)) := by
  rw [schmidtCoefficients, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact_mod_cast Real.mul_self_sqrt (hp a)

theorem schmidt_reduced (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) :
    reducedDensityMatrix (coefficientVector (schmidtCoefficients p)) =
      Matrix.diagonal (fun a => (p a : ℂ)) := by
  rw [reducedDensityMatrix_coefficientVector, schmidtCoefficients_star,
    schmidtCoefficients_square p hp]

/-- The derivative of partial trace along a purification tangent matrix. -/
def partialTraceDifferential (p : A → ℝ) (Z : Matrix A A ℂ) : Matrix A A ℂ :=
  Z * schmidtCoefficients p + schmidtCoefficients p * Zᴴ

theorem partialTraceDifferential_apply (p : A → ℝ) (Z : Matrix A A ℂ) (a c : A) :
    partialTraceDifferential p Z a c =
      Z a c * (Real.sqrt (p c) : ℂ) + (Real.sqrt (p a) : ℂ) * star (Z c a) := by
  simp [partialTraceDifferential, schmidtCoefficients, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.conjTranspose_apply]

theorem partialTraceDifferential_diagonal (p : A → ℝ) (Z : Matrix A A ℂ) (a : A) :
    partialTraceDifferential p Z a a = (2 * Real.sqrt (p a) * (Z a a).re : ℝ) := by
  rw [partialTraceDifferential_apply]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring

theorem partialTraceDifferential_hermitian (p : A → ℝ) (Z : Matrix A A ℂ) :
    (partialTraceDifferential p Z).IsHermitian := by
  change (partialTraceDifferential p Z)ᴴ = partialTraceDifferential p Z
  simp [partialTraceDifferential, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    schmidtCoefficients_star, add_comm]

/-- The tangent orthogonality condition is exactly the vanishing of the
weighted diagonal sum of the coefficient matrix. -/
theorem schmidt_inner_tangent (p : A → ℝ) (Z : Matrix A A ℂ) :
    ⟪coefficientVector (schmidtCoefficients p), coefficientVector Z⟫_ℂ =
      ∑ a, (Real.sqrt (p a) : ℂ) * Z a a := by
  simp [lp.inner_eq_tsum, tsum_fintype, Fintype.sum_prod_type, coefficientVector,
    schmidtCoefficients, Matrix.diagonal_apply, RCLike.inner_apply, apply_ite,
    mul_comm]

theorem partialTraceDifferential_trace_zero (p : A → ℝ) (Z : Matrix A A ℂ)
    (horth : ⟪coefficientVector (schmidtCoefficients p), coefficientVector Z⟫_ℂ = 0) :
    Matrix.trace (partialTraceDifferential p Z) = 0 := by
  rw [schmidt_inner_tangent] at horth
  have hre := congrArg Complex.re horth
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.zero_re] at hre
  simp only [Matrix.trace, Matrix.diag, partialTraceDifferential_diagonal,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Finset.mul_sum]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  have hs : (∑ a, (Real.sqrt (p a) : ℂ) * ((Z a a).re : ℂ)) = 0 := by
    exact_mod_cast hre
  rw [hs, mul_zero]

/-- Exact numerator expansion of the reduced perturbed purification. -/
theorem reduced_perturbation_exact (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (Z : Matrix A A ℂ) (t : ℝ) :
    reducedDensityMatrix (coefficientVector (schmidtCoefficients p + t • Z)) =
      Matrix.diagonal (fun a => (p a : ℂ)) +
        t • partialTraceDifferential p Z + t ^ 2 • (Z * Zᴴ) := by
  rw [reducedDensityMatrix_coefficientVector]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial,
    schmidtCoefficients_star, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, schmidtCoefficients_square p hp,
    partialTraceDifferential, smul_add, pow_two]
  module

/-- The normalized physical tangent vector, with its exact quadratic denominator. -/
def normalizedTangentVector (p : A → ℝ) (Z : Matrix A A ℂ) (e t : ℝ) : Register (A × A) :=
  ((Real.sqrt (1 + t ^ 2 * e) : ℂ)⁻¹) •
    coefficientVector (schmidtCoefficients p + t • Z)

theorem normalizedTangent_reduced_exact (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (Z : Matrix A A ℂ) (e : ℝ) (he : 0 ≤ e) (t : ℝ) :
    reducedDensityMatrix (normalizedTangentVector p Z e t) =
      (1 + t ^ 2 * e)⁻¹ •
        (Matrix.diagonal (fun a => (p a : ℂ)) +
          t • partialTraceDifferential p Z + t ^ 2 • (Z * Zᴴ)) := by
  have hd : 0 ≤ 1 + t ^ 2 * e := by positivity
  rw [normalizedTangentVector, reducedDensityMatrix_smul]
  have hc : ((Real.sqrt (1 + t ^ 2 * e) : ℂ)⁻¹) *
      star ((Real.sqrt (1 + t ^ 2 * e) : ℂ)⁻¹) = ((1 + t ^ 2 * e)⁻¹ : ℝ) := by
    simp only [map_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hd, Complex.ofReal_inv]
  rw [hc, Complex.coe_smul, reduced_perturbation_exact p hp Z t]

end Cloning.PCTReducedGaussian
