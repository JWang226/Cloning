import Cloning.PCTGaussianCovariance

/-! Exact normalization of physical tangent purifications. The quadratic
energy is the actual Hilbert–Schmidt norm of the coefficient matrix, and the
reference spectrum is normalized and orthogonal to the tangent. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators Matrix Matrix.Norms.L2Operator
namespace Cloning.PCTReducedGaussian
open Cloning.PCT Cloning.PCTGaussianCovariance
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [DecidableEq A]

@[simp] lemma coefficientVector_add (M N : Matrix A A ℂ) :
    coefficientVector (M + N) = coefficientVector M + coefficientVector N := by
  ext ab
  rfl

@[simp] lemma coefficientVector_real_smul (t : ℝ) (M : Matrix A A ℂ) :
    coefficientVector (t • M) = t • coefficientVector M := by
  ext ab
  rfl

lemma schmidt_norm_sq (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) :
    ‖coefficientVector (schmidtCoefficients p)‖ ^ 2 = ∑ a, p a := by
  rw [coefficientVector_norm_sq]
  simp only [schmidtCoefficients, Matrix.diagonal_apply, apply_ite, norm_zero,
    ite_pow, zero_pow (by omega : 2 ≠ 0)]
  apply Finset.sum_congr rfl
  intro a _
  simp [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hp a)]

/-- Exact physical numerator norm; its energy is not an arbitrary parameter. -/
theorem tangent_numerator_norm_sq (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hs : ∑ a, p a = 1) (Z : Matrix A A ℂ)
    (horth : ⟪coefficientVector (schmidtCoefficients p), coefficientVector Z⟫_ℂ = 0)
    (t : ℝ) :
    ‖coefficientVector (schmidtCoefficients p + t • Z)‖ ^ 2 =
      1 + t ^ 2 * ‖coefficientVector Z‖ ^ 2 := by
  rw [coefficientVector_add, coefficientVector_real_smul, norm_add_sq (𝕜 := ℂ),
    ← Complex.coe_smul t, inner_smul_right, horth, mul_zero, map_zero, mul_zero, add_zero,
    schmidt_norm_sq p hp, hs, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A genuinely normalized physical tangent vector under precisely the
normalization and orthogonality hypotheses needed for that assertion. -/
theorem normalizedTangentVector_norm (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hs : ∑ a, p a = 1) (Z : Matrix A A ℂ)
    (horth : ⟪coefficientVector (schmidtCoefficients p), coefficientVector Z⟫_ℂ = 0)
    (t : ℝ) : ‖normalizedTangentVector p Z (‖coefficientVector Z‖ ^ 2) t‖ = 1 := by
  have hd : 0 < 1 + t ^ 2 * ‖coefficientVector Z‖ ^ 2 := by positivity
  have hn : ‖normalizedTangentVector p Z (‖coefficientVector Z‖ ^ 2) t‖ ^ 2 = 1 := by
    rw [normalizedTangentVector, norm_smul, mul_pow, norm_inv, inv_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hd.le,
      tangent_numerator_norm_sq p hp hs Z horth t, inv_mul_cancel₀ hd.ne']
  nlinarith [norm_nonneg (normalizedTangentVector p Z (‖coefficientVector Z‖ ^ 2) t)]

/-- Frame tangent energy is the actual Hilbert–Schmidt energy of its matrix. -/
theorem frameTangentMatrix_energy {s : ℕ}
    (u : Fin (s + 1) → Register (A × A)) (hu : Orthonormal ℂ u) (z : Fin s → ℂ) :
    ‖coefficientVector (frameTangentMatrix u z)‖ ^ 2 = GeneralCoherent.energy z := by
  rw [coefficientVector_frameTangentMatrix, frameTangent_norm_sq u hu]

/-- Exact second-order remainder, with the actual tangent energy. -/
theorem normalizedTangent_remainder (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (Z : Matrix A A ℂ) (t : ℝ) :
    let e := ‖coefficientVector Z‖ ^ 2
    reducedDensityMatrix (normalizedTangentVector p Z e t) -
      Matrix.diagonal (fun a => (p a : ℂ)) - t • partialTraceDifferential p Z =
      (t ^ 2 / (1 + t ^ 2 * e)) • (Z * Zᴴ -
        e • Matrix.diagonal (fun a => (p a : ℂ)) -
          (t * e) • partialTraceDifferential p Z) := by
  dsimp only
  rw [normalizedTangent_reduced_exact p hp Z _ (sq_nonneg _) t]
  have hd : 1 + t ^ 2 * ‖coefficientVector Z‖ ^ 2 ≠ 0 := by positivity
  ext a b
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one]
  have hdC : (1 : ℂ) + (t : ℂ) ^ 2 * (‖coefficientVector Z‖ : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast hd
  field_simp [hdC]
  <;> ring

end Cloning.PCTReducedGaussian
