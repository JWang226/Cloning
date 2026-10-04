import Cloning.PCTReducedGaussian
import Cloning.WeylThermalFourierWitness

/-! The characteristic function of the actual circular Gaussian tangent in a
purification frame. The projected Hilbert norm fixes its full joint law,
including the covariance lost by removing the reference direction. -/
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.PCTGaussianCovariance
open Cloning.PCT Cloning.PCTReducedGaussian
open Cloning.MultimodeCoherentGaussianMixture Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {C : Type*} [Fintype C] [DecidableEq C] {s : ℕ}

/-- The orthonormal tangent coordinates have exactly their Euclidean energy. -/
theorem frameTangent_norm_sq (u : Fin (s + 1) → Register C)
    (hu : Orthonormal ℂ u) (z : Fin s → ℂ) :
    ‖frameTangent u z‖ ^ 2 = GeneralCoherent.energy z := by
  have huv : Orthonormal ℂ (fun i : Fin s => u i.succ) := hu.comp _ (Fin.succ_injective _)
  have h := huv.inner_sum z z Finset.univ
  simp only [Finset.mem_univ, forall_const, Finset.sum_const_zero, Finset.sum_attach] at h
  rw [inner_self_eq_norm_sq_to_K] at h
  have h' := congrArg Complex.re h
  simp only [Complex.re_sum, Complex.ofReal_pow, Complex.ofReal_re] at h'
  simpa [GeneralCoherent.energy, frameTangent, Complex.conj_mul',
    Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow] using h'

lemma tangent_phase_eq_character (u : Fin (s + 1) → Register C)
    (X : Register C) (z : Fin s → ℂ) :
    Complex.exp (⟪X, frameTangent u z⟫_ℂ - ⟪frameTangent u z, X⟫_ℂ) =
      weylCharacter z (fun i => ⟪u i.succ, X⟫_ℂ) := by
  rw [weylCharacter_eq_prod_exp, ← Complex.exp_sum]
  congr 1
  simp only [frameTangent, inner_sum, sum_inner, inner_smul_right, inner_smul_left,
    ← Finset.sum_sub_distrib, inner_conj_symm]

/-- Exact Fourier transform of the actual Gaussian frame tangent. The
reference component is subtracted by full-frame Parseval, not postulated as
a covariance matrix. -/
theorem frameTangent_characteristic (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register C))
    {v : ℝ} (hv : 0 < v) (X : Register C) :
    (∫ z, Complex.exp (⟪X, frameTangent u z⟫_ℂ - ⟪frameTangent u z, X⟫_ℂ)
      ∂gaussianProductMeasure (fun _ : Fin s => v)) =
      Complex.exp (-((v * (‖X‖ ^ 2 - ‖⟪u 0, X⟫_ℂ‖ ^ 2) : ℝ) : ℂ)) := by
  simp_rw [tangent_phase_eq_character]
  rw [integral_weylCharacter_gaussianProductMeasure (fun _ => hv), ← Complex.exp_sum]
  have hp := u.sum_sq_norm_inner_right X
  rw [Fin.sum_univ_succ] at hp
  have he : ∑ i : Fin s, ‖⟪u i.succ, X⟫_ℂ‖ ^ 2 =
      ‖X‖ ^ 2 - ‖⟪u 0, X⟫_ℂ‖ ^ 2 := by linarith
  congr 1
  norm_cast
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, he]

/-- The coefficient matrix of the actual random physical tangent vector. -/
def frameTangentMatrix {A : Type*} [Fintype A] [DecidableEq A]
    (u : Fin (s + 1) → Register (A × A)) (z : Fin s → ℂ) : Matrix A A ℂ :=
  fun a b => frameTangent u z (a,b)

@[simp] theorem coefficientVector_frameTangentMatrix {A : Type*} [Fintype A] [DecidableEq A]
    (u : Fin (s + 1) → Register (A × A)) (z : Fin s → ℂ) :
    coefficientVector (frameTangentMatrix u z) = frameTangent u z := by
  ext ab
  rfl

lemma coefficientVector_norm_sq {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (M : Matrix A B ℂ) :
    ‖coefficientVector M‖ ^ 2 = ∑ a, ∑ b, ‖M a b‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, tsum_fintype, Fintype.sum_prod_type,
    coefficientVector_apply] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) (coefficientVector M)

/-- Full covariance characteristic in matrix coordinates. For any matrix
`M`, the variance subtracts exactly its Schmidt diagonal component. This
single identity specifies every joint real-linear marginal of the tangent. -/
theorem frameTangentMatrix_characteristic {A : Type*} [Fintype A] [DecidableEq A]
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hu : u 0 = coefficientVector (schmidtCoefficients p))
    {v : ℝ} (hv : 0 < v) (M : Matrix A A ℂ) :
    (∫ z, Complex.exp (⟪coefficientVector M, coefficientVector (frameTangentMatrix u z)⟫_ℂ -
      ⟪coefficientVector (frameTangentMatrix u z), coefficientVector M⟫_ℂ)
      ∂gaussianProductMeasure (fun _ : Fin s => v)) =
      Complex.exp (-((v * ((∑ a, ∑ b, ‖M a b‖ ^ 2) -
        ‖∑ a, (Real.sqrt (p a) : ℂ) * M a a‖ ^ 2) : ℝ) : ℂ)) := by
  simp_rw [coefficientVector_frameTangentMatrix]
  rw [frameTangent_characteristic u hv, hu, schmidt_inner_tangent, coefficientVector_norm_sq]

end Cloning.PCTGaussianCovariance
