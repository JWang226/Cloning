import Cloning.WeylGaussianSandwichNormalized

/-! Scalar Gaussian twirling identities for completeness of translated vacuum spaces. -/
noncomputable section
open scoped BigOperators Topology ComplexOrder
open MeasureTheory
namespace Cloning.ComplexCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem integral_gaussian_conjugation_single {t : ℝ} (ht : 0 < t) (z : ℂ) :
    (∫ a : ℂ, (Real.exp (-t*‖a‖^2) : ℂ)*displacementPhase a z*displacementPhase (a+z) (-a)) =
      ((Real.pi/t : ℝ) : ℂ)*(Real.exp (-t⁻¹*‖z‖^2) : ℂ) := by
  have he (a : ℂ) : (Real.exp (-t*‖a‖^2) : ℂ)*displacementPhase a z*displacementPhase (a+z) (-a) =
      Complex.exp (-(t : ℂ)*((‖a‖^2 : ℝ) : ℂ)+starRingEnd ℂ z*a+(-z)*starRingEnd ℂ a) := by
    simp only [Complex.ofReal_exp, displacementPhase, ← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, map_neg, map_add]
    ring
  simp_rw [he]
  rw [integral_complex_gaussian_linear_scaled ht]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_inv, norm_sq_cast']
  ring

end Cloning.ComplexCoherent
namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

theorem integral_gaussian_conjugation_product {t : Fin d → ℝ} (ht : ∀i,0<t i) (z : Fin d → ℂ) :
    (∫ a, (gaussianWeight t a : ℂ)*displacementPhase a z*displacementPhase (a+z) (-a)) =
      ((∏ i, Real.pi/t i : ℝ) : ℂ)*(gaussianWeight (fun i => (t i)⁻¹) z : ℂ) := by
  have he (a : Fin d → ℂ) :
      (gaussianWeight t a : ℂ)*displacementPhase a z*displacementPhase (a+z) (-a) =
        ∏ i, ((Real.exp (-t i*‖a i‖^2) : ℂ)*
          Cloning.ComplexCoherent.displacementPhase (a i) (z i)*
          Cloning.ComplexCoherent.displacementPhase (a i+z i) (-a i)) := by
    simp only [gaussianWeight, displacementPhase, Complex.ofReal_prod,
      Pi.add_apply, Pi.neg_apply, Finset.prod_mul_distrib]
  simp_rw [he]
  rw [integral_fintype_prod_volume_eq_prod (fun i (a : ℂ) =>
    (Real.exp (-t i*‖a‖^2) : ℂ)*Cloning.ComplexCoherent.displacementPhase a (z i)*
      Cloning.ComplexCoherent.displacementPhase (a+z i) (-a))]
  simp only [Cloning.ComplexCoherent.integral_gaussian_conjugation_single (ht _),
    Finset.prod_mul_distrib, ← Complex.ofReal_prod, gaussianWeight]

theorem gaussianWeight_mul (s t : Fin d → ℝ) (a : Fin d → ℂ) :
    gaussianWeight s a * gaussianWeight t a = gaussianWeight (s+t) a := by
  simp only [gaussianWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.exp_add]
  congr 1
  simp only [Pi.add_apply]
  ring

end Cloning.MultimodeCoherent
