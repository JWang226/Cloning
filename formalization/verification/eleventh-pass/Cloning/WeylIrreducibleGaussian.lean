import Cloning.WeylContinuity
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Gaussian weak integrals used to derive the vacuum projector from Weyl operators. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Topology BigOperators

namespace Cloning.ComplexCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The complex two-dimensional Gaussian with arbitrary holomorphic and
antiholomorphic linear coefficients. -/
theorem integral_complex_gaussian_linear (u v : ℂ) :
    (∫ a : ℂ, Complex.exp (-((‖a‖ ^ 2 : ℝ) : ℂ) + u * a + v * starRingEnd ℂ a)) =
      (Real.pi : ℂ) * Complex.exp (u * v) := by
  rw [← (Complex.volume_preserving_equiv_pi.symm).integral_comp
    Complex.measurableEquivPi.symm.measurableEmbedding]
  have he (x : Fin 2 → ℝ) :
      -((‖Complex.measurableEquivPi.symm x‖ ^ 2 : ℝ) : ℂ) +
        u * Complex.measurableEquivPi.symm x + v * starRingEnd ℂ (Complex.measurableEquivPi.symm x) =
      -(1 : ℂ) * (∑ i : Fin 2, (x i : ℂ) ^ 2) +
        ∑ i : Fin 2, (![u + v, Complex.I * (u - v)] i) * x i := by
    rw [norm_sq_cast', Complex.measurableEquivPi_symm_apply]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
    simp [Complex.I_sq]
    ring
  simp_rw [he]
  rw [GaussianFourier.integral_cexp_neg_mul_sum_add (by norm_num : (0 : ℝ) < (1 : ℂ).re)]
  norm_num [Fin.sum_univ_two]
  congr 1
  ring_nf
  simp [Complex.I_sq]
  ring

end Cloning.ComplexCoherent
