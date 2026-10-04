import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Exact mixed moments of the circular complex Gaussian density, proved by
polar coordinates and the Gamma integral. -/

namespace Cloning.ComplexGaussianMoments

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped Real

lemma angular_integral_zero (n m : ℕ) (hnm : n ≠ m) :
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi,
      Complex.exp (((n : ℂ) - m) * Complex.I * θ)) = 0 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hc : ((n : ℂ) - m) * Complex.I ≠ 0 := by
    apply mul_ne_zero _ Complex.I_ne_zero
    exact sub_ne_zero.mpr (by exact_mod_cast hnm)
  rw [integral_exp_mul_complex hc]
  have he : Complex.exp (((n : ℂ) - m) * Complex.I * (Real.pi : ℝ)) =
      Complex.exp (((n : ℂ) - m) * Complex.I * (-Real.pi : ℝ)) := by
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨(n : ℤ) - m, ?_⟩
    push_cast
    ring
  rw [he, sub_self, zero_div]

lemma polarCoord_symm_exp (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) := by
  rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  simp only [Complex.ofReal_cos, Complex.ofReal_sin]

lemma polar_monomial (p : ℝ × ℝ) (n m : ℕ) :
    Complex.polarCoord.symm p ^ n * star (Complex.polarCoord.symm p) ^ m =
      (p.1 : ℂ) ^ (n + m) * Complex.exp (((n : ℂ) - m) * Complex.I * p.2) := by
  rw [polarCoord_symm_exp]
  simp only [map_mul, Complex.star_def, Complex.conj_ofReal,
    ← Complex.exp_conj, map_mul, Complex.conj_I, mul_neg, mul_pow]
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  calc
    _ = (p.1 : ℂ) ^ (n + m) *
        (Complex.exp ((n : ℂ) * ((p.2 : ℂ) * Complex.I)) *
         Complex.exp ((m : ℂ) * -((p.2 : ℂ) * Complex.I))) := by rw [pow_add]; ring
    _ = _ := by rw [← Complex.exp_add]; congr 2; ring

lemma offDiagonal_integral (a : ℝ) (n m : ℕ) (hnm : n ≠ m) :
    (∫ z : ℂ, (Real.exp (-a * ‖z‖ ^ 2) : ℂ) * z ^ n * star z ^ m) = 0 := by
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  have he (p : ℝ × ℝ) :
      p.1 • ((Real.exp (-a * ‖Complex.polarCoord.symm p‖ ^ 2) : ℂ) *
        Complex.polarCoord.symm p ^ n * star (Complex.polarCoord.symm p) ^ m) =
      ((p.1 : ℂ) * Real.exp (-a * |p.1| ^ 2) * (p.1 : ℂ) ^ (n + m)) *
        Complex.exp (((n : ℂ) - m) * Complex.I * p.2) := by
    rw [Complex.norm_polarCoord_symm, mul_assoc, polar_monomial]
    simp only [Complex.real_smul]
    ring
  simp_rw [he]
  rw [Measure.volume_eq_prod]
  rw [setIntegral_prod_mul
    (fun r : ℝ => (r : ℂ) * Real.exp (-a * |r| ^ 2) * (r : ℂ) ^ (n + m))
    (fun θ : ℝ => Complex.exp (((n : ℂ) - m) * Complex.I * θ))]
  rw [angular_integral_zero n m hnm, mul_zero]

lemma radial_integral (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (∫ z : ℂ, ‖z‖ ^ (2 * n) * Real.exp (-a * ‖z‖ ^ 2)) =
      Real.pi * (n.factorial : ℝ) / a ^ (n + 1) := by
  have h := Complex.integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := (2 * n : ℕ)) (b := a) (by norm_num) (by have hn : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) ha
  have he : -(((2 * n : ℕ) : ℝ) + 2) / 2 = -((n + 1 : ℕ) : ℝ) := by push_cast; ring
  have he' : (((2 * n : ℕ) : ℝ) + 2) / 2 = (n : ℝ) + 1 := by push_cast; ring
  simp only [Real.rpow_natCast, Real.rpow_two, he, he', Real.Gamma_nat_eq_factorial] at h
  rw [Real.rpow_neg ha.le, Real.rpow_natCast] at h
  convert h using 1
  ring

lemma diagonal_integral (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (∫ z : ℂ, (Real.exp (-a * ‖z‖ ^ 2) : ℂ) * z ^ n * star z ^ n) =
      (Real.pi * (n.factorial : ℝ) / a ^ (n + 1) : ℝ) := by
  have he (z : ℂ) : (Real.exp (-a * ‖z‖ ^ 2) : ℂ) * z ^ n * star z ^ n =
      ((‖z‖ ^ (2 * n) * Real.exp (-a * ‖z‖ ^ 2) : ℝ) : ℂ) := by
    rw [mul_assoc, ← mul_pow, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rw [pow_mul]
    ring
  simp_rw [he]
  rw [integral_complex_ofReal, radial_integral a ha n]

end
end Cloning.ComplexGaussianMoments
