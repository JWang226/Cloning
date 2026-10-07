import Cloning.PCTProjectorPurityGaussianEnergy
import Cloning.WeylGaussianThermal

/-! Exact real-linear and real-quadratic exponential moments of one actual
circular complex Gaussian coordinate. -/
noncomputable section
open scoped Topology BigOperators
open MeasureTheory
namespace Cloning.PCTProjectorPurity
open Cloning.CoherentGaussianMixture
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 120000

lemma integral_complex_real_linear {q : ℝ} (hq : 0<q) (t : ℝ) :
    (∫z : ℂ,Real.exp (-q*‖z‖^2+t*z.re))=
      (Real.pi/q)*Real.exp (t^2/(4*q)) := by
  have hh := Cloning.ComplexCoherent.integral_complex_gaussian_linear_scaled hq
    ((t/2 : ℝ) : ℂ) ((t/2 : ℝ) : ℂ)
  have he (z : ℂ) :
      -(q : ℂ)*((‖z‖^2 : ℝ) : ℂ)+((t/2 : ℝ) : ℂ)*z+
        ((t/2 : ℝ) : ℂ)*(starRingEnd ℂ) z=((-q*‖z‖^2+t*z.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  simp_rw [he,←Complex.ofReal_exp,integral_complex_ofReal] at hh
  have ht : ((t/2 : ℝ) : ℂ)*((t/2 : ℝ) : ℂ)/(q : ℂ)=((t^2/(4*q) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [ht,←Complex.ofReal_exp,←Complex.ofReal_mul] at hh
  exact Complex.ofReal_injective hh

theorem integral_exp_re {δ : ℝ} (hδ : 0<δ) (t : ℝ) :
    (∫z : ℂ,Real.exp (t*z.re) ∂gaussianMeasure δ)=Real.exp (δ*t^2/4) := by
  rw [integral_gaussianMeasure_real δ hδ]
  have he (z : ℂ) : gaussianDensity δ z*Real.exp (t*z.re)=
      (Real.pi*δ)⁻¹*Real.exp (-δ⁻¹*‖z‖^2+t*z.re) := by
    unfold gaussianDensity
    rw [div_eq_mul_inv,mul_right_comm,←Real.exp_add,mul_comm]
    congr 1
    congr 1
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_complex_real_linear (inv_pos.mpr hδ)]
  have hc : (Real.pi*δ)⁻¹*(Real.pi/δ⁻¹)=1 := by
    rw [div_inv_eq_mul,inv_mul_cancel₀ (mul_ne_zero Real.pi_ne_zero hδ.ne')]
  have ht : t^2/(4*δ⁻¹)=δ*t^2/4 := by field_simp <;> ring
  rw [←mul_assoc,hc,one_mul,ht]

lemma integral_complex_anisotropic (a b : ℝ) :
    (∫z : ℂ,Real.exp (-a*z.re^2-b*z.im^2))=
      Real.sqrt (Real.pi/a)*Real.sqrt (Real.pi/b) := by
  rw [←Complex.volume_preserving_equiv_pi.symm.integral_comp
    Complex.measurableEquivPi.symm.measurableEmbedding]
  have he (x : Fin 2 → ℝ) :
      Real.exp (-a*(Complex.measurableEquivPi.symm x).re^2-
        b*(Complex.measurableEquivPi.symm x).im^2)=
      ∏i : Fin 2,Real.exp (-(![a,b] i)*x i^2) := by
    simp only [Complex.measurableEquivPi_symm_apply,Complex.add_re,Complex.ofReal_re,
      Complex.mul_re,Complex.I_re,Complex.ofReal_im,Complex.I_im,zero_mul,mul_zero,
      sub_zero,add_zero,Complex.add_im,Complex.mul_im,one_mul,zero_add,
      Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,←Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_fintype_prod_volume_eq_prod (fun i : Fin 2 => fun x : ℝ => Real.exp (-(![a,b] i)*x^2))]
  simp only [integral_gaussian,Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]

theorem integral_exp_re_sq {δ : ℝ} (hδ : 0<δ) (t : ℝ) (ht : t*δ<1) :
    (∫z : ℂ,Real.exp (t*z.re^2) ∂gaussianMeasure δ)=(Real.sqrt (1-t*δ))⁻¹ := by
  have hq : 0<δ⁻¹-t := by
    have := (lt_div_iff₀ hδ).2 ht
    simpa only [one_div] using sub_pos.mpr this
  rw [integral_gaussianMeasure_real δ hδ]
  have he (z : ℂ) : gaussianDensity δ z*Real.exp (t*z.re^2)=
      (Real.pi*δ)⁻¹*Real.exp (-(δ⁻¹-t)*z.re^2-δ⁻¹*z.im^2) := by
    unfold gaussianDensity
    rw [div_eq_mul_inv,mul_right_comm,←Real.exp_add,mul_comm]
    congr 1
    congr 1
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_complex_anisotropic,
    ←Real.sqrt_mul (div_nonneg Real.pi_pos.le hq.le)]
  have hrad : (Real.pi/(δ⁻¹-t))*(Real.pi/δ⁻¹)=
      (Real.pi*δ)^2*(1-t*δ)⁻¹ := by
    field_simp
    <;> ring
  rw [hrad,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (mul_nonneg Real.pi_pos.le hδ.le),
    Real.sqrt_inv,←mul_assoc,inv_mul_cancel₀ (mul_ne_zero Real.pi_ne_zero hδ.ne'),one_mul]

end Cloning.PCTProjectorPurity
