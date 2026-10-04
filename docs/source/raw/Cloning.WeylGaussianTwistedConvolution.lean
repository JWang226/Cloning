import Cloning.WeylGaussianThermal
import Cloning.WeylQuantumPositive
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Group.Prod

/-! Exact twisted convolution of anisotropic Gaussian phase-space weights for
the concrete Weyl cocycle. This is the scalar analytic step in the direct
least-noise bound from quantum positivity. -/
noncomputable section
open scoped ComplexOrder BigOperators Topology
open Filter MeasureTheory
namespace Cloning.ComplexCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- One-mode twisted Gaussian convolution, with exactly the physical Weyl
cocycle ratio at gain `r`. -/
theorem integral_gaussian_twisted_single {t : ℝ} (ht : 0 < t) (r : ℝ) (z : ℂ) :
    (∫ a : ℂ, (Real.exp (-t * ‖a‖ ^ 2) : ℂ) *
      (Real.exp (-t * ‖a + z‖ ^ 2) : ℂ) *
      (displacementPhase (-a) (a + z) / displacementPhase (-(r • a)) (r • (a + z)))) =
      ((Real.pi / (2 * t) : ℝ) : ℂ) *
        (Real.exp (-(t / 2 + (r ^ 2 - 1) ^ 2 / (8 * t)) * ‖z‖ ^ 2) : ℂ) := by
  let u : ℂ := (((r : ℂ) ^ 2 - 1) / 2 - (t : ℂ)) * starRingEnd ℂ z
  let v : ℂ := (-((r : ℂ) ^ 2 - 1) / 2 - (t : ℂ)) * z
  have he (a : ℂ) : (Real.exp (-t * ‖a‖ ^ 2) : ℂ) *
      (Real.exp (-t * ‖a + z‖ ^ 2) : ℂ) *
      (displacementPhase (-a) (a + z) / displacementPhase (-(r • a)) (r • (a + z))) =
      Complex.exp (-(t : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ)) *
        Complex.exp (-((2 * t : ℝ) : ℂ) * ((‖a‖ ^ 2 : ℝ) : ℂ) +
          u * a + v * starRingEnd ℂ a) := by
    simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg,
      displacementPhase, ← Complex.exp_sub, ← Complex.exp_add]
    congr 1
    simp only [norm_sq_cast', map_add, map_neg, Complex.real_smul, map_mul,
      Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_ofNat, u, v]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_complex_gaussian_linear_scaled (by positivity : 0 < 2 * t)]
  rw [mul_left_comm]
  congr 1
  rw [← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  simp only [u, v, norm_sq_cast', Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  simp only [norm_sq_cast]
  field_simp
  ring

end Cloning.ComplexCoherent

namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {d : ℕ}

/-- The unnormalized anisotropic Gaussian test weight. -/
def gaussianWeight (t : Fin d → ℝ) (a : Fin d → ℂ) : ℝ :=
  ∏ i, Real.exp (-t i * ‖a i‖ ^ 2)

lemma gaussianWeight_nonneg (t : Fin d → ℝ) (a : Fin d → ℂ) : 0 ≤ gaussianWeight t a :=
  Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le)

lemma continuous_gaussianWeight (t : Fin d → ℝ) : Continuous (gaussianWeight t) := by
  unfold gaussianWeight
  fun_prop

lemma integral_gaussian_single {t : ℝ} (ht : 0 < t) :
    (∫ a : ℂ, Real.exp (-t * ‖a‖ ^ 2)) = Real.pi / t := by
  simpa using Cloning.ComplexGaussianMoments.radial_integral t ht 0

lemma integrable_gaussian_single {t : ℝ} (ht : 0 < t) :
    Integrable (fun a : ℂ => Real.exp (-t * ‖a‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_gaussian_single ht]
  exact (div_pos Real.pi_pos ht).ne'

lemma integrable_gaussianWeight {t : Fin d → ℝ} (ht : ∀ i, 0 < t i) :
    Integrable (gaussianWeight t) :=
  Integrable.fintype_prod (fun i => integrable_gaussian_single (ht i))

lemma integral_gaussianWeight {t : Fin d → ℝ} (ht : ∀ i, 0 < t i) :
    (∫ a, gaussianWeight t a) = ∏ i, Real.pi / t i := by
  unfold gaussianWeight
  rw [integral_fintype_prod_volume_eq_prod (fun i (a : ℂ) => Real.exp (-t i * ‖a‖ ^ 2))]
  simp only [integral_gaussian_single (ht _)]

/-- Product form of the exact twisted Gaussian convolution; no isotropy
assumption is made on the widths. -/
theorem integral_gaussian_twisted_product {t : Fin d → ℝ} (ht : ∀ i, 0 < t i)
    (r : ℝ) (z : Fin d → ℂ) :
    (∫ a, (gaussianWeight t a : ℂ) * (gaussianWeight t (a + z) : ℂ) *
      (displacementPhase (-a) (a + z) / displacementPhase (-(r • a)) (r • (a + z)))) =
      ((∏ i, Real.pi / (2 * t i) : ℝ) : ℂ) *
        (gaussianWeight (fun i => t i / 2 + (r ^ 2 - 1) ^ 2 / (8 * t i)) z : ℂ) := by
  have he (a : Fin d → ℂ) :
      (gaussianWeight t a : ℂ) * (gaussianWeight t (a + z) : ℂ) *
        (displacementPhase (-a) (a + z) / displacementPhase (-(r • a)) (r • (a + z))) =
      ∏ i, ((Real.exp (-t i * ‖a i‖ ^ 2) : ℂ) *
        (Real.exp (-t i * ‖a i + z i‖ ^ 2) : ℂ) *
        (Cloning.ComplexCoherent.displacementPhase (-a i) (a i + z i) /
          Cloning.ComplexCoherent.displacementPhase (-(r • a i)) (r • (a i + z i)))) := by
    simp only [gaussianWeight, displacementPhase, Complex.ofReal_prod, Pi.add_apply,
      Pi.neg_apply, Pi.smul_apply, Finset.prod_mul_distrib, Finset.prod_div_distrib]
  simp_rw [he]
  rw [integral_fintype_prod_volume_eq_prod (fun i (a : ℂ) =>
    (Real.exp (-t i * ‖a‖ ^ 2) : ℂ) * (Real.exp (-t i * ‖a + z i‖ ^ 2) : ℂ) *
      (Cloning.ComplexCoherent.displacementPhase (-a) (a + z i) /
        Cloning.ComplexCoherent.displacementPhase (-(r • a)) (r • (a + z i))))]
  simp only [Cloning.ComplexCoherent.integral_gaussian_twisted_single (ht _),
    Finset.prod_mul_distrib, ← Complex.ofReal_prod, gaussianWeight]

lemma quantumPositiveKernel_norm (f : (Fin d → ℂ) → ℂ) (r : ℝ)
    (a b : Fin d → ℂ) : ‖quantumPositiveKernel f r a b‖ = ‖f (b - a)‖ := by
  simp only [quantumPositiveKernel, norm_mul, norm_div, displacementPhase_norm, div_self one_ne_zero,
    one_mul]

lemma continuous_quantumPositiveKernel {f : (Fin d → ℂ) → ℂ} (hf : Continuous f) (r : ℝ) :
    Continuous (fun p : (Fin d → ℂ) × (Fin d → ℂ) => quantumPositiveKernel f r p.1 p.2) := by
  unfold quantumPositiveKernel
  apply Continuous.mul
  · apply Continuous.div
    · unfold displacementPhase Cloning.ComplexCoherent.displacementPhase
      fun_prop
    · unfold displacementPhase Cloning.ComplexCoherent.displacementPhase
      fun_prop
    · intro p
      exact displacementPhase_ne_zero _ _
  · exact hf.comp (continuous_snd.sub continuous_fst)

/-- Absolute integrability of the kernel quadratic form follows solely from
the Gaussian weights and the multiplier bound. -/
lemma integrable_gaussian_kernel {t : Fin d → ℝ} (ht : ∀ i, 0 < t i)
    {f : (Fin d → ℂ) → ℂ} (hf : Continuous f) (hfbound : ∀ a, ‖f a‖ ≤ 1) (r : ℝ) :
    Integrable (fun p : (Fin d → ℂ) × (Fin d → ℂ) =>
      (gaussianWeight t p.1 : ℂ) * (gaussianWeight t p.2 : ℂ) *
        quantumPositiveKernel f r p.1 p.2) (volume.prod volume) := by
  apply ((integrable_gaussianWeight ht).mul_prod (integrable_gaussianWeight ht)).mono'
  · exact (((Complex.continuous_ofReal.comp (continuous_gaussianWeight t |>.comp continuous_fst)).mul
      (Complex.continuous_ofReal.comp (continuous_gaussianWeight t |>.comp continuous_snd))).mul
        (continuous_quantumPositiveKernel hf r)).aestronglyMeasurable
  · exact Eventually.of_forall fun p => by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (gaussianWeight_nonneg _ _),
        Real.norm_of_nonneg (gaussianWeight_nonneg _ _), quantumPositiveKernel_norm]
      exact mul_le_of_le_one_right (mul_nonneg (gaussianWeight_nonneg _ _) (gaussianWeight_nonneg _ _))
        (hfbound _)

/-- The exact double-integral identity feeding the quantum-positive Gaussian
recursion. The shear and Fubini steps are justified in the full Bochner
integral by a proved integrable dominating Gaussian. -/
theorem integral_integral_gaussian_quantumKernel {t : Fin d → ℝ} (ht : ∀ i, 0 < t i)
    {f : (Fin d → ℂ) → ℂ} (hf : Continuous f) (hfbound : ∀ a, ‖f a‖ ≤ 1) (r : ℝ) :
    (∫ a, ∫ b, (gaussianWeight t a : ℂ) * (gaussianWeight t b : ℂ) *
      quantumPositiveKernel f r a b) =
      ((∏ i, Real.pi / (2 * t i) : ℝ) : ℂ) *
        ∫ z, (gaussianWeight (fun i => t i / 2 + (r ^ 2 - 1) ^ 2 / (8 * t i)) z : ℂ) * f z := by
  let K := fun a b => (gaussianWeight t a : ℂ) * (gaussianWeight t b : ℂ) *
    quantumPositiveKernel f r a b
  have hi := (measurePreserving_prod_add volume volume).integrable_comp_of_integrable
    (integrable_gaussian_kernel ht hf hfbound r)
  have hshift : (∫ a, ∫ b, K a b) = ∫ a, ∫ z, K a (a + z) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun a => (integral_add_left_eq_self (K a) a).symm
  change (∫ a, ∫ b, K a b) = _
  have hi' : Integrable (Function.uncurry (fun a z => K a (a + z))) (volume.prod volume) := hi
  rw [hshift, integral_integral_swap (f := fun a z => K a (a + z)) hi']
  have he (a z : Fin d → ℂ) : K a (a + z) =
      ((gaussianWeight t a : ℂ) * (gaussianWeight t (a + z) : ℂ) *
        (displacementPhase (-a) (a + z) / displacementPhase (-(r • a)) (r • (a + z)))) * f z := by
    simp only [K, quantumPositiveKernel, add_sub_cancel_left, mul_assoc]
  simp_rw [he, integral_mul_const, integral_gaussian_twisted_product ht r]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => mul_assoc _ _ _

end Cloning.MultimodeCoherent
