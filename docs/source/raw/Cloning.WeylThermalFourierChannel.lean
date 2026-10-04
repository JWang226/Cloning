import Cloning.WeylThermalFourierWitness
import Cloning.WeylThermalCharacteristic
import Cloning.WeylGaussianTwistedConvolution

/-! The thermal moment of a covariant channel is exactly the Gaussian
functional of its constructed Weyl multiplier. Both the input and the thermal
test operator are literal product-geometric operators on Fock space. -/

noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {d : ℕ}

/-- Fourier width of a geometric thermal state. -/
def geometricFourierWidth (q : ℝ) : ℝ := (1 + q) / (2 * (1 - q))

lemma geometricFourierWidth_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < geometricFourierWidth q := by
  unfold geometricFourierWidth
  exact div_pos (by linarith) (mul_pos (by norm_num) (sub_pos.mpr hq1))

lemma geometricFourierWidth_gt_half {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    1 / 2 < geometricFourierWidth q := by
  unfold geometricFourierWidth
  apply (lt_div_iff₀ (mul_pos (by norm_num) (sub_pos.mpr hq1))).mpr
  linarith

lemma norm_real_smul_sq (r : ℝ) (a : ℂ) : ‖r • a‖ ^ 2 = r ^ 2 * ‖a‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- Every thermal input and thermal test give Gaussian widths in the
physical domain of the sharp quantum-positive recurrence. -/
lemma thermal_moment_width_ge_noise (r : ℝ) {q y : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    (r ^ 2 - 1) / 2 ≤ geometricFourierWidth y + r ^ 2 * geometricFourierWidth q := by
  have hq := geometricFourierWidth_gt_half hq0 hq1
  have hy := geometricFourierWidth_gt_half hy0 hy1
  have hm := mul_le_mul_of_nonneg_left hq.le (sq_nonneg r)
  nlinarith

/-- The output characteristic of an actual covariant trace-class map on a
literal thermal input, with the multiplier derived from the normal dual. -/
theorem covariant_thermal_output_characteristic
    (Φ : TraceClass (Fock d) →L[ℂ] TraceClass (Fock d)) (r : ℝ)
    (hΦ : ∀ a T, Φ (displacementTraceMap a T) = displacementTraceMap (r • a) (Φ T))
    {q : Fin d → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (a : Fin d → ℂ) :
    tracePairing (Φ (vectorMixture (numberBasis d) (Cloning.ThermalWitness.productGeometric q)))
      (displacement a) =
      weylMultiplier (heisenbergDual Φ) r a *
        ∏ i, Complex.exp (-((geometricFourierWidth (q i) * r ^ 2 * ‖a i‖ ^ 2 : ℝ) : ℂ)) := by
  rw [← heisenbergDual_pairing, traceClass_covariant_weyl_multiplier Φ r hΦ,
    map_smul, smul_eq_mul, productThermal_characteristic hq0 hq1]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [Pi.smul_apply, norm_real_smul_sq, geometricFourierWidth, mul_assoc]

lemma thermal_gaussian_weights_combine (q y : Fin d → ℝ) (r : ℝ) (a : Fin d → ℂ) :
    (∏ i, (Real.exp (-geometricFourierWidth (y i) * ‖a i‖ ^ 2) / Real.pi : ℂ)) *
      (∏ i, Complex.exp (-((geometricFourierWidth (q i) * r ^ 2 * ‖a i‖ ^ 2 : ℝ) : ℂ))) =
      ((Real.pi ^ d : ℝ) : ℂ)⁻¹ *
        (gaussianWeight (fun i => geometricFourierWidth (y i) +
          r ^ 2 * geometricFourierWidth (q i)) a : ℂ) := by
  rw [← Finset.prod_mul_distrib]
  have heq (i : Fin d) :
      (Real.exp (-geometricFourierWidth (y i) * ‖a i‖ ^ 2) / Real.pi : ℂ) *
        Complex.exp (-((geometricFourierWidth (q i) * r ^ 2 * ‖a i‖ ^ 2 : ℝ) : ℂ)) =
      ((Real.pi : ℂ)⁻¹) *
        (Real.exp (-(geometricFourierWidth (y i) + r ^ 2 * geometricFourierWidth (q i)) *
          ‖a i‖ ^ 2) : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, div_mul_eq_mul_div,
      ← Complex.ofReal_mul, ← Real.exp_add]
    have harg : -geometricFourierWidth (y i) * ‖a i‖ ^ 2 +
        -(geometricFourierWidth (q i) * r ^ 2 * ‖a i‖ ^ 2) =
        -(geometricFourierWidth (y i) + r ^ 2 * geometricFourierWidth (q i)) * ‖a i‖ ^ 2 := by ring
    rw [harg, div_eq_mul_inv, mul_comm]
  simp only [heq, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, gaussianWeight, Complex.ofReal_prod,
    Complex.ofReal_pow, inv_pow]

/-- Exact Gaussian multiplier expression for an output thermal moment.
No Gaussianity or independence of the channel's noise is assumed. -/
theorem covariant_productThermal_moment_fourier
    (Φ : TraceClass (Fock d) →L[ℂ] TraceClass (Fock d)) (r : ℝ)
    (hΦ : ∀ a T, Φ (displacementTraceMap a T) = displacementTraceMap (r • a) (Φ T))
    {q y : Fin d → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (hy0 : ∀ i, 0 < y i) (hy1 : ∀ i, y i < 1) :
    tracePairing (Φ (vectorMixture (numberBasis d) (Cloning.ThermalWitness.productGeometric q)))
      (vectorMixture (numberBasis d) (Cloning.ThermalWitness.productGeometric y)).1 =
      ((Real.pi ^ d : ℝ) : ℂ)⁻¹ * ∫ a : Fin d → ℂ,
        (gaussianWeight (fun i => geometricFourierWidth (y i) +
          r ^ 2 * geometricFourierWidth (q i)) a : ℂ) * weylMultiplier (heisenbergDual Φ) r a := by
  rw [show Cloning.ThermalWitness.productGeometric y =
    (fun k => ∏ i, Cloning.Thermal.geometric (y i) (k i)) from rfl,
    tracePairing_geometricThermal_fourier hy0 hy1]
  simp_rw [covariant_thermal_output_characteristic Φ r hΦ hq0 hq1]
  rw [← integral_const_mul]
  congr 1
  funext a
  change (∏ i, (Real.exp (-geometricFourierWidth (y i) * ‖a i‖ ^ 2) / Real.pi : ℂ)) *
      (weylMultiplier (heisenbergDual Φ) r a * _) = _
  rw [mul_left_comm _ (weylMultiplier (heisenbergDual Φ) r a),
    thermal_gaussian_weights_combine]
  ring

/-- Exact overlap of two literal product-geometric thermal states. -/
theorem productThermal_overlap_fourier {x y : Fin d → ℝ}
    (hx0 : ∀ i, 0 < x i) (hx1 : ∀ i, x i < 1)
    (hy0 : ∀ i, 0 < y i) (hy1 : ∀ i, y i < 1) :
    tracePairing (vectorMixture (numberBasis d) (Cloning.ThermalWitness.productGeometric x))
      (vectorMixture (numberBasis d) (Cloning.ThermalWitness.productGeometric y)).1 =
      ((Real.pi ^ d : ℝ) : ℂ)⁻¹ *
        ((∏ i, Real.pi / (geometricFourierWidth (y i) +
          geometricFourierWidth (x i)) : ℝ) : ℂ) := by
  rw [show Cloning.ThermalWitness.productGeometric y =
    (fun k => ∏ i, Cloning.Thermal.geometric (y i) (k i)) from rfl,
    tracePairing_geometricThermal_fourier hy0 hy1]
  simp_rw [productThermal_characteristic hx0 hx1]
  have heq (a : Fin d → ℂ) :
      (∏ i, (Real.exp (-geometricFourierWidth (y i) * ‖a i‖ ^ 2) / Real.pi : ℂ)) *
        (∏ i, Complex.exp (-((geometricFourierWidth (x i) * ‖a i‖ ^ 2 : ℝ) : ℂ))) =
      ((Real.pi ^ d : ℝ) : ℂ)⁻¹ *
        (gaussianWeight (fun i => geometricFourierWidth (y i) +
          geometricFourierWidth (x i)) a : ℂ) := by
    simpa only [one_pow, mul_one, one_mul] using thermal_gaussian_weights_combine x y 1 a
  change (∫ a : Fin d → ℂ,
    (∏ i, (Real.exp (-geometricFourierWidth (y i) * ‖a i‖ ^ 2) / Real.pi : ℂ)) *
      (∏ i, Complex.exp (-((geometricFourierWidth (x i) * ‖a i‖ ^ 2 : ℝ) : ℂ)))) = _
  simp_rw [heq]
  rw [integral_const_mul, integral_complex_ofReal,
    integral_gaussianWeight (fun i => add_pos (geometricFourierWidth_pos (hy0 i) (hy1 i))
      (geometricFourierWidth_pos (hx0 i) (hx1 i)))]

end Cloning.MultimodeCoherent
