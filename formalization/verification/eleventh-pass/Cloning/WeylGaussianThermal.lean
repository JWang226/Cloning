import Cloning.WeylIrreducibleGaussian
import Cloning.WeylIrreducible
import Cloning.HeisenbergDualContinuity
import Cloning.CoherentGaussianMixture

/-! Exact Gaussian Fourier identities for the actual thermal states and Weyl
operators. These are the operator-to-scalar bridge for a direct Gaussian moment
bound based on quantum positive-definiteness. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Topology BigOperators ComplexOrder
namespace Cloning.ComplexCoherent
open Cloning.InfiniteTraceClass Cloning.CoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem integral_complex_gaussian_linear_scaled {t : ℝ} (ht : 0 < t) (u v : ℂ) :
    (∫ a : ℂ, Complex.exp (-(t : ℂ) * ((‖a‖ ^ 2 : ℝ) : ℂ) +
      u * a + v * starRingEnd ℂ a)) =
      ((Real.pi / t : ℝ) : ℂ) * Complex.exp (u * v / (t : ℂ)) := by
  rw [← (Complex.volume_preserving_equiv_pi.symm).integral_comp
    Complex.measurableEquivPi.symm.measurableEmbedding]
  have he (x : Fin 2 → ℝ) :
      -(t : ℂ) * ((‖Complex.measurableEquivPi.symm x‖ ^ 2 : ℝ) : ℂ) +
        u * Complex.measurableEquivPi.symm x + v * starRingEnd ℂ (Complex.measurableEquivPi.symm x) =
      -(t : ℂ) * (∑ i : Fin 2, (x i : ℂ) ^ 2) +
        ∑ i : Fin 2, (![u + v, Complex.I * (u - v)] i) * x i := by
    rw [norm_sq_cast', Complex.measurableEquivPi_symm_apply]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
    simp [Complex.I_sq]
    ring
  simp_rw [he]
  rw [GaussianFourier.integral_cexp_neg_mul_sum_add (by simpa using ht : 0 < (t : ℂ).re)]
  simp only [Fintype.card_fin, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Complex.ofReal_div]
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hsq : ((u + v) ^ 2 + (Complex.I * (u - v)) ^ 2) / (4 * (t : ℂ)) =
      u * v / (t : ℂ) := by
    rw [mul_pow, Complex.I_sq]
    field_simp
    <;> ring
  rw [hsq]
  congr 1
  norm_num

theorem integrable_complex_gaussian_linear_scaled {t : ℝ} (ht : 0 < t) (u v : ℂ) :
    Integrable (fun a : ℂ => Complex.exp (-(t : ℂ) * ((‖a‖ ^ 2 : ℝ) : ℂ) +
      u * a + v * starRingEnd ℂ a)) := by
  rw [← (Complex.volume_preserving_equiv_pi.symm).integrable_comp_emb
    Complex.measurableEquivPi.symm.measurableEmbedding]
  have he (x : Fin 2 → ℝ) :
      -(t : ℂ) * ((‖Complex.measurableEquivPi.symm x‖ ^ 2 : ℝ) : ℂ) +
        u * Complex.measurableEquivPi.symm x + v * starRingEnd ℂ (Complex.measurableEquivPi.symm x) =
      -(t : ℂ) * (∑ i : Fin 2, (x i : ℂ) ^ 2) +
        ∑ i : Fin 2, (![u + v, Complex.I * (u - v)] i) * x i := by
    rw [norm_sq_cast', Complex.measurableEquivPi_symm_apply]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
    simp [Complex.I_sq]
    ring
  change Integrable (fun x : Fin 2 → ℝ => Complex.exp
    (-(t : ℂ) * ((‖Complex.measurableEquivPi.symm x‖ ^ 2 : ℝ) : ℂ) +
      u * Complex.measurableEquivPi.symm x + v * starRingEnd ℂ (Complex.measurableEquivPi.symm x)))
  simp_rw [he]
  exact GaussianFourier.integrable_cexp_neg_mul_sum_add
    (by simpa using ht : 0 < (t : ℂ).re) (![u + v, Complex.I * (u - v)])

theorem coherentProjector_characteristic (z a : ℂ) :
    tracePairing (coherentProjector z) (displacement a) =
      Complex.exp (-((‖a‖ ^ 2 / 2 : ℝ) : ℂ) +
        a * starRingEnd ℂ z - starRingEnd ℂ a * z) := by
  change tracePairing (rankOneOperator (coherentVector z) (coherentVector z)) (displacement a) = _
  rw [tracePairing_rankOneOperator, displacement_coherentVector, inner_smul_right,
    inner_coherentVector]
  unfold displacementPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  simp only [norm_sq_cast, map_add]
  ring

/-- Fourier transform of the actual circular Gaussian amplitude law. -/
theorem integral_gaussianDensity_phase {s : ℝ} (hs : 0 < s) (a : ℂ) :
    (∫ z : ℂ, (gaussianDensity s z : ℂ) *
      Complex.exp (a * starRingEnd ℂ z - starRingEnd ℂ a * z)) =
        Complex.exp (-((s * ‖a‖ ^ 2 : ℝ) : ℂ)) := by
  have he (z : ℂ) : (gaussianDensity s z : ℂ) *
      Complex.exp (a * starRingEnd ℂ z - starRingEnd ℂ a * z) =
      (1 / ((Real.pi * s : ℝ) : ℂ)) *
        Complex.exp (-((1 / s : ℝ) : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) +
          (-starRingEnd ℂ a) * z + a * starRingEnd ℂ z) := by
    have hexp :
        Complex.exp (-((1 / s : ℝ) : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) +
          (-starRingEnd ℂ a) * z + a * starRingEnd ℂ z) =
        Complex.exp (((-‖z‖ ^ 2 / s : ℝ) : ℂ)) *
          Complex.exp (a * starRingEnd ℂ z - starRingEnd ℂ a * z) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    simp only [gaussianDensity, Complex.ofReal_div, Complex.ofReal_exp,
      Complex.ofReal_mul]
    ring

  simp_rw [he]
  rw [integral_const_mul, integral_complex_gaussian_linear_scaled (one_div_pos.mpr hs)]
  have hcoeff : (1 / ((Real.pi * s : ℝ) : ℂ)) * ((Real.pi / (1 / s) : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp
  rw [← mul_assoc, hcoeff, one_mul]
  congr 1
  push_cast
  rw [norm_sq_cast]
  field_simp
  <;> ring

/-- The characteristic function of the genuine one-mode thermal operator,
with the mean occupation parameter `s`. -/
theorem gaussianMixture_characteristic {s : ℝ} (hs : 0 < s) (a : ℂ) :
    tracePairing (gaussianMixture s) (displacement a) =
      Complex.exp (-(((s + 1 / 2) * ‖a‖ ^ 2 : ℝ) : ℂ)) := by
  have h := (tracePairingCLM.flip (displacement a)).integral_comp_comm
    (integrable_weighted_projector hs)
  change (∫ z : ℂ, tracePairing (gaussianDensity s z • coherentProjector z) (displacement a)) =
    tracePairing (gaussianMixture s) (displacement a) at h
  rw [← h]
  have he (z : ℂ) : tracePairing (gaussianDensity s z • coherentProjector z) (displacement a) =
      Complex.exp (-((‖a‖ ^ 2 / 2 : ℝ) : ℂ)) *
        ((gaussianDensity s z : ℂ) *
          Complex.exp (a * starRingEnd ℂ z - starRingEnd ℂ a * z)) := by
    rw [show gaussianDensity s z • coherentProjector z =
      (gaussianDensity s z : ℂ) • coherentProjector z by rw [Complex.coe_smul]]
    change tracePairingCLM ((gaussianDensity s z : ℂ) • coherentProjector z) (displacement a) = _
    rw [map_smul, ContinuousLinearMap.smul_apply, tracePairingCLM_apply,
      coherentProjector_characteristic]
    simp only [smul_eq_mul]
    rw [show -((‖a‖ ^ 2 / 2 : ℝ) : ℂ) + a * starRingEnd ℂ z - starRingEnd ℂ a * z =
      -((‖a‖ ^ 2 / 2 : ℝ) : ℂ) + (a * starRingEnd ℂ z - starRingEnd ℂ a * z) by ring,
      Complex.exp_add]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_gaussianDensity_phase hs, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integral_gaussianMeasure_phase {s : ℝ} (hs : 0 < s) (a : ℂ) :
    (∫ z : ℂ, Complex.exp (a * starRingEnd ℂ z - starRingEnd ℂ a * z)
      ∂gaussianMeasure s) = Complex.exp (-((s * ‖a‖ ^ 2 : ℝ) : ℂ)) := by
  rw [gaussianMeasure, integral_withDensity_eq_integral_toReal_smul
    ((continuous_gaussianDensity s).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (gaussianDensity_pos hs _).le, Complex.real_smul]
  exact integral_gaussianDensity_phase hs a

theorem thermal_characteristic {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (a : ℂ) :
    tracePairing (vectorMixture numberBasis (Cloning.Thermal.geometric q)) (displacement a) =
      Complex.exp (-((((1 + q) / (2 * (1 - q))) * ‖a‖ ^ 2 : ℝ) : ℂ)) := by
  have hs : 0 < q / (1 - q) := div_pos hq0 (sub_pos.mpr hq1)
  have hden : 1 - q ≠ 0 := (sub_pos.mpr hq1).ne'
  have hq : (q / (1 - q)) / (1 + q / (1 - q)) = q := by
    field_simp [hden]
    <;> ring
  have hm := gaussianMixture_eq_thermal hs
  rw [hq] at hm
  rw [← hm, gaussianMixture_characteristic hs]
  have hc : q / (1 - q) + 1 / 2 = (1 + q) / (2 * (1 - q)) := by
    field_simp
    <;> ring
  rw [hc]

end Cloning.ComplexCoherent
