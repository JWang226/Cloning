import Cloning.WeylGaussianThermal
import Cloning.MultimodeCoherentGaussianMixture
import Cloning.ThermalWitness

/-! Characteristic functions of the actual finite-mode thermal operators,
derived from their coherent Gaussian mixture identity. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Topology BigOperators ComplexOrder
open Cloning.InfiniteTraceClass

namespace Cloning.ComplexCoherent
open Cloning.CoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false

theorem integral_coherent_characteristic_gaussian {s : ℝ} (hs : 0 < s) (a : ℂ) :
    (∫ z : ℂ, tracePairing (coherentProjector z) (displacement a) ∂gaussianMeasure s) =
      Complex.exp (-(((s + 1 / 2) * ‖a‖ ^ 2 : ℝ) : ℂ)) := by
  simp_rw [coherentProjector_characteristic]
  have he (z : ℂ) : -((‖a‖ ^ 2 / 2 : ℝ) : ℂ) +
      a * starRingEnd ℂ z - starRingEnd ℂ a * z =
      -((‖a‖ ^ 2 / 2 : ℝ) : ℂ) + (a * starRingEnd ℂ z - starRingEnd ℂ a * z) := by ring
  simp_rw [he, Complex.exp_add]
  rw [integral_const_mul, integral_gaussianMeasure_phase hs, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Cloning.ComplexCoherent

namespace Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

theorem coherentProjector_characteristic_product (z a : Fin d → ℂ) :
    tracePairing (coherentProjector z) (displacement a) =
      ∏ i, tracePairing (ComplexCoherent.coherentProjector (z i))
        (ComplexCoherent.displacement (a i)) := by
  change tracePairing (rankOneOperator (coherentVector z) (coherentVector z)) (displacement a) = _
  rw [tracePairing_rankOneOperator, displacement_coherentVector, inner_smul_right,
    inner_coherentVector]
  simp only [displacementPhase, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  change _ = tracePairing (rankOneOperator (ComplexCoherent.coherentVector (z i))
      (ComplexCoherent.coherentVector (z i))) (ComplexCoherent.displacement (a i))
  rw [tracePairing_rankOneOperator, ComplexCoherent.displacement_coherentVector,
    inner_smul_right, ComplexCoherent.inner_coherentVector]
  rfl

theorem gaussianMixture_characteristic_product {s : Fin d → ℝ}
    (hs : ∀ i, 0 < s i) (a : Fin d → ℂ) :
    tracePairing (gaussianMixture s) (displacement a) =
      ∏ i, Complex.exp (-(((s i + 1 / 2) * ‖a i‖ ^ 2 : ℝ) : ℂ)) := by
  have h := (tracePairingCLM.flip (displacement a)).integral_comp_comm
    (integrable_coherentProjector_gaussian hs)
  change (∫ z, tracePairing (coherentProjector z) (displacement a) ∂gaussianProductMeasure s) =
    tracePairing (gaussianMixture s) (displacement a) at h
  rw [← h]
  simp_rw [coherentProjector_characteristic_product]
  letI (i : Fin d) : IsProbabilityMeasure (CoherentGaussianMixture.gaussianMeasure (s i)) :=
    CoherentGaussianMixture.gaussianMeasure_probability (hs i)
  rw [gaussianProductMeasure, integral_fin_nat_prod_eq_prod
    (μ := fun i : Fin d => CoherentGaussianMixture.gaussianMeasure (s i))
    (fun i z => tracePairing (ComplexCoherent.coherentProjector z)
      (ComplexCoherent.displacement (a i)))]
  exact Finset.prod_congr rfl (fun i _ => ComplexCoherent.integral_coherent_characteristic_gaussian (hs i) (a i))

/-- The forward Fourier transform for literal product-geometric density
operators. It includes the empty zero-mode product. -/
theorem productThermal_characteristic {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (a : Fin d → ℂ) :
    tracePairing (vectorMixture (numberBasis d) (ThermalWitness.productGeometric q))
      (displacement a) =
      ∏ i, Complex.exp (-((((1 + q i) / (2 * (1 - q i))) * ‖a i‖ ^ 2 : ℝ) : ℂ)) := by
  let s : Fin d → ℝ := fun i => q i / (1 - q i)
  have hs (i : Fin d) : 0 < s i := div_pos (hq0 i) (sub_pos.mpr (hq1 i))
  have hq (i : Fin d) : s i / (1 + s i) = q i := by
    dsimp [s]
    have hden : 1 - q i ≠ 0 := (sub_pos.mpr (hq1 i)).ne'
    field_simp [hden]
    <;> ring
  have hm := integral_coherentProjector_gaussian_eq_productThermal hs
  simp_rw [hq] at hm
  change gaussianMixture s = vectorMixture (numberBasis d) (ThermalWitness.productGeometric q) at hm
  rw [← hm, gaussianMixture_characteristic_product hs]
  apply Finset.prod_congr rfl
  intro i _
  have hc : s i + 1 / 2 = (1 + q i) / (2 * (1 - q i)) := by
    dsimp [s]
    have hden : 1 - q i ≠ 0 := (sub_pos.mpr (hq1 i)).ne'
    field_simp [hden]
    <;> ring
  rw [hc]

end Cloning.MultimodeCoherent
