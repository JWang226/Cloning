import Cloning.WeylThermalFourier
import Cloning.WeylGaussianThermal

/-! Exact inverse Weyl representation of actual product thermal operators.
This converts thermal operator moments of arbitrary trace-class outputs into
the Gaussian scalar functionals controlled by quantum-positive kernels. -/

noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {d : ℕ}

lemma weylCharacter_eq_prod_exp (a b : Fin d → ℂ) :
    weylCharacter a b = ∏ i, Complex.exp
      (a i * (starRingEnd ℂ) (b i) - (starRingEnd ℂ) (a i) * b i) := by
  simp only [weylCharacter, displacementPhase, ← Finset.prod_div_distrib,
    ComplexCoherent.displacementPhase, ← Complex.exp_sub]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  ring

/-- The actual product Gaussian measure has the exact symplectic Fourier
transform, with the sign convention of the constructed Weyl operators. -/
theorem integral_weylCharacter_gaussianProductMeasure {s : Fin d → ℝ}
    (hs : ∀ i, 0 < s i) (a : Fin d → ℂ) :
    (∫ z, weylCharacter z a ∂gaussianProductMeasure s) =
      ∏ i, Complex.exp (-((s i * ‖a i‖ ^ 2 : ℝ) : ℂ)) := by
  letI (i : Fin d) : IsProbabilityMeasure (Cloning.CoherentGaussianMixture.gaussianMeasure (s i)) :=
    Cloning.CoherentGaussianMixture.gaussianMeasure_probability (hs i)
  simp_rw [weylCharacter_eq_prod_exp]
  rw [gaussianProductMeasure, integral_fin_nat_prod_eq_prod
    (μ := fun i : Fin d => Cloning.CoherentGaussianMixture.gaussianMeasure (s i))
    (fun i (z : ℂ) => Complex.exp
      (z * (starRingEnd ℂ) (a i) - (starRingEnd ℂ) z * a i))]
  apply Finset.prod_congr rfl
  intro i _
  have heq (z : ℂ) : z * (starRingEnd ℂ) (a i) - (starRingEnd ℂ) z * a i =
      (-a i) * (starRingEnd ℂ) z - (starRingEnd ℂ) (-a i) * z := by
    rw [map_neg]
    ring
  simp_rw [heq]
  rw [Cloning.ComplexCoherent.integral_gaussianMeasure_phase (hs i), norm_neg]

/-- Lebesgue Fourier weight of the product thermal state with mean occupation
numbers `sᵢ`. The per-mode normalization is exactly `1/π`. -/
def thermalFourierWeight (s : Fin d → ℝ) (a : Fin d → ℂ) : ℝ :=
  ∏ i, Real.exp (-(s i + 1 / 2) * ‖a i‖ ^ 2) / Real.pi

lemma thermalFourierWeight_factor (s : Fin d → ℝ) (a : Fin d → ℂ) :
    (weylGaussianWeight a : ℂ) *
      (∏ i, Complex.exp (-((s i * ‖a i‖ ^ 2 : ℝ) : ℂ))) =
      (thermalFourierWeight s a : ℂ) := by
  simp only [weylGaussianWeight, thermalFourierWeight, Complex.ofReal_prod,
    ← Finset.prod_mul_distrib, ComplexCoherent.weylGaussianWeight,
    Complex.ofReal_div, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  apply Finset.prod_congr rfl
  intro i _
  have hreal : Real.exp (-‖a i‖ ^ 2 / 2) / Real.pi *
      Real.exp (-(s i * ‖a i‖ ^ 2)) =
      Real.exp (-(s i + 1 / 2) * ‖a i‖ ^ 2) / Real.pi := by
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    congr 2
    ring
  exact_mod_cast hreal

/-- Exact thermal operator-to-Fourier bridge for every trace-class test
operator and every positive finite-mode thermal occupation vector. -/
theorem tracePairing_productThermal_fourier {s : Fin d → ℝ}
    (hs : ∀ i, 0 < s i) (T : TraceClass (Fock d)) :
    tracePairing T (vectorMixture (numberBasis d)
      (fun k => ∏ i, Cloning.Thermal.geometric (s i / (1 + s i)) (k i))).1 =
      ∫ a : Fin d → ℂ, (thermalFourierWeight s a : ℂ) * tracePairing T (displacement a) := by
  letI := gaussianProductMeasure_probability hs
  rw [← integral_coherentProjector_gaussian_eq_productThermal hs,
    tracePairing_coherentMixture_fourier]
  congr 1
  funext a
  rw [integral_weylCharacter_gaussianProductMeasure hs, ← mul_assoc,
    thermalFourierWeight_factor]

/-- The same witness bridge in geometric parameters `0<qᵢ<1`, as used by
the manuscript's product thermal state and compact witness. -/
theorem tracePairing_geometricThermal_fourier {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (T : TraceClass (Fock d)) :
    tracePairing T (vectorMixture (numberBasis d)
      (fun k => ∏ i, Cloning.Thermal.geometric (q i) (k i))).1 =
      ∫ a : Fin d → ℂ,
        (∏ i, (Real.exp (-((1 + q i) / (2 * (1 - q i))) * ‖a i‖ ^ 2) / Real.pi : ℂ)) *
          tracePairing T (displacement a) := by
  let s : Fin d → ℝ := fun i => q i / (1 - q i)
  have hs (i : Fin d) : 0 < s i := div_pos (hq0 i) (sub_pos.mpr (hq1 i))
  have hq (i : Fin d) : s i / (1 + s i) = q i := by
    dsimp only [s]
    field_simp [ne_of_gt (sub_pos.mpr (hq1 i))]
    <;> ring
  have hc (i : Fin d) : s i + 1 / 2 = (1 + q i) / (2 * (1 - q i)) := by
    dsimp only [s]
    field_simp [ne_of_gt (sub_pos.mpr (hq1 i))]
    <;> ring
  have h := tracePairing_productThermal_fourier hs T
  simpa only [hq, thermalFourierWeight, hc, Complex.ofReal_prod, Complex.ofReal_div] using h

end Cloning.MultimodeCoherent
