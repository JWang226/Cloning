import Cloning.UniversalLeastNoiseGaussian
import Cloning.WeylThermalFourierChannel

/-! The universal least-noise bound for actual thermal test operators.
The input, output, and test are genuine trace-class Fock operators. The
channel may have arbitrary correlated and non-Gaussian noise. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory
namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass Cloning.ThermalWitness Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ}

lemma geometricFourierWidth_amplified {g q : ℝ} (hg : g ≠ 0) (hq : q ≠ 1) :
    geometricFourierWidth (Cloning.Thermal.amplified g q) =
      g * geometricFourierWidth q + (g - 1) / 2 := by
  have hq' : 1 - q ≠ 0 := sub_ne_zero.mpr hq.symm
  unfold geometricFourierWidth Cloning.Thermal.amplified
  field_simp [hg, hq']
  ring

/-- An arbitrary covariant CPTP amplifier has at most the thermal-test
moment of the quantum-limited amplifier, in every finite mode count. -/
theorem covariant_thermal_test_moment_le
    (Φ : QuantumChannel (Fock d) (Fock d)) (r : ℝ)
    (hcov : ∀ a T, Φ.toLinearMap (displacementTraceMap a T) =
      displacementTraceMap (r • a) (Φ.toLinearMap T))
    (hr : 1 < r ^ 2) {q y : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (hy0 : ∀ i, 0 < y i) (hy1 : ∀ i, y i < 1) :
    (tracePairing (Φ.toLinearMap (vectorMixture (numberBasis d) (productGeometric q)))
      (vectorMixture (numberBasis d) (productGeometric y)).1).re ≤
    (tracePairing (vectorMixture (numberBasis d)
      (productGeometric (fun i => Cloning.Thermal.amplified (r ^ 2) (q i))))
      (vectorMixture (numberBasis d) (productGeometric y)).1).re := by
  let t : Fin d → ℝ := fun i => geometricFourierWidth (y i) + r ^ 2 * geometricFourierWidth (q i)
  have ht (i : Fin d) : (r ^ 2 - 1) / 2 ≤ t i :=
    thermal_moment_width_ge_noise r (hq0 i) (hq1 i) (hy0 i) (hy1 i)
  have hbound := quantumChannel_weyl_gaussian_bound Φ r hcov hr ht
  have hfourier := covariant_productThermal_moment_fourier
    Φ.toPositiveTracePreservingMap.toContinuousLinearMap r hcov hq0 hq1 hy0 hy1
  change tracePairing (Φ.toLinearMap (vectorMixture (numberBasis d) (productGeometric q)))
      (vectorMixture (numberBasis d) (productGeometric y)).1 =
      ((Real.pi ^ d : ℝ) : ℂ)⁻¹ * ∫ a : Fin d → ℂ,
        (gaussianWeight t a : ℂ) * weylMultiplier Φ.heisenberg r a at hfourier
  have hx0 (i : Fin d) : 0 < Cloning.Thermal.amplified (r ^ 2) (q i) :=
    (hq0 i).trans (Cloning.Thermal.lt_amplified hr (hq1 i))
  have hx1 (i : Fin d) : Cloning.Thermal.amplified (r ^ 2) (q i) < 1 :=
    Cloning.Thermal.amplified_lt_one (by linarith) (hq1 i)
  have hoverlap := productThermal_overlap_fourier hx0 hx1 hy0 hy1
  rw [hfourier, hoverlap]
  simp only [← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have hc : 0 ≤ (Real.pi ^ d)⁻¹ := inv_nonneg.mpr (pow_pos Real.pi_pos _).le
  apply (mul_le_mul_of_nonneg_left ((Complex.re_le_norm _).trans hbound) hc).trans_eq
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [geometricFourierWidth_amplified (by linarith : r ^ 2 ≠ 0) (hq1 i).ne]
  congr 1
  dsimp only [t]
  ring

end Cloning.MultimodeCoherent
