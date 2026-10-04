import Cloning.AmplifierWeylMultimodeCovariance
import Cloning.WeylThermalFourierChannel
import Cloning.UniversalLeastNoiseThermalTest

/-! The constructed covariant amplifier has the quantum-limited Gaussian
Weyl multiplier and sends genuine product thermal densities to their amplified
thermal densities. Equality follows from characteristic-function injectivity. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.MultimodeAmplifier
open Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture Cloning.ThermalWitness
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ}

/-- The actual common-gain amplifier, independent of the input spectrum. -/
def gainChannel (g : ℝ) (hg : 1 < g) : QuantumChannel (Fock d) (Fock d) :=
  channel (fun _ => 1 - 1 / g) (fun _ => Cloning.BosonicAmplifier.gainNoise_nonneg hg)
    (fun _ => Cloning.BosonicAmplifier.gainNoise_lt_one hg)

lemma gainChannel_covariant (g : ℝ) (hg : 1 < g) (a : Fin d → ℂ) (A : TraceClass (Fock d)) :
    (gainChannel g hg).toLinearMap (displacementTraceMap a A) =
      displacementTraceMap (Real.sqrt g • a) ((gainChannel g hg).toLinearMap A) :=
  channel_weyl_covariant_gain g hg a A

lemma gainNoise_pos {g : ℝ} (hg : 1 < g) : 0 < 1 - 1 / g := by
  have h := (div_lt_one (by linarith : 0 < g)).mpr hg
  linarith

lemma gainChannel_vacuum (g : ℝ) (hg : 1 < g) :
    (gainChannel g hg).toLinearMap (coherentProjector (0 : Fin d → ℂ)) =
      vectorMixture (numberBasis d) (productGeometric (fun _ => 1 - 1 / g)) :=
  channel_vacuum _ _ _

lemma vacuumProjector_characteristic (a : Fin d → ℂ) :
    tracePairing (coherentProjector (0 : Fin d → ℂ)) (displacement a) =
      ∏ i, (Real.exp (-‖a i‖ ^ 2 / 2) : ℂ) := by
  change tracePairing (rankOneOperator (coherentVector 0) (coherentVector 0)) (displacement a) = _
  rw [tracePairing_rankOneOperator, vacuum_characteristic]

lemma gainNoise_width {g : ℝ} (hg : g ≠ 0) :
    geometricFourierWidth (1 - 1 / g) = g - 1 / 2 := by
  unfold geometricFourierWidth
  field_simp
  ring

/-- Exact quantum-limited Weyl multiplier of the physical amplifier. -/
theorem gainChannel_weylMultiplier (g : ℝ) (hg : 1 < g) (a : Fin d → ℂ) :
    weylMultiplier (gainChannel g hg).heisenberg (Real.sqrt g) a =
      ∏ i, Complex.exp (-((((g - 1) / 2) * ‖a i‖ ^ 2 : ℝ) : ℂ)) := by
  let Φ := gainChannel (d := d) g hg
  have hcov := gainChannel_covariant (d := d) g hg
  have hm := (quantumChannel_weyl_multiplier Φ (Real.sqrt g) hcov).1 a
  have hv := heisenbergDual_pairing Φ.toPositiveTracePreservingMap.toContinuousLinearMap
    (coherentProjector (0 : Fin d → ℂ)) (displacement a)
  change tracePairing (coherentProjector (0 : Fin d → ℂ)) (Φ.heisenberg (displacement a)) =
    tracePairing (Φ.toLinearMap (coherentProjector 0)) (displacement a) at hv
  rw [hm, map_smul, smul_eq_mul, vacuumProjector_characteristic,
    show Φ.toLinearMap (coherentProjector 0) =
      vectorMixture (numberBasis d) (productGeometric (fun _ => 1 - 1 / g))
      from gainChannel_vacuum g hg,
    productThermal_characteristic (fun _ => gainNoise_pos hg)
      (fun _ => Cloning.BosonicAmplifier.gainNoise_lt_one hg)] at hv
  have hsq : Real.sqrt g ^ 2 = g := Real.sq_sqrt (by linarith)
  have hvscale : (∏ i : Fin d, (Real.exp (-‖(Real.sqrt g • a) i‖ ^ 2 / 2) : ℂ)) =
      ∏ i, Complex.exp (-(((g / 2) * ‖a i‖ ^ 2 : ℝ) : ℂ)) := by
    apply Finset.prod_congr rfl
    intro i _
    simp only [Pi.smul_apply, norm_real_smul_sq, hsq, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hvscale] at hv
  have hn : (∏ i : Fin d, Complex.exp (-(((g / 2) * ‖a i‖ ^ 2 : ℝ) : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => Complex.exp_ne_zero _)
  apply mul_right_cancel₀ hn
  change weylMultiplier Φ.heisenberg (Real.sqrt g) a * _ = _
  rw [hv, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  change Complex.exp (-((geometricFourierWidth (1 - 1 / g) * ‖a i‖ ^ 2 : ℝ) : ℂ)) = _
  rw [gainNoise_width (by linarith : g ≠ 0), ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Actual thermal amplification on the full multimode Fock space. -/
theorem gainChannel_productThermal (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    (gainChannel g hg).toLinearMap (vectorMixture (numberBasis d) (productGeometric q)) =
      vectorMixture (numberBasis d) (productGeometric (fun i => Cloning.Thermal.amplified g (q i))) := by
  apply characteristic_injective
  funext a
  dsimp only
  have hx0 (i : Fin d) : 0 < Cloning.Thermal.amplified g (q i) :=
    (hq0 i).trans (Cloning.Thermal.lt_amplified hg (hq1 i))
  have hx1 (i : Fin d) : Cloning.Thermal.amplified g (q i) < 1 :=
    Cloning.Thermal.amplified_lt_one (by linarith) (hq1 i)
  rw [productThermal_characteristic hx0 hx1]
  have h := covariant_thermal_output_characteristic
    (gainChannel (d := d) g hg).toPositiveTracePreservingMap.toContinuousLinearMap
    (Real.sqrt g) (gainChannel_covariant g hg) hq0 hq1 a
  change tracePairing ((gainChannel g hg).toLinearMap
      (vectorMixture (numberBasis d) (productGeometric q))) (displacement a) =
    weylMultiplier (gainChannel g hg).heisenberg (Real.sqrt g) a * _ at h
  rw [h, gainChannel_weylMultiplier, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.sq_sqrt (by linarith : 0 ≤ g), ← Complex.exp_add]
  change Complex.exp _ = Complex.exp (-((geometricFourierWidth (Cloning.Thermal.amplified g (q i)) * ‖a i‖ ^ 2 : ℝ) : ℂ))
  rw [geometricFourierWidth_amplified (by linarith : g ≠ 0) (hq1 i).ne]
  congr 1
  push_cast
  ring

end Cloning.MultimodeAmplifier
