import Cloning.WeylThermalFourierChannel
import Cloning.WeylCovariantization
import Cloning.Thermal

/-! Actual Gaussian displacement averaging of product thermal states. This
comparison-state identity uses trace-class Bochner integration and Weyl
characteristic injectivity, independently of a mixed-state LAN theorem. -/
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Cloning.PCTGaussianOutput
open Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture Cloning.ThermalWitness
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

theorem integrable_displacement (μ : Measure (Fin d → ℂ)) [IsFiniteMeasure μ]
    (A : TraceClass (Fock d)) : Integrable (fun z => displacementTraceMap z A) μ := by
  apply (integrable_const ‖A‖).mono' (continuous_displacementTraceMap A).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => (displacementTraceMap_norm z A).le)

/-- The random-displacement channel, constructed on the entire trace class. -/
def displacementAverageChannel (μ : Measure (Fin d → ℂ)) [IsProbabilityMeasure μ] :
    QuantumChannel (Fock d) (Fock d) :=
  QuantumChannel.average μ displacementChannel (fun A => by
    simpa only [← displacementTraceMap_eq_channel] using
      (continuous_displacementTraceMap A).aestronglyMeasurable)

@[simp] theorem displacementAverageChannel_apply
    (μ : Measure (Fin d → ℂ)) [IsProbabilityMeasure μ] (A : TraceClass (Fock d)) :
    (displacementAverageChannel μ).toLinearMap A = ∫ z, displacementTraceMap z A ∂μ := by
  change (∫ z, (displacementChannel z).toLinearMap A ∂μ) = _
  simp only [displacementTraceMap_eq_channel]

theorem displacement_characteristic (z a : Fin d → ℂ) (A : TraceClass (Fock d)) :
    tracePairing (displacementTraceMap z A) (displacement a) =
      weylCharacter z (-a) * tracePairing A (displacement a) := by
  have hc : weylCharacter (-z) a = weylCharacter z (-a) := by
    simpa only [neg_one_smul] using weylCharacter_real_smul_left (-1) z a
  simp only [displacementTraceMap, tracePairing_sandwich, ContinuousLinearMap.mul_def,
    show displacement z = displacement (-(-z)) by simp, displacement_conjugation,
    map_smul, smul_eq_mul, hc]

/-- The full quantum characteristic of the actual displaced-state integral. -/
theorem gaussian_displacement_characteristic {b : Fin d → ℝ}
    (hb : ∀ i, 0 < b i) (A : TraceClass (Fock d)) (a : Fin d → ℂ) :
    tracePairing (∫ z, displacementTraceMap z A ∂gaussianProductMeasure b) (displacement a) =
      (∏ i, Complex.exp (-((b i * ‖a i‖ ^ 2 : ℝ) : ℂ))) *
        tracePairing A (displacement a) := by
  letI := gaussianProductMeasure_probability hb
  have h := (tracePairingCLM.flip (displacement a)).integral_comp_comm
    (integrable_displacement (gaussianProductMeasure b) A)
  change (∫ z, tracePairing (displacementTraceMap z A) (displacement a)
    ∂gaussianProductMeasure b) = tracePairing (∫ z, displacementTraceMap z A
    ∂gaussianProductMeasure b) (displacement a) at h
  rw [← h]
  simp only [ContinuousLinearMap.flip_apply, tracePairingCLM_apply,
    displacement_characteristic, integral_mul_const]
  rw [integral_weylCharacter_gaussianProductMeasure hb]
  simp only [Pi.neg_apply, norm_neg]

/-- Exact thermal output whenever its Weyl width is the input width plus the
actual circular displacement variance. No covariance or moment hypothesis
stands in for the integral. -/
theorem gaussian_displacement_productThermal {b q x : Fin d → ℝ}
    (hb : ∀ i, 0 < b i) (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (hx0 : ∀ i, 0 < x i) (hx1 : ∀ i, x i < 1)
    (hwidth : ∀ i, geometricFourierWidth (x i) = geometricFourierWidth (q i) + b i) :
    (∫ z, displacementTraceMap z (vectorMixture (numberBasis d) (productGeometric q))
      ∂gaussianProductMeasure b) = vectorMixture (numberBasis d) (productGeometric x) := by
  apply characteristic_injective
  funext a
  dsimp only
  rw [gaussian_displacement_characteristic hb,
    productThermal_characteristic hq0 hq1, productThermal_characteristic hx0 hx1,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  change Complex.exp _ * Complex.exp _ =
    Complex.exp (-((geometricFourierWidth (x i) * ‖a i‖ ^ 2 : ℝ) : ℂ))
  rw [hwidth, ← Complex.exp_add]
  congr 1
  unfold geometricFourierWidth
  push_cast
  ring

/-- Circular tangent-displacement variance in the thermal coordinate `q`. -/
def pctDisplacementVariance (g q : ℝ) : ℝ := (g - 1) * (1 + q) / (1 - q)

lemma pctDisplacementVariance_pos {g q : ℝ} (hg : 1 < g)
    (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 < pctDisplacementVariance g q := by
  unfold pctDisplacementVariance
  exact div_pos (mul_pos (sub_pos.mpr hg) (by linarith)) (sub_pos.mpr hq1)

lemma pct_width {g q : ℝ} (hg : 1 < g) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    geometricFourierWidth (Thermal.pct g q) =
      geometricFourierWidth q + pctDisplacementVariance g q := by
  have hd := (Thermal.pct_denominator_pos hg hq0).ne'
  have hq := (sub_pos.mpr hq1).ne'
  have hx := (sub_pos.mpr (Thermal.pct_lt_one hg hq0 hq1)).ne'
  unfold geometricFourierWidth pctDisplacementVariance Thermal.pct at *
  field_simp [hd, hq]
  ring_nf
  field_simp [hq]
  <;> ring

/-- The explicit Gaussian comparison channel sends every strict product
thermal state to the literal product with parameters `Thermal.pct g q`. -/
theorem gaussian_displacement_productThermal_pct (g : ℝ) (hg : 1 < g)
    {q : Fin d → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    (∫ z, displacementTraceMap z (vectorMixture (numberBasis d) (productGeometric q))
      ∂gaussianProductMeasure (fun i => pctDisplacementVariance g (q i))) =
        vectorMixture (numberBasis d) (productGeometric (fun i => Thermal.pct g (q i))) := by
  apply gaussian_displacement_productThermal
    (fun i => pctDisplacementVariance_pos hg (hq0 i).le (hq1 i)) hq0 hq1
  · intro i
    exact ((hq0 i).trans (Thermal.lt_amplified hg (hq1 i))).trans
      (Thermal.amplified_lt_pct hg (hq0 i) (hq1 i))
  · exact fun i => Thermal.pct_lt_one hg (hq0 i).le (hq1 i)
  · exact fun i => pct_width hg (hq0 i).le (hq1 i)

end Cloning.PCTGaussianOutput
