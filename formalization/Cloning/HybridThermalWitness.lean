import Cloning.HybridWeightedFidelity
import Cloning.HybridL1
import Cloning.GaussianWitness
import Cloning.ThermalWitness

/-!
# The actual Gaussian--thermal hybrid witness

The abstract weighted fidelity inequality is instantiated with the manuscript's
Gaussian density ratio and product thermal operator. Both integrability
conditions and the regularized inverse moment are proved here.
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false

variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def witnessMomentCLM (W : H →L[ℂ] H) : TraceClass H →L[ℝ] ℝ :=
  Complex.reCLM.comp ((tracePairingCLM.flip W).restrictScalars ℝ)

@[simp] theorem witnessMomentCLM_apply (W : H →L[ℂ] H) (A : TraceClass H) :
    witnessMomentCLM W A = witnessMoment A W := rfl

namespace PositiveField

theorem integrable_witnessMoment (R : PositiveField (H := H) μ) (W : H →L[ℂ] H) :
    Integrable (fun y => witnessMoment (R.value y).1 W) μ :=
  (witnessMomentCLM W).integrable_comp R.integrable

theorem integrable_weighted_witnessMoment (R : PositiveField (H := H) μ)
    (W : H →L[ℂ] H) (χ : Ω → ℝ) (hχ : AEStronglyMeasurable χ μ)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C) :
    Integrable (fun y => χ y * witnessMoment (R.value y).1 W) μ :=
  (R.integrable_witnessMoment W).bdd_mul hχ (Eventually.of_forall hbound)

theorem integrable_weighted_fibre (R : PositiveField (H := H) μ)
    (χ : Ω → ℝ) (hχ : AEStronglyMeasurable χ μ)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C) :
    Integrable (fun y => (χ y : ℂ) • (R.value y).1) μ := by
  apply R.integrable.bdd_smul C (Complex.continuous_ofReal.comp_aestronglyMeasurable hχ)
  exact Eventually.of_forall fun y => by simpa only [Complex.norm_real] using hbound y

/-- Integrating a classical weight gives an actual quantum trace-class operator. -/
def weightedMarginal (R : PositiveField (H := H) μ) (χ : Ω → ℝ) : TraceClass H :=
  ∫ y, (χ y : ℂ) • (R.value y).1 ∂μ

theorem weightedMarginal_nonneg (R : PositiveField (H := H) μ)
    (χ : Ω → ℝ) (hχ : AEStronglyMeasurable χ μ) (hχ0 : ∀ y, 0 ≤ χ y)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C) : 0 ≤ (R.weightedMarginal χ).1 := by
  let S := ofIntegrable (fun y => (χ y : ℂ) • (R.value y).1)
    (R.integrable_weighted_fibre χ hχ hbound) (fun y => by
      change 0 ≤ (χ y : ℂ) • (R.value y).1.1
      rw [Complex.coe_smul]
      exact smul_nonneg (hχ0 y) (R.value y).2)
  exact S.quantumMarginal_nonneg

/-- The compact-observable moment is exactly the weighted hybrid moment. -/
theorem witnessMoment_weightedMarginal (R : PositiveField (H := H) μ)
    (χ : Ω → ℝ) (hχ : AEStronglyMeasurable χ μ)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C) (W : H →L[ℂ] H) :
    witnessMoment (R.weightedMarginal χ) W =
      ∫ y, χ y * witnessMoment (R.value y).1 W ∂μ := by
  change witnessMomentCLM W (∫ y, (χ y : ℂ) • (R.value y).1 ∂μ) = _
  rw [← (witnessMomentCLM W).integral_comp_comm
    (R.integrable_weighted_fibre χ hχ hbound)]
  simp only [witnessMomentCLM_apply, witnessMoment_real_smul]

variable {k s : ℕ}

/-- The exact hybrid Gaussian--thermal bound with no assumed witness moments
or integrability estimates. The output may have arbitrary classical--quantum
correlations and arbitrary off-diagonal quantum coherences. -/
theorem rootFidelity_sq_le_gaussian_thermal
    (R : PositiveField (H := H) (volume : Measure (Fin k → ℝ)))
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) {g : ℝ} (hg : 1 ≤ g)
    (b : HilbertBasis (Fin s → ℕ) ℂ H) (q x : Fin s → ℝ)
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1) :
    R.rootFidelity (product (GaussianAffinity.productDensity a)
      (GaussianAffinity.integrable_productDensity a ha)
      (GaussianAffinity.productDensity_nonneg a)
      (InfiniteDiagonalFidelity.productGeometricState b q (fun i => (hq0 i).le)
        (fun i => (hqx i).trans (hx1 i)))) ^ 2 ≤
      witnessMoment
        (R.weightedMarginal (GaussianAffinity.productWitness a (fun i => a i / g)))
        (ThermalWitness.productWitnessOperator b q x) *
      Thermal.classicalBase g ^ ((k : ℝ) / 2) *
        ∏ i, Thermal.fidelity (q i) (x i) := by
  have hg0 : 0 < g := lt_of_lt_of_le zero_lt_one hg
  let χ := GaussianAffinity.productWitness a (fun i => a i / g)
  have hχm : AEStronglyMeasurable χ volume :=
    (GaussianAffinity.continuous_productWitness a _ ha (fun i => div_pos (ha i) hg0)).aestronglyMeasurable
  have hχ0 (y : Fin k → ℝ) : 0 < χ y :=
    GaussianAffinity.productWitness_pos a _ ha (fun i => div_pos (ha i) hg0) y
  have hχb (y : Fin k → ℝ) :
      ‖χ y‖ ≤ ∏ i, Real.sqrt (Real.sqrt (a i) / Real.sqrt (a i / g)) := by
    rw [Real.norm_eq_abs, abs_of_pos (hχ0 y)]
    apply GaussianAffinity.productWitness_le a _ ha (fun i => div_pos (ha i) hg0)
    intro i
    exact (div_le_iff₀ hg0).mpr (by nlinarith [ha i])
  have hM : 0 ≤ ∏ i, Thermal.fidelity (q i) (x i) :=
    Finset.prod_nonneg (fun i _ => (Thermal.fidelity_pos (hq0 i).le
      ((hqx i).trans (hx1 i)) ((hq0 i).trans (hqx i)).le (hx1 i)).le)
  have hinv (ε : ℝ) (hε : 0 < ε) : witnessMoment
      (TraceClass.ofOperator
        (InfiniteDiagonalFidelity.productGeometricState b q (fun i => (hq0 i).le)
          (fun i => (hqx i).trans (hx1 i))).op
        (InfiniteDiagonalFidelity.productGeometricState b q (fun i => (hq0 i).le)
          (fun i => (hqx i).trans (hx1 i))).traceClass)
      (CFC.rpow (regularizedWeight (ThermalWitness.productWitnessOperator b q x) ε) (-1)) ≤
        ∏ i, Thermal.fidelity (q i) (x i) :=
    ThermalWitness.product_thermal_regularized_inverse_moment b hq0 hqx hx1 hε
  have hf := R.rootFidelity_sq_le_weighted_product
    (GaussianAffinity.productDensity a) (GaussianAffinity.integrable_productDensity a ha)
    (GaussianAffinity.productDensity_nonneg a)
    (InfiniteDiagonalFidelity.productGeometricState b q (fun i => (hq0 i).le)
      (fun i => (hqx i).trans (hx1 i)))
    (ThermalWitness.productWitnessOperator_nonneg b hq0 hqx hx1) hM hinv χ hχ0
    (R.integrable_weighted_witnessMoment _ χ hχm hχb)
    (GaussianAffinity.integrable_productDensity_div_witness a _ ha
      (fun i => div_pos (ha i) hg0))
  rw [← R.witnessMoment_weightedMarginal χ hχm hχb] at hf
  simpa only [χ, GaussianAffinity.integral_productDensity_div_witness a ha hg0,
    Fintype.card_fin] using hf

end PositiveField
end Cloning.Hybrid
