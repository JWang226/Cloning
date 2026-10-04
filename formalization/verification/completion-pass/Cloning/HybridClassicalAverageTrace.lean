import Cloning.HybridGaussianMass
import Cloning.HybridTranslation
import Cloning.HybridCovariantWeighted

/-! Sharp classical Gaussian control of weighted averages of actual L¹
translations. The input may have arbitrary classical--quantum correlations. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k : ℕ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Gaussian translation estimate applies directly to every operator-valued
L¹ class, with its actual L¹ norm on the right. -/
theorem gaussian_shift_weighted_L1norm_le
    (R : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ)))
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) {g : ℝ} (hg : 1 ≤ g) :
    (∫ h : Fin k → ℝ, GaussianAffinity.productDensity a h *
      ∫ v : Fin k → ℝ, GaussianAffinity.productWitness a (fun i => a i / g)
        (fun i => v i + Real.sqrt g * h i) * ‖R v‖) ≤
      Thermal.classicalBase g ^ ((k : ℝ) / 2) * ‖R‖ := by
  let G := GaussianAffinity.productDensity a
  let χ := GaussianAffinity.productWitness a (fun i => a i / g)
  let B : (Fin k → ℝ) → ℝ := fun v => ‖R v‖
  let F : (Fin k → ℝ) × (Fin k → ℝ) → ℝ := fun z =>
    G z.1 * B z.2 * χ (fun i => z.2 i + Real.sqrt g * z.1 i)
  have hg0 : 0 < g := lt_of_lt_of_le zero_lt_one hg
  have hχp (v : Fin k → ℝ) : 0 < χ v :=
    GaussianAffinity.productWitness_pos a _ ha (fun i => div_pos (ha i) hg0) v
  have hχb (v : Fin k → ℝ) : ‖χ v‖ ≤
      ∏ i, Real.sqrt (Real.sqrt (a i) / Real.sqrt (a i / g)) := by
    rw [Real.norm_eq_abs, abs_of_pos (hχp v)]
    apply GaussianAffinity.productWitness_le a _ ha (fun i => div_pos (ha i) hg0)
    intro i
    exact (div_le_iff₀ hg0).mpr (by nlinarith [ha i])
  have hχc : Continuous χ := GaussianAffinity.continuous_productWitness a _ ha
    (fun i => div_pos (ha i) hg0)
  have hF : Integrable F (volume.prod volume) := by
    apply ((GaussianAffinity.integrable_productDensity a ha).mul_prod
      (L1.integrable_coeFn R).norm).mul_bdd
      ((hχc.comp (by fun_prop)).aestronglyMeasurable)
    exact Eventually.of_forall fun z => hχb _
  have he (v : Fin k → ℝ) :
      (∫ h : Fin k → ℝ, F (h, v)) = B v *
        (∫ h : Fin k → ℝ, G h * χ (fun i => v i + Real.sqrt g * h i)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun h => by dsimp [F]; ring
  calc
    _ = ∫ h : Fin k → ℝ, ∫ v : Fin k → ℝ, F (h, v) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun h => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun v => by dsimp [F, G, B, χ]; ring
    _ = ∫ v : Fin k → ℝ, ∫ h : Fin k → ℝ, F (h, v) := integral_integral_swap hF
    _ ≤ ∫ v : Fin k → ℝ, B v * Thermal.classicalBase g ^ ((k : ℝ) / 2) := by
      apply integral_mono hF.integral_prod_right ((L1.integrable_coeFn R).norm.mul_const _)
      intro v
      dsimp only
      rw [he]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [Fintype.card_fin] using
        GaussianAffinity.integral_product_translated_witness_le a ha hg v
    _ = _ := by rw [integral_mul_const, L1.norm_eq_integral_norm]; exact mul_comm _ _

/-- Real integrated trace against a bounded classical weight. -/
def weightedL1Trace (χ : (Fin k → ℝ) → ℝ) (hχ : AEStronglyMeasurable χ volume)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C) :
    Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ)) →L[ℝ] ℝ :=
  Complex.reCLM.comp
    ((traceCLM.comp (weightedL1IntegralCLM χ hχ hbound)).restrictScalars ℝ)

lemma weightedL1Trace_apply (χ : (Fin k → ℝ) → ℝ)
    (hχ : AEStronglyMeasurable χ volume) {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C)
    (R : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    weightedL1Trace χ hχ hbound R =
      (traceCLM (weightedL1Integral χ hχ hbound R)).re := rfl

lemma norm_weightedL1Trace_le (χ : (Fin k → ℝ) → ℝ)
    (hχ : AEStronglyMeasurable χ volume) {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C)
    (R : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    ‖weightedL1Trace χ hχ hbound R‖ ≤ C * ‖R‖ := by
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_trace_le_traceNorm (weightedL1Integral χ hχ hbound R).2).trans
  exact norm_weightedL1Integral_le χ hχ hbound R

lemma weightedL1Trace_eq_integral (χ : (Fin k → ℝ) → ℝ)
    (hχ : AEStronglyMeasurable χ volume) {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C)
    (R : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    weightedL1Trace χ hχ hbound R = ∫ y, χ y * (traceCLM (R y)).re := by
  let T : TraceClass H →L[ℝ] ℝ := Complex.reCLM.comp (traceCLM.restrictScalars ℝ)
  change T (∫ y, (χ y : ℂ) • R y) = _
  rw [← T.integral_comp_comm (weightedL1_integrable χ hχ hbound R)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    change (traceCLM ((χ y : ℂ) • R y)).re = _
    simp only [map_smul, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The exact sign of the output translation in the weighted integral. -/
lemma weightedL1Trace_classicalTranslation (χ : (Fin k → ℝ) → ℝ)
    (hχ : AEStronglyMeasurable χ volume) {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C)
    (h : Fin k → ℝ) (R : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    weightedL1Trace χ hχ hbound (classicalTranslation h R) =
      ∫ y, χ (y + h) * (traceCLM (R y)).re := by
  rw [weightedL1Trace_eq_integral]
  calc
    _ = ∫ y, χ y * (traceCLM (R (y - h))).re := by
      apply integral_congr_ae
      filter_upwards [classicalTranslation_ae h R] with y hy
      rw [hy]
    _ = _ := by
      rw [← integral_add_right_eq_self (fun y => χ y * (traceCLM (R (y - h))).re) h]
      simp only [add_sub_cancel_right]

/-- A translated weighted trace is dominated by the same translated weight
against the L¹ norm density, for arbitrary complex inputs. -/
lemma weightedL1Trace_classicalTranslation_le (χ : (Fin k → ℝ) → ℝ)
    (hχ : AEStronglyMeasurable χ volume) (hχ0 : ∀ y, 0 ≤ χ y)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C)
    (h : Fin k → ℝ) (R : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    weightedL1Trace χ hχ hbound (classicalTranslation h R) ≤
      ∫ y, χ (y + h) * ‖R y‖ := by
  rw [weightedL1Trace_classicalTranslation]
  have hm : AEStronglyMeasurable (fun y => χ (y + h)) volume :=
    hχ.comp_measurePreserving (measurePreserving_add_right volume h)
  have hi := (Complex.reCLM.comp ((traceCLM (H := H)).restrictScalars ℝ)).integrable_comp
    (L1.integrable_coeFn R)
  apply integral_mono (hi.bdd_mul hm (Eventually.of_forall fun y => hbound (y + h)))
    ((L1.integrable_coeFn R).norm.bdd_mul hm (Eventually.of_forall fun y => hbound (y + h)))
  intro y
  apply mul_le_mul_of_nonneg_left _ (hχ0 _)
  exact (Complex.re_le_norm _).trans (norm_trace_le_traceNorm (R y).2)

/-- The actual Gaussian average of translated weighted traces has the sharp
classical affinity bound, with no assumption on the input correlations. -/
theorem gaussian_average_weightedL1Trace_le
    (R : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ)))
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) {g : ℝ} (hg : 1 ≤ g)
    (hχ : AEStronglyMeasurable
      (GaussianAffinity.productWitness a (fun i => a i / g)) volume)
    {C : ℝ} (hbound : ∀ y,
      ‖GaussianAffinity.productWitness a (fun i => a i / g) y‖ ≤ C) :
    (∫ h : Fin k → ℝ, GaussianAffinity.productDensity a h *
      weightedL1Trace (GaussianAffinity.productWitness a (fun i => a i / g)) hχ hbound
        (classicalTranslation (Real.sqrt g • h) R)) ≤
      Thermal.classicalBase g ^ ((k : ℝ) / 2) * ‖R‖ := by
  let G := GaussianAffinity.productDensity a
  let χ := GaussianAffinity.productWitness a (fun i => a i / g)
  let Q := weightedL1Trace (H := H) χ hχ hbound
  have hχc : Continuous χ := GaussianAffinity.continuous_productWitness a _ ha
    (fun i => div_pos (ha i) (lt_of_lt_of_le zero_lt_one hg))
  have hχ0 (y : Fin k → ℝ) : 0 ≤ χ y :=
    (GaussianAffinity.productWitness_pos a _ ha
      (fun i => div_pos (ha i) (lt_of_lt_of_le zero_lt_one hg)) y).le
  have hi : Integrable (fun h : Fin k → ℝ => G h * Q
      (classicalTranslation (Real.sqrt g • h) R)) := by
    apply (GaussianAffinity.integrable_productDensity a ha).mul_bdd
      (Q.continuous.comp ((continuous_classicalTranslation R).comp
        (continuous_const.smul continuous_id))).aestronglyMeasurable
    exact Eventually.of_forall fun h => by
      simpa only [norm_classicalTranslation] using
        norm_weightedL1Trace_le χ hχ hbound (classicalTranslation (Real.sqrt g • h) R)
  have hF : Integrable (fun z : (Fin k → ℝ) × (Fin k → ℝ) =>
      G z.1 * ‖R z.2‖ * χ (z.2 + Real.sqrt g • z.1)) (volume.prod volume) := by
    apply ((GaussianAffinity.integrable_productDensity a ha).mul_prod
      (L1.integrable_coeFn R).norm).mul_bdd
      ((hχc.comp (by fun_prop)).aestronglyMeasurable)
    exact Eventually.of_forall fun z => hbound _
  have hj : Integrable (fun h : Fin k → ℝ =>
      G h * ∫ y : Fin k → ℝ, χ (y + Real.sqrt g • h) * ‖R y‖) := by
    convert hF.integral_prod_left using 1
    funext h
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  have hb : (∫ h : Fin k → ℝ, G h * Q (classicalTranslation (Real.sqrt g • h) R)) ≤
      ∫ h : Fin k → ℝ, G h * ∫ y : Fin k → ℝ, χ (y + Real.sqrt g • h) * ‖R y‖ := by
    apply integral_mono hi hj
    intro h
    exact mul_le_mul_of_nonneg_left
      (weightedL1Trace_classicalTranslation_le χ hχ hχ0 hbound _ R)
      (GaussianAffinity.productDensity_nonneg a h)
  exact hb.trans (gaussian_shift_weighted_L1norm_le R a ha hg)

end Cloning.Hybrid
