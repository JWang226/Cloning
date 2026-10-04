import Cloning.HybridClassicalAverageTrace
import Cloning.HybridClassicalConvolution

/-! The sharp Gaussian residual trace bound for actual approximately
translation-covariant hybrid channels. Explicit L¹ approximate identities
remove the input mollifier; neither the sharp trace bound nor density
recovery is an assumption. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k : ℕ} {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma L1CompletelyPositive.norm_map_of_nonneg
    {Λ : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ)) →ₗ[ℂ]
      Lp (TraceClass K) 1 (volume : Measure (Fin k → ℝ))}
    (hΛ : L1CompletelyPositive Λ) (hTP : L1TracePreserving Λ)
    (A : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ)))
    (hA : ∀ᵐ y ∂volume, 0 ≤ (A y).1) : ‖Λ A‖ = ‖A‖ := by
  have hp := hΛ.map_nonneg A hA
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
  calc
    _ = ∫ y, (traceCLM (Λ A y)).re := by
      apply integral_congr_ae
      exact hp.mono fun y hy => TraceClass.norm_eq_trace_re_of_nonneg _ hy
    _ = (∫ y, traceCLM (Λ A y)).re :=
      Complex.reCLM.integral_comp_comm (traceCLM.integrable_comp (L1.integrable_coeFn _))
    _ = (∫ y, traceCLM (A y)).re := congrArg Complex.re (hTP A)
    _ = ∫ y, (traceCLM (A y)).re :=
      (Complex.reCLM.integral_comp_comm (traceCLM.integrable_comp (L1.integrable_coeFn _))).symm
    _ = _ := by
      apply integral_congr_ae
      exact hA.mono fun y hy => (TraceClass.norm_eq_trace_re_of_nonneg _ hy).symm

lemma integrable_mul_weightedL1Trace_translation
    (G : (Fin k → ℝ) → ℝ) (hG : Integrable G)
    (χ : (Fin k → ℝ) → ℝ) (hχ : AEStronglyMeasurable χ volume)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C) (r : ℝ)
    (R : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    Integrable (fun h => G h * weightedL1Trace χ hχ hbound
      (classicalTranslation (r • h) R)) := by
  apply hG.mul_bdd
    ((weightedL1Trace χ hχ hbound).continuous.comp
      ((continuous_classicalTranslation R).comp
        (continuous_const.smul continuous_id))).aestronglyMeasurable
  exact Eventually.of_forall fun h => by
    simpa only [norm_classicalTranslation] using
      norm_weightedL1Trace_le χ hχ hbound (classicalTranslation (r • h) R)

/-- A finite covariance defect gives the sharp Gaussian trace estimate for
an actual Bochner-averaged input. -/
lemma weightedL1Trace_gaussian_average_le
    (Λ : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ)) →L[ℂ]
      Lp (TraceClass K) 1 (volume : Measure (Fin k → ℝ)))
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) {g : ℝ} (hg : 1 ≤ g)
    (hχ : AEStronglyMeasurable
      (GaussianAffinity.productWitness a (fun i => a i / g)) volume)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y,
      ‖GaussianAffinity.productWitness a (fun i => a i / g) y‖ ≤ C)
    (b : (Fin k → ℝ) → ℝ)
    (hb : Integrable (fun h => GaussianAffinity.productDensity a h * b h))
    (herror : ∀ h R, ‖Λ (classicalTranslation h R) -
      classicalTranslation (Real.sqrt g • h) (Λ R)‖ ≤ b h * ‖R‖)
    (R : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    weightedL1Trace (GaussianAffinity.productWitness a (fun i => a i / g)) hχ hbound
      (Λ (classicalAverage (GaussianAffinity.productDensity a) R)) ≤
      Thermal.classicalBase g ^ ((k : ℝ) / 2) * ‖Λ R‖ +
        C * (∫ h, GaussianAffinity.productDensity a h * b h) * ‖R‖ := by
  let G := GaussianAffinity.productDensity a
  let χ := GaussianAffinity.productWitness a (fun i => a i / g)
  let Q := weightedL1Trace (H := K) χ hχ hbound
  have hG := GaussianAffinity.integrable_productDensity a ha
  have hI := integrable_classicalAverage_integrand G hG R
  have hi : Integrable (fun h => G h * Q (Λ (classicalTranslation h R))) := by
    convert (Q.comp (Λ.restrictScalars ℝ)).integrable_comp hI using 1
    funext h
    simp only [ContinuousLinearMap.comp_apply, map_smul, Complex.coe_smul,
      ContinuousLinearMap.coe_restrictScalars', smul_eq_mul]
  have ho := integrable_mul_weightedL1Trace_translation G hG χ hχ hbound
    (Real.sqrt g) (Λ R)
  have he : Integrable (fun h => C * (G h * b h) * ‖R‖) :=
    (hb.const_mul C).mul_const ‖R‖
  have hpoint (h : Fin k → ℝ) :
      Q (Λ (classicalTranslation h R)) ≤
        Q (classicalTranslation (Real.sqrt g • h) (Λ R)) + C * b h * ‖R‖ := by
    have hnorm := (norm_weightedL1Trace_le χ hχ hbound
      (Λ (classicalTranslation h R) - classicalTranslation (Real.sqrt g • h) (Λ R))).trans
      (mul_le_mul_of_nonneg_left (herror h R) hC)
    have hr := (le_abs_self (Q (Λ (classicalTranslation h R) -
      classicalTranslation (Real.sqrt g • h) (Λ R)))).trans hnorm
    rw [map_sub] at hr
    nlinarith
  have heq : Q (Λ (classicalAverage G R)) =
      ∫ h, G h * Q (Λ (classicalTranslation h R)) := by
    change (Q.comp (Λ.restrictScalars ℝ)) (∫ h, (G h : ℂ) • classicalTranslation h R) = _
    rw [← (Q.comp (Λ.restrictScalars ℝ)).integral_comp_comm hI]
    apply integral_congr_ae
    exact Eventually.of_forall fun h => by
      simp only [ContinuousLinearMap.comp_apply, Complex.coe_smul, map_smul,
        ContinuousLinearMap.coe_restrictScalars', smul_eq_mul]
  rw [heq]
  calc
    _ ≤ ∫ h, (G h * Q (classicalTranslation (Real.sqrt g • h) (Λ R)) +
        C * (G h * b h) * ‖R‖) := by
      apply integral_mono hi (ho.add he)
      intro h
      have ht := mul_le_mul_of_nonneg_left (hpoint h)
        (GaussianAffinity.productDensity_nonneg a h)
      convert ht using 1
      dsimp only [G, Q, Pi.add_apply]
      ring
    _ = (∫ h, G h * Q (classicalTranslation (Real.sqrt g • h) (Λ R))) +
        C * (∫ h, G h * b h) * ‖R‖ := by
      rw [integral_add ho he, integral_mul_const, integral_const_mul]
    _ ≤ _ := add_le_add (gaussian_average_weightedL1Trace_le (Λ R) a ha hg hχ hbound) le_rfl

/-- The sharp residual trace bound for any actual hybrid channel with a
quantitative classical covariance defect. The input mollifier and its limit
are explicitly constructed in operator-valued L¹. -/
theorem weightedQuantumMap_gaussian_trace_le
    (Λ : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ)) →L[ℂ]
      Lp (TraceClass K) 1 (volume : Measure (Fin k → ℝ)))
    (hΛ : L1CompletelyPositive Λ.toLinearMap) (hTP : L1TracePreserving Λ.toLinearMap)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) {g : ℝ} (hg : 1 ≤ g)
    (hχ : AEStronglyMeasurable
      (GaussianAffinity.productWitness a (fun i => a i / g)) volume)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y,
      ‖GaussianAffinity.productWitness a (fun i => a i / g) y‖ ≤ C)
    (b : (Fin k → ℝ) → ℝ)
    (hb : Integrable (fun h => GaussianAffinity.productDensity a h * b h))
    (herror : ∀ h R, ‖Λ (classicalTranslation h R) -
      classicalTranslation (Real.sqrt g • h) (Λ R)‖ ≤ b h * ‖R‖)
    (X : TraceClass H) (hX : 0 ≤ X.1) :
    (traceCLM (weightedQuantumMap Λ.toLinearMap (GaussianAffinity.productDensity a)
      (GaussianAffinity.integrable_productDensity a ha)
      (GaussianAffinity.productWitness a (fun i => a i / g)) hχ hbound X)).re ≤
      (Thermal.classicalBase g ^ ((k : ℝ) / 2) +
        C * (∫ h, GaussianAffinity.productDensity a h * b h)) * (traceCLM X).re := by
  let G := GaussianAffinity.productDensity a
  let χ := GaussianAffinity.productWitness a (fun i => a i / g)
  let Q := weightedL1Trace (H := K) χ hχ hbound
  let U (n : ℕ) := prepareL1 (classicalApproxDensity k n)
    (integrable_classicalApproxDensity k n) X
  have hUn (n : ℕ) : ‖U n‖ = ‖X‖ :=
    norm_prepareL1 _ _ (classicalApproxDensity_nonneg k n)
      (integral_classicalApproxDensity k n) X
  have hUp (n : ℕ) : ∀ᵐ y ∂volume, 0 ≤ (U n y).1 :=
    prepareL1_nonneg _ _ (classicalApproxDensity_nonneg k n) X hX
  have hLn (n : ℕ) : ‖Λ (U n)‖ = ‖X‖ :=
    (hΛ.norm_map_of_nonneg hTP (U n) (hUp n)).trans (hUn n)
  have hboundn (n : ℕ) : Q (Λ (classicalAverage G (U n))) ≤
      (Thermal.classicalBase g ^ ((k : ℝ) / 2) + C * (∫ h, G h * b h)) *
        (traceCLM X).re := by
    have ht := weightedL1Trace_gaussian_average_le Λ a ha hg hχ hC hbound b hb herror (U n)
    rw [hLn n, hUn n, TraceClass.norm_eq_trace_re_of_nonneg X hX] at ht
    exact ht.trans_eq (by dsimp only [G]; rw [traceCLM_apply]; ring)
  have hlim : Tendsto (fun n => Q (Λ (classicalAverage G (U n)))) atTop
      (𝓝 (Q (Λ (prepareL1 G (GaussianAffinity.integrable_productDensity a ha) X)))) :=
    (Q.continuous.comp Λ.continuous).continuousAt.tendsto.comp
      (classicalAverage_prepareApprox_tendsto G (GaussianAffinity.integrable_productDensity a ha) X)
  exact le_of_tendsto_of_tendsto hlim tendsto_const_nhds (Eventually.of_forall hboundn)

/-- Dominated convergence discharges the Gaussian-averaged covariance error. -/
theorem tendsto_gaussian_covariance_error_zero
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (C : ℝ)
    (b : ℕ → (Fin k → ℝ) → ℝ)
    (hb : ∀ n, AEStronglyMeasurable (b n) volume)
    {B : ℝ} (hbound : ∀ n h, ‖b n h‖ ≤ B)
    (hlim : ∀ h, Tendsto (fun n => b n h) atTop (𝓝 0)) :
    Tendsto (fun n => C * (∫ h, GaussianAffinity.productDensity a h * b n h))
      atTop (𝓝 0) := by
  have hG := GaussianAffinity.integrable_productDensity a ha
  have ht : Tendsto (fun n => ∫ h, GaussianAffinity.productDensity a h * b n h)
      atTop (𝓝 (∫ _h : Fin k → ℝ, (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence
      (fun h => GaussianAffinity.productDensity a h * B)
      (fun n => hG.aestronglyMeasurable.mul (hb n)) (hG.mul_const B)
    · intro n
      exact Eventually.of_forall fun h => by
        rw [Pi.mul_apply, norm_mul, Real.norm_of_nonneg (GaussianAffinity.productDensity_nonneg a h)]
        exact mul_le_mul_of_nonneg_left (hbound n h)
          (GaussianAffinity.productDensity_nonneg a h)
    · exact Eventually.of_forall fun h => by
        simpa using (hlim h).const_mul (GaussianAffinity.productDensity a h)
  simpa using ht.const_mul C

/-- The residual trace factor is eventually at most the sharp classical
factor plus any positive tolerance, uniformly over every positive input. -/
theorem eventually_weightedQuantumMap_gaussian_trace_le
    (Λ : ℕ → Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ)) →L[ℂ]
      Lp (TraceClass K) 1 (volume : Measure (Fin k → ℝ)))
    (hΛ : ∀ n, L1CompletelyPositive (Λ n).toLinearMap)
    (hTP : ∀ n, L1TracePreserving (Λ n).toLinearMap)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) {g : ℝ} (hg : 1 ≤ g)
    (hχ : AEStronglyMeasurable
      (GaussianAffinity.productWitness a (fun i => a i / g)) volume)
    {C : ℝ} (hC : 0 ≤ C) (hχbound : ∀ y,
      ‖GaussianAffinity.productWitness a (fun i => a i / g) y‖ ≤ C)
    (b : ℕ → (Fin k → ℝ) → ℝ)
    (hb : ∀ n, AEStronglyMeasurable (b n) volume)
    {B : ℝ} (hbbound : ∀ n h, ‖b n h‖ ≤ B)
    (hlim : ∀ h, Tendsto (fun n => b n h) atTop (𝓝 0))
    (herror : ∀ n h R, ‖Λ n (classicalTranslation h R) -
      classicalTranslation (Real.sqrt g • h) (Λ n R)‖ ≤ b n h * ‖R‖) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ X : TraceClass H, 0 ≤ X.1 →
      (traceCLM (weightedQuantumMap (Λ n).toLinearMap (GaussianAffinity.productDensity a)
        (GaussianAffinity.integrable_productDensity a ha)
        (GaussianAffinity.productWitness a (fun i => a i / g)) hχ hχbound X)).re ≤
        (Thermal.classicalBase g ^ ((k : ℝ) / 2) + ε) * (traceCLM X).re := by
  intro ε hε
  have ht := tendsto_gaussian_covariance_error_zero a ha C b hb hbbound hlim
  have he := ht.eventually_lt_const hε
  filter_upwards [he] with n hn
  intro X hX
  have hbi : Integrable (fun h => GaussianAffinity.productDensity a h * b n h) :=
    (GaussianAffinity.integrable_productDensity a ha).mul_bdd (hb n)
      (Eventually.of_forall (hbbound n))
  apply (weightedQuantumMap_gaussian_trace_le (Λ n) (hΛ n) (hTP n) a ha hg
    hχ hC hχbound (b n) hbi (herror n) X hX).trans
  exact mul_le_mul_of_nonneg_right (add_le_add le_rfl hn.le)
    (trace_re_nonneg hX X.2)

end Cloning.Hybrid
