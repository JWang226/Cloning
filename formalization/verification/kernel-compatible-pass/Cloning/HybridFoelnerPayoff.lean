import Cloning.HybridFoelnerThermal

/-! Weighted fidelity of the actual hybrid channel output, with exact L¹
preparation and weighted marginal identifications. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass
open Cloning.MultimodeCoherent Cloning.MultimodeCoherentGaussianMixture Cloning.ThermalWitness
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma PositiveField.weightedMarginal_eq_weightedL1Integral
    (R : PositiveField (H := H) μ) (χ : Ω → ℝ)
    (hχ : AEStronglyMeasurable χ μ) {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C) :
    R.weightedMarginal χ = weightedL1Integral χ hχ hbound R.toL1 := by
  apply integral_congr_ae
  filter_upwards [R.coe_toL1] with y hy
  rw [hy]

lemma PositiveField.product_toL1_eq_prepareL1
    (G : Ω → ℝ) (hG : Integrable G μ) (hG0 : ∀ y, 0 ≤ G y) (T : DensityState H) :
    (PositiveField.product G hG hG0 T).toL1 =
      prepareL1 G hG (TraceClass.ofOperator T.op T.traceClass) := by
  apply Lp.ext
  filter_upwards [(PositiveField.product G hG hG0 T).coe_toL1,
    prepareL1_ae G hG (TraceClass.ofOperator T.op T.traceClass)] with y hy hz
  rw [hy, hz, PositiveField.product_value]

variable {k s : ℕ}

/-- The actual centered Gaussian--thermal density shared by the input and
target of the hybrid model. -/
def gaussianThermalField (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    PositiveField (H := Fock s) (volume : Measure (Fin k → ℝ)) :=
  PositiveField.product (GaussianAffinity.productDensity a)
    (GaussianAffinity.integrable_productDensity a ha)
    (GaussianAffinity.productDensity_nonneg a)
    (InfiniteDiagonalFidelity.productGeometricState (numberBasis s) q hq0 hq1)

lemma gaussianThermalField_toL1 (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    (gaussianThermalField a ha q hq0 hq1).toL1 =
      prepareL1 (GaussianAffinity.productDensity a) (GaussianAffinity.integrable_productDensity a ha)
        (vectorMixture (numberBasis s) (productGeometric q)) := by
  rw [gaussianThermalField, PositiveField.product_toL1_eq_prepareL1]
  rfl

lemma weightedMarginal_channel_gaussianThermal_eq
    (Λ : Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ)) →ₗ[ℂ]
      Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ)))
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (R : PositiveField (H := Fock s) (volume : Measure (Fin k → ℝ)))
    (hR : R.toL1 = Λ (gaussianThermalField a ha q hq0 hq1).toL1)
    (χ : (Fin k → ℝ) → ℝ) (hχ : AEStronglyMeasurable χ volume)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C) :
    R.weightedMarginal χ = weightedQuantumMap Λ
      (GaussianAffinity.productDensity a) (GaussianAffinity.integrable_productDensity a ha)
      χ hχ hbound (vectorMixture (numberBasis s) (productGeometric q)) := by
  rw [R.weightedMarginal_eq_weightedL1Integral χ hχ hbound, hR, gaussianThermalField_toL1]
  rfl

/-- The concrete weighted fidelity inequality of an actual hybrid output
uses precisely the quantum map extracted from the same channel. -/
theorem gaussianThermal_output_rootFidelity_sq_le
    (Λ : Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ)) →ₗ[ℂ]
      Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ)))
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (R : PositiveField (H := Fock s) (volume : Measure (Fin k → ℝ)))
    (hR : R.toL1 = Λ (gaussianThermalField a ha q (fun i => (hq0 i).le) hq1).toL1)
    (hχ : AEStronglyMeasurable
      (GaussianAffinity.productWitness a (fun i => a i / g)) volume)
    {C : ℝ} (hbound : ∀ y,
      ‖GaussianAffinity.productWitness a (fun i => a i / g) y‖ ≤ C) :
    R.rootFidelity (gaussianThermalField a ha q (fun i => (hq0 i).le) hq1) ^ 2 ≤
      (tracePairing (weightedQuantumMap Λ (GaussianAffinity.productDensity a)
        (GaussianAffinity.integrable_productDensity a ha)
        (GaussianAffinity.productWitness a (fun i => a i / g)) hχ hbound
        (vectorMixture (numberBasis s) (productGeometric q)))
        (productWitnessOperator (numberBasis s) q (fun i => Thermal.amplified g (q i)))).re *
      Thermal.classicalBase g ^ ((k : ℝ) / 2) *
        ∏ i, Thermal.fidelity (q i) (Thermal.amplified g (q i)) := by
  have h := R.rootFidelity_sq_le_gaussian_thermal a ha hg.le (numberBasis s) q
    (fun i => Thermal.amplified g (q i)) hq0
    (fun i => Thermal.lt_amplified hg (hq1 i))
    (fun i => Thermal.amplified_lt_one (by linarith) (hq1 i))
  rw [weightedMarginal_channel_gaussianThermal_eq Λ a ha q _ hq1 R hR _ hχ hbound] at h
  exact h

/-- Every asymptotically covariant sequence of genuine hybrid channels has
eventually at most the sharp Gaussian--thermal root-fidelity payoff. The
channels can vary independently with the scale. -/
theorem eventually_gaussianThermal_output_rootFidelity_le
    (Λ : ℕ → Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ)) →L[ℂ]
      Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ)))
    (hΛ : ∀ n, L1CompletelyPositive (Λ n).toLinearMap)
    (hTP : ∀ n, L1TracePreserving (Λ n).toLinearMap)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (b : ℕ → (Fin k → ℝ) → ℝ)
    (hb : ∀ n, AEStronglyMeasurable (b n) volume)
    {B : ℝ} (hbbound : ∀ n h, ‖b n h‖ ≤ B)
    (hlim : ∀ h, Tendsto (fun n => b n h) atTop (𝓝 0))
    (hclassical : ∀ n h R, ‖Λ n (classicalTranslation h R) -
      classicalTranslation (Real.sqrt g • h) (Λ n R)‖ ≤ b n h * ‖R‖)
    (hquantum : ∀ z R, Tendsto (fun n =>
      ‖Λ n (quantumL1Action z R) - quantumL1Action (Real.sqrt g • z) (Λ n R)‖)
        atTop (𝓝 0))
    (R : ℕ → PositiveField (H := Fock s) (volume : Measure (Fin k → ℝ)))
    (hR : ∀ n, (R n).toL1 = Λ n
      (gaussianThermalField a ha q (fun i => (hq0 i).le) hq1).toL1) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      (R n).rootFidelity (gaussianThermalField a ha q (fun i => (hq0 i).le) hq1) ≤
        Thermal.classicalBase g ^ ((k : ℝ) / 2) *
          (∏ i, Thermal.fidelity (q i) (Thermal.amplified g (q i))) + ε := by
  classical
  let χ := GaussianAffinity.productWitness a (fun i => a i / g)
  let C := ∏ i, Real.sqrt (Real.sqrt (a i) / Real.sqrt (a i / g))
  have hg0 : 0 < g := by linarith
  have hχ : AEStronglyMeasurable χ volume :=
    (GaussianAffinity.continuous_productWitness a _ ha
      (fun i => div_pos (ha i) hg0)).aestronglyMeasurable
  have hC : 0 ≤ C := Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hχbound (y : Fin k → ℝ) : ‖χ y‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_of_pos
      (GaussianAffinity.productWitness_pos a _ ha (fun i => div_pos (ha i) hg0) y)]
    apply GaussianAffinity.productWitness_le a _ ha (fun i => div_pos (ha i) hg0)
    intro i
    exact (div_le_iff₀ hg0).mpr (by nlinarith [ha i])
  let ck := Thermal.classicalBase g ^ ((k : ℝ) / 2)
  let F := ∏ i, Thermal.fidelity (q i) (Thermal.amplified g (q i))
  have hck : 0 ≤ ck := Real.rpow_nonneg (Thermal.classicalBase_pos hg0).le _
  have hF : 0 ≤ F := Finset.prod_nonneg (fun i _ =>
    (Thermal.fidelity_pos (hq0 i).le (hq1 i)
      ((hq0 i).trans (Thermal.lt_amplified hg (hq1 i))).le
      (Thermal.amplified_lt_one hg0 (hq1 i))).le)
  let W := productWitnessOperator (numberBasis s) q (fun i => Thermal.amplified g (q i))
  have hW : IsCompactOperator W := productWitnessOperator_compact _ hq0
    (fun i => Thermal.lt_amplified hg (hq1 i))
    (fun i => Thermal.amplified_lt_one hg0 (hq1 i))
  let τ := vectorMixture (numberBasis s) (productGeometric q)
  intro ε hε
  by_contra h
  have hf : ∃ᶠ n in atTop, ck * F + ε <
      (R n).rootFidelity (gaussianThermalField a ha q (fun i => (hq0 i).le) hq1) := by
    simpa only [Filter.Frequently, not_lt, ck, F] using h
  obtain ⟨scale, hscale, hbad⟩ := exists_seq_forall_of_frequently hf
  obtain ⟨Γ, hΓ, htrace, hcov, φ, hφ, hcompact⟩ :=
    exists_gaussian_weighted_covariant_residual (fun n => Λ (scale n))
      (fun n => hΛ (scale n)) (fun n => hTP (scale n)) a ha hg.le hχ hC hχbound
      (fun n => b (scale n)) (fun n => hb (scale n))
      (fun n h => hbbound (scale n) h) (fun h => (hlim h).comp hscale)
      (fun n => hclassical (scale n)) (fun z A => (hquantum z A).comp hscale)
  have hmoment : (tracePairing (Γ τ) W).re ≤ ck * F :=
    hybrid_residual_thermal_witness_moment_le Γ hΓ g hg htrace hcov hq0 hq1
  have hmomentMul : (tracePairing (Γ τ) W).re * ck * F ≤ (ck * F) ^ 2 := by
    have ht := mul_le_mul_of_nonneg_right hmoment (mul_nonneg hck hF)
    nlinarith
  have hlimM := (((Complex.continuous_re.tendsto _).comp (hcompact τ W hW)).mul_const ck).mul_const F
  have hnear := hlimM.eventually_lt_const
    (lt_add_of_pos_right _ (show 0 < ε ^ 2 / 2 by positivity))
  obtain ⟨n, hn⟩ := hnear.exists
  have hweighted := gaussianThermal_output_rootFidelity_sq_le
    (Λ (scale (φ n))).toLinearMap a ha g hg q hq0 hq1 (R (scale (φ n)))
    (hR (scale (φ n))) hχ hχbound
  have hbadn := hbad (φ n)
  have hsq := (sq_lt_sq₀ (add_nonneg (mul_nonneg hck hF) hε.le)
    ((R (scale (φ n))).rootFidelity_nonneg _)).mpr hbadn
  change _ < (tracePairing (Γ τ) W).re * ck * F + ε ^ 2 / 2 at hn
  change (R (scale (φ n))).rootFidelity
      (gaussianThermalField a ha q (fun i => (hq0 i).le) hq1) ^ 2 ≤
    (tracePairing _ W).re * ck * F at hweighted
  dsimp only [Function.comp_apply, τ] at hn
  nlinarith [mul_nonneg (mul_nonneg hck hF) hε.le]

end Cloning.Hybrid
