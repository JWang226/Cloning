import Cloning.HybridTranslation
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Actual L¹ classical averaging and approximate identities

Classical averaging is the Bochner integral of the strongly continuous
translation action on operator-valued L¹. Preparing either scalar factor and
averaging with the other gives the same L¹ class. Explicit normalized bumps
give an approximate identity in the L¹ norm.
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators Convolution
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {k : ℕ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual Bochner average of classical translations. -/
def classicalAverage (g : (Fin k → ℝ) → ℝ)
    (A : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ)) :=
  ∫ h, (g h : ℂ) • classicalTranslation h A

theorem integrable_classicalAverage_integrand (g : (Fin k → ℝ) → ℝ)
    (hg : Integrable g)
    (A : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    Integrable (fun h => (g h : ℂ) • classicalTranslation h A) := by
  apply (hg.norm.mul_const ‖A‖).mono'
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable hg.aestronglyMeasurable).smul
      (continuous_classicalTranslation A).aestronglyMeasurable)
  exact Eventually.of_forall fun h => by
    simp only [norm_smul, Complex.norm_real, norm_classicalTranslation, le_refl]

theorem norm_classicalAverage_le (g : (Fin k → ℝ) → ℝ)
    (A : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    ‖classicalAverage g A‖ ≤ (∫ h, |g h|) * ‖A‖ := by
  unfold classicalAverage
  calc
    _ ≤ ∫ h, ‖(g h : ℂ) • classicalTranslation h A‖ := norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_smul, Complex.norm_real, norm_classicalTranslation,
      Real.norm_eq_abs, integral_mul_const]

/-- Set integration is a continuous linear functional on operator-valued L¹. -/
def classicalSetIntegralCLM (s : Set (Fin k → ℝ)) :
    Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ)) →L[ℂ] TraceClass H :=
  LinearMap.mkContinuous
    { toFun := fun A => ∫ y in s, A y
      map_add' := fun A B => by
        rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add A B))]
        exact integral_add (L1.integrable_coeFn A).integrableOn
          (L1.integrable_coeFn B).integrableOn
      map_smul' := fun c A => by
        rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c A))]
        exact integral_smul c _ }
    1 (by
      intro A
      rw [one_mul, L1.norm_eq_integral_norm]
      exact (norm_integral_le_integral_norm _).trans
        (setIntegral_le_integral (L1.integrable_coeFn A).norm
          (Eventually.of_forall fun y => norm_nonneg (A y))))

theorem classicalSetIntegralCLM_apply (s : Set (Fin k → ℝ))
    (A : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    classicalSetIntegralCLM s A = ∫ y in s, A y := rfl

theorem classicalTranslation_prepareL1_ae (u : (Fin k → ℝ) → ℝ)
    (hu : Integrable u) (h : Fin k → ℝ) (X : TraceClass H) :
    classicalTranslation h (prepareL1 u hu X) =ᵐ[volume]
      fun y => (u (y - h) : ℂ) • X := by
  exact (classicalTranslation_ae h _).trans
    ((measurePreserving_sub_right volume h).quasiMeasurePreserving.ae (prepareL1_ae u hu X))

theorem setIntegral_classicalAverage_prepareL1
    (g u : (Fin k → ℝ) → ℝ) (hg : Integrable g) (hu : Integrable u)
    (X : TraceClass H) (s : Set (Fin k → ℝ)) :
    (∫ y in s, classicalAverage g (prepareL1 u hu X) y) =
      ∫ y in s, ∫ h, ((g h * u (y - h) : ℝ) : ℂ) • X := by
  have hscalar : Integrable
      (fun z : (Fin k → ℝ) × (Fin k → ℝ) => g z.2 * u (z.1 - z.2))
      (volume.prod volume) :=
    hg.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hu
  have hF := (Complex.ofRealCLM.integrable_comp hscalar).smul_const X
  have hFs : Integrable
      (fun z : (Fin k → ℝ) × (Fin k → ℝ) =>
        ((g z.2 * u (z.1 - z.2) : ℝ) : ℂ) • X)
      ((volume.restrict s).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hF.integrableOn
  calc
    _ = ∫ h, classicalSetIntegralCLM s
        ((g h : ℂ) • classicalTranslation h (prepareL1 u hu X)) :=
      ((classicalSetIntegralCLM s).integral_comp_comm
        (integrable_classicalAverage_integrand g hg _)).symm
    _ = ∫ h, ∫ y in s, ((g h * u (y - h) : ℝ) : ℂ) • X := by
      apply integral_congr_ae
      exact Eventually.of_forall fun h => by
        dsimp only
        rw [map_smul, classicalSetIntegralCLM_apply, ← integral_smul]
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (classicalTranslation_prepareL1_ae u hu h X)]
          with y hy
        rw [hy, smul_smul, Complex.ofReal_mul]
    _ = _ := integral_integral_swap hFs.swap

/-- Commutativity of scalar convolution holds as equality of actual
operator-valued L¹ averages, without choosing pointwise representatives of
their Bochner integrals. -/
theorem classicalAverage_prepareL1_comm
    (g u : (Fin k → ℝ) → ℝ) (hg : Integrable g) (hu : Integrable u)
    (X : TraceClass H) :
    classicalAverage g (prepareL1 u hu X) =
      classicalAverage u (prepareL1 g hg X) := by
  apply Lp.ext
  apply Lp.ae_eq_of_forall_setIntegral_eq _ _ (by simp) (by simp)
    (fun s _ _ => (L1.integrable_coeFn _).integrableOn)
    (fun s _ _ => (L1.integrable_coeFn _).integrableOn)
  intro s _ _
  rw [setIntegral_classicalAverage_prepareL1 g u hg hu,
    setIntegral_classicalAverage_prepareL1 u g hu hg]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [← integral_sub_left_eq_self
      (fun h : Fin k → ℝ => ((u h * g (y - h) : ℝ) : ℂ) • X) volume y]
    apply integral_congr_ae
    exact Eventually.of_forall fun h => by
      simp only [sub_sub_cancel, mul_comm]

/-- Inner and outer radii are respectively `1/(2(n+1))` and `1/(n+1)`. -/
def classicalApproxBump (k n : ℕ) : ContDiffBump (0 : Fin k → ℝ) where
  rIn := ((n : ℝ) + 1)⁻¹ / 2
  rOut := ((n : ℝ) + 1)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
    linarith

def classicalApproxDensity (k n : ℕ) : (Fin k → ℝ) → ℝ :=
  (classicalApproxBump k n).normed volume

theorem continuous_classicalApproxDensity (k n : ℕ) :
    Continuous (classicalApproxDensity k n) :=
  (classicalApproxBump k n).continuous_normed

theorem integrable_classicalApproxDensity (k n : ℕ) :
    Integrable (classicalApproxDensity k n) :=
  (classicalApproxBump k n).integrable_normed

theorem classicalApproxDensity_nonneg (k n : ℕ) (y : Fin k → ℝ) :
    0 ≤ classicalApproxDensity k n y :=
  (classicalApproxBump k n).nonneg_normed y

theorem integral_classicalApproxDensity (k n : ℕ) :
    (∫ y, classicalApproxDensity k n y) = 1 :=
  (classicalApproxBump k n).integral_normed

theorem classicalApproxDensity_support (k n : ℕ) :
    Function.support (classicalApproxDensity k n) =
      Metric.ball 0 (((n : ℝ) + 1)⁻¹) :=
  (classicalApproxBump k n).support_normed_eq

/-- Normalized compactly supported classical averages converge in actual L¹. -/
theorem classicalAverage_approx_tendsto
    (A : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    Tendsto (fun n => classicalAverage (classicalApproxDensity k n) A) atTop (𝓝 A) := by
  have hr : Tendsto (fun n : ℕ => (classicalApproxBump k n).rOut) atTop (𝓝 0) := by
    simpa only [classicalApproxBump, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hc : Continuous (fun x : Fin k → ℝ => classicalTranslation (-x) A) :=
    (continuous_classicalTranslation A).comp continuous_neg
  have ht := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hr hc 0
  simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub, neg_neg,
    neg_zero, classicalTranslation_zero, classicalAverage, classicalApproxDensity,
    Complex.coe_smul] using ht

/-- Averaging a prepared approximate delta against any integrable density
converges to preparation of that density, in the actual operator-valued L¹ norm. -/
theorem classicalAverage_prepareApprox_tendsto
    (g : (Fin k → ℝ) → ℝ) (hg : Integrable g) (X : TraceClass H) :
    Tendsto (fun n => classicalAverage g
      (prepareL1 (classicalApproxDensity k n) (integrable_classicalApproxDensity k n) X))
      atTop (𝓝 (prepareL1 g hg X)) := by
  have he (n : ℕ) := classicalAverage_prepareL1_comm g (classicalApproxDensity k n)
    hg (integrable_classicalApproxDensity k n) X
  simpa only [he] using classicalAverage_approx_tendsto (prepareL1 g hg X)

end Cloning.Hybrid
