import Cloning.HybridWeightedFidelity
import Cloning.InfiniteFidelityRegularizedLimit

/-! The full weighted hybrid fidelity lemma for arbitrary positive trace-class
targets. The inverse moment is its literal finite regularization limit, and
neither the quantum target nor the classical density needs normalization. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Each regularized inverse is an actual bounded operator. -/
def regularizedInverseMoment (T : PositiveTraceClass H) (W : H→L[ℂ] H) (ε : ℝ) : ℝ :=
  witnessMoment T.1 (CFC.rpow (regularizedWeight W ε) (-1))

theorem regularizedInverseMoment_nonneg (T : PositiveTraceClass H) (W : H→L[ℂ] H) (ε : ℝ) :
    0≤regularizedInverseMoment T W ε := witnessMoment_nonneg T CFC.rpow_nonneg

theorem regularizedInverseMoment_limit_nonneg (T : PositiveTraceClass H)
    (W : H→L[ℂ] H) {M : ℝ}
    (hInv : Tendsto (regularizedInverseMoment T W) (𝓝[>] (0:ℝ)) (𝓝 M)) : 0≤M :=
  le_of_tendsto_of_tendsto tendsto_const_nhds hInv
    (Eventually.of_forall (regularizedInverseMoment_nonneg T W))

namespace PositiveField

/-- Literal g(y) T for any positive trace-class T, including zero. -/
def productPositive (g : Ω→ℝ) (hg : Integrable g μ) (hgn : ∀x,0≤g x)
    (T : PositiveTraceClass H) : PositiveField (H:=H) μ where
  value x := PositiveTraceClass.scale (Real.toNNReal (g x)) T
  measurable := (PositiveTraceClass.continuous_scale _).comp_aestronglyMeasurable
    (continuous_real_toNNReal.comp_aestronglyMeasurable hg.aestronglyMeasurable)
  integrable := by
    have h := (Complex.ofRealCLM.integrable_comp hg).smul_const T.1
    simpa only [PositiveTraceClass.scale,Real.coe_toNNReal _ (hgn _)] using h

@[simp] theorem productPositive_value (g : Ω→ℝ) (hg : Integrable g μ) (hgn : ∀x,0≤g x)
    (T : PositiveTraceClass H) (x : Ω) :
    ((productPositive g hg hgn T).value x).1=(g x:ℂ) • T.1 := by
  simp only [productPositive,PositiveTraceClass.scale,Real.coe_toNNReal _ (hgn _)]

theorem rootFidelity_productPositive_sq_le (R : PositiveField (H:=H) μ)
    (g : Ω→ℝ) (hg : Integrable g μ) (hgn : ∀x,0≤g x) (T : PositiveTraceClass H)
    {W : H→L[ℂ] H} (hW : 0≤W) {M : ℝ}
    (hInv : Tendsto (regularizedInverseMoment T W) (𝓝[>] (0:ℝ)) (𝓝 M)) (x : Ω) :
    PositiveTraceClass.rootFidelity (R.value x) ((productPositive g hg hgn T).value x)^2≤
      witnessMoment (R.value x).1 W*(g x*M) := by
  apply fidelity_sq_le_of_regularized_inverse_limit (R.value x).2
    ((productPositive g hg hgn T).value x).2 hW (R.value x).1.2
    ((productPositive g hg hgn T).value x).1.2
  have h := hInv.const_mul (g x)
  convert h using 1
  ext ε
  change witnessMoment ((productPositive g hg hgn T).value x).1
    (CFC.rpow (regularizedWeight W ε) (-1))=g x*regularizedInverseMoment T W ε
  rw [productPositive_value,witnessMoment_real_smul]
  rfl

/-- The manuscript's weighted-hybrid bound with its precise finite-limit
hypothesis and arbitrary positive trace-class T. The integrability assumptions
express the finite RHS. The statement also permits unnormalized g. -/
theorem rootFidelity_sq_le_weighted_productPositive_of_inverse_limit
    (R : PositiveField (H:=H) μ)
    (g : Ω→ℝ) (hg : Integrable g μ) (hgn : ∀x,0≤g x) (T : PositiveTraceClass H)
    {W : H→L[ℂ] H} (hW : 0≤W) {M : ℝ}
    (hInv : Tendsto (regularizedInverseMoment T W) (𝓝[>] (0:ℝ)) (𝓝 M))
    (χ : Ω→ℝ) (hχ : ∀x,0<χ x)
    (hweighted : Integrable (fun x=>χ x*witnessMoment (R.value x).1 W) μ)
    (hclassical : Integrable (fun x=>g x/χ x) μ) :
    R.rootFidelity (productPositive g hg hgn T)^2≤
      (∫x,χ x*witnessMoment (R.value x).1 W ∂μ)*
      (∫x,g x/χ x ∂μ)*M := by
  have hM := regularizedInverseMoment_limit_nonneg T W hInv
  let f : Ω→ℝ := fun x=>χ x*witnessMoment (R.value x).1 W
  let k : Ω→ℝ := fun x=>g x/χ x
  have hfn (x : Ω) : 0≤f x := mul_nonneg (hχ x).le (witnessMoment_nonneg _ hW)
  have hkn (x : Ω) : 0≤k x := div_nonneg (hgn x) (hχ x).le
  have hip := integrable_sqrt_mul_sqrt hweighted hclassical hfn hkn
  have hpoint (x : Ω) :
      PositiveTraceClass.rootFidelity (R.value x) ((productPositive g hg hgn T).value x)≤
        Real.sqrt (f x)*Real.sqrt (k x)*Real.sqrt M := by
    have hsq := rootFidelity_productPositive_sq_le R g hg hgn T hW hInv x
    have heq : f x*k x*M=witnessMoment (R.value x).1 W*(g x*M) := by
      dsimp [f,k]
      field_simp [ne_of_gt (hχ x)]
    have hsqrt : (Real.sqrt (f x)*Real.sqrt (k x)*Real.sqrt M)^2=
        witnessMoment (R.value x).1 W*(g x*M) := by
      rw [mul_pow,mul_pow,Real.sq_sqrt (hfn x),Real.sq_sqrt (hkn x),Real.sq_sqrt hM]
      exact heq
    have hpos := mul_nonneg (mul_nonneg (Real.sqrt_nonneg (f x))
      (Real.sqrt_nonneg (k x))) (Real.sqrt_nonneg M)
    nlinarith [PositiveTraceClass.rootFidelity_nonneg (R.value x) ((productPositive g hg hgn T).value x)]
  have hroot : R.rootFidelity (productPositive g hg hgn T)≤
      Real.sqrt (∫x,f x ∂μ)*Real.sqrt (∫x,k x ∂μ)*Real.sqrt M := by
    calc
      _≤∫x,Real.sqrt (f x)*Real.sqrt (k x)*Real.sqrt M ∂μ :=
        integral_mono (R.integrable_rootFidelity _) (hip.mul_const _) hpoint
      _=(∫x,Real.sqrt (f x)*Real.sqrt (k x) ∂μ)*Real.sqrt M := integral_mul_const _ _
      _≤_ := mul_le_mul_of_nonneg_right
        (integral_sqrt_mul_sqrt_le hweighted hclassical hfn hkn) (Real.sqrt_nonneg M)
  have hfint : 0≤∫x,f x ∂μ := integral_nonneg (fun x=>hfn x)
  have hkint : 0≤∫x,k x ∂μ := integral_nonneg (fun x=>hkn x)
  have hsquared := (sq_le_sq₀ (R.rootFidelity_nonneg _) (by positivity)).mpr hroot
  simpa only [mul_pow,Real.sq_sqrt hfint,Real.sq_sqrt hkint,Real.sq_sqrt hM] using hsquared

end PositiveField
end Cloning.Hybrid
