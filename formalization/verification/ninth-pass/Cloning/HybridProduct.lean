import Cloning.HybridFidelity

/-! Product classical–quantum densities and their exact normalization. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace PositiveTraceClass
/-- Multiplying a positive trace-class fibre by a nonnegative scalar. -/
def scale (a : NNReal) (A : PositiveTraceClass H) : PositiveTraceClass H :=
  ⟨((a : ℝ) : ℂ) • A.1, by
    change 0 ≤ ((a : ℝ) : ℂ) • A.1.1
    rw [Complex.coe_smul]
    exact smul_nonneg a.2 A.2⟩

lemma continuous_scale (A : PositiveTraceClass H) : Continuous (fun a : NNReal => scale a A) := by
  apply Continuous.subtype_mk
  exact (Complex.continuous_ofReal.comp continuous_subtype_val).smul continuous_const

@[simp] lemma norm_scale (a : NNReal) (A : PositiveTraceClass H) :
    ‖(scale a A).1‖ = (a : ℝ) * ‖A.1‖ := by
  rw [scale, norm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (NNReal.coe_nonneg a)]

end PositiveTraceClass

namespace PositiveField
/-- The actual hybrid product state `g(y) T`; the density is an integrable
real-valued nonnegative function and `T` is a genuine quantum density operator. -/
def product (g : Ω → ℝ) (hg : Integrable g μ) (hgn : ∀ x, 0 ≤ g x)
    (T : DensityState H) : PositiveField (H := H) μ where
  value := fun x => PositiveTraceClass.scale (Real.toNNReal (g x))
    ⟨TraceClass.ofOperator T.op T.traceClass, T.positive⟩
  measurable := (PositiveTraceClass.continuous_scale _).comp_aestronglyMeasurable
    (continuous_real_toNNReal.comp_aestronglyMeasurable hg.aestronglyMeasurable)
  integrable := by
    have h := (Complex.ofRealCLM.integrable_comp hg).smul_const
      (TraceClass.ofOperator T.op T.traceClass)
    simpa only [PositiveTraceClass.scale, Real.coe_toNNReal _ (hgn _)] using h

@[simp] lemma product_value (g : Ω → ℝ) (hg : Integrable g μ) (hgn : ∀ x, 0 ≤ g x)
    (T : DensityState H) (x : Ω) :
    ((product g hg hgn T).value x).1 = (g x : ℂ) • TraceClass.ofOperator T.op T.traceClass := by
  simp only [product, PositiveTraceClass.scale, Real.coe_toNNReal _ (hgn _)]

@[simp] lemma mass_product (g : Ω → ℝ) (hg : Integrable g μ) (hgn : ∀ x, 0 ≤ g x)
    (T : DensityState H) : (product g hg hgn T).mass = ∫ x, g x ∂μ := by
  unfold mass
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [product_value, norm_smul, TraceClass.norm_eq_trace_re_of_nonneg _ T.positive]
    simp only [TraceClass.ofOperator_coe, T.trace_one, Complex.one_re, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hgn x)]

/-- A classical probability density times a quantum state has total trace one. -/
lemma mass_product_one (g : Ω → ℝ) (hg : Integrable g μ) (hgn : ∀ x, 0 ≤ g x)
    (T : DensityState H) (hprob : ∫ x, g x ∂μ = 1) : (product g hg hgn T).mass = 1 := by
  rwa [mass_product]

end PositiveField
end Cloning.Hybrid
