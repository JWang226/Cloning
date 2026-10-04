import Cloning.HybridCovariantization
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure

/-! Expanding genuine densities on the joint classical and quantum phase
space. Translation error is continuous, uniformly bounded, and tends to zero. -/
noncomputable section
open scoped Topology
open Filter MeasureTheory
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k s : ℕ}

instance phaseSpaceVolume_addLeftInvariant :
    (volume : Measure (PhaseSpace k s)).IsAddLeftInvariant :=
  Measure.prod.instIsAddLeftInvariant

structure PhaseDensity (k s : ℕ) where
  value : PhaseSpace k s → ℝ
  measurable : Measurable value
  nonneg : ∀ ξ, 0 ≤ value ξ
  integral_one : (∫ ξ, value ξ) = 1

namespace PhaseDensity
variable (p : PhaseDensity k s)
lemma integrable : Integrable p.value := integrable_of_integral_eq_one p.integral_one

def prior : Measure (PhaseSpace k s) := volume.withDensity (fun ξ => ENNReal.ofReal (p.value ξ))
instance prior_probability : IsProbabilityMeasure p.prior := by
  constructor
  rw [prior, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal p.integrable
    (Eventually.of_forall p.nonneg), p.integral_one]
  exact ENNReal.ofReal_one

def expandingPrior (n : ℕ) : Measure (PhaseSpace k s) :=
  p.prior.map (fun ξ => ((n : ℝ) + 1) • ξ)
instance expandingPrior_probability (n : ℕ) : IsProbabilityMeasure (p.expandingPrior n) := by
  unfold expandingPrior
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma integral_expandingPrior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : PhaseSpace k s → E) (hf : Continuous f) :
    (∫ ξ, f ξ ∂p.expandingPrior n) = ∫ z, p.value z • f (((n : ℝ) + 1) • z) := by
  rw [expandingPrior, integral_map (by fun_prop) hf.aestronglyMeasurable]
  rw [prior, integral_withDensity_eq_integral_toReal_smul p.measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (p.nonneg _)]

lemma integral_expandingPrior_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (b : PhaseSpace k s) (f : PhaseSpace k s → E) (hf : Continuous f) :
    (∫ ξ, f (ξ + b) ∂p.expandingPrior n) =
      ∫ z, p.value (-(((n : ℝ) + 1)⁻¹ • b) + z) • f (((n : ℝ) + 1) • z) := by
  rw [p.integral_expandingPrior n (fun a => f (a + b))
    (hf.comp (continuous_id.add continuous_const))]
  rw [← integral_add_left_eq_self
    (fun z => p.value z • f (((n : ℝ) + 1) • z + b)) (-(((n : ℝ) + 1)⁻¹ • b))]
  congr 1
  funext z
  congr 1
  congr 1
  have hn : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  rw [smul_add, smul_neg, smul_smul, mul_inv_cancel₀ hn, one_smul]
  abel

/-- Literal L¹ distance of the density from its translate. -/
def translationError (b : PhaseSpace k s) : ℝ := ∫ z, |p.value (b + z) - p.value z|

lemma translationError_nonneg (b : PhaseSpace k s) : 0 ≤ p.translationError b :=
  integral_nonneg fun _ => abs_nonneg _

lemma translationError_le_two (b : PhaseSpace k s) : p.translationError b ≤ 2 := by
  have hi : Integrable (fun z => p.value (b + z)) :=
    (measurePreserving_add_left volume b).integrable_comp_of_integrable p.integrable
  have h := integral_mono (hi.sub p.integrable).abs (hi.add p.integrable) (fun z => by
    exact (abs_sub (p.value (b + z)) (p.value z)).trans_eq
      (by rw [abs_of_nonneg (p.nonneg _), abs_of_nonneg (p.nonneg _)]; rfl))
  change (∫ z, |p.value (b + z) - p.value z|) ≤ ∫ z, p.value (b + z) + p.value z at h
  rw [integral_add hi p.integrable, integral_add_left_eq_self, p.integral_one] at h
  norm_num at h
  exact h

lemma continuous_translationError : Continuous p.translationError := by
  let f : Lp ℝ 1 (volume : Measure (PhaseSpace k s)) := p.integrable.toL1 p.value
  let shifts : C(PhaseSpace k s, C(PhaseSpace k s, PhaseSpace k s)) :=
    (ContinuousMap.mk (fun z : PhaseSpace k s × PhaseSpace k s => z.1 + z.2) continuous_add).curry
  have hm (b : PhaseSpace k s) : MeasurePreserving (shifts b) volume volume :=
    measurePreserving_add_left volume b
  have hc : Continuous (fun b => Lp.compMeasurePreserving (shifts b) (hm b) f) :=
    continuous_const.compMeasurePreservingLp shifts.continuous hm (by norm_num)
  have he (b : PhaseSpace k s) : ‖Lp.compMeasurePreserving (shifts b) (hm b) f - f‖ =
      p.translationError b := by
    have hi := (hm b).integrable_comp_of_integrable p.integrable
    change ‖hi.toL1 (fun z => p.value (b + z)) - p.integrable.toL1 p.value‖ = _
    rw [← Integrable.toL1_sub, L1.norm_of_fun_eq_integral_norm]
    simp only [Pi.sub_apply, Real.norm_eq_abs, translationError]
  exact (hc.sub continuous_const).norm.congr (fun b => he b)

@[simp] lemma translationError_zero : p.translationError 0 = 0 := by
  simp [translationError]

/-- A uniform whole-space covariance coefficient for the actual averages. -/
def covarianceError (n : ℕ) (b : PhaseSpace k s) : ℝ :=
  2 * p.translationError (-(((n : ℝ) + 1)⁻¹ • b))

lemma covarianceError_nonneg (n : ℕ) (b : PhaseSpace k s) : 0 ≤ p.covarianceError n b :=
  mul_nonneg (by norm_num) (p.translationError_nonneg _)

lemma covarianceError_le_four (n : ℕ) (b : PhaseSpace k s) : p.covarianceError n b ≤ 4 := by
  unfold covarianceError
  linarith [p.translationError_le_two (-(((n : ℝ) + 1)⁻¹ • b))]

lemma continuous_covarianceError (n : ℕ) : Continuous (p.covarianceError n) :=
  continuous_const.mul (p.continuous_translationError.comp (by fun_prop))

lemma covarianceError_tendsto (b : PhaseSpace k s) :
    Tendsto (fun n => p.covarianceError n b) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hb : Tendsto (fun n : ℕ => -(((n : ℝ) + 1)⁻¹ • b)) atTop (𝓝 0) := by
    simpa only [zero_smul, neg_zero] using (hi.smul_const b).neg
  simpa [covarianceError] using (p.continuous_translationError.tendsto 0 |>.comp hb).const_mul 2

end PhaseDensity
end Cloning.Hybrid
