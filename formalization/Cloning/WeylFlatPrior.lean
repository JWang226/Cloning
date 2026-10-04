import Cloning.WeylFoelner

/-! Expanding flat priors on arbitrary finite positive-volume phase-space
regions. The Følner property is derived from L1 translation continuity, so it
applies in particular to boxes and requires no assumed boundary estimate. -/
noncomputable section
open scoped ComplexOrder BigOperators Topology
open Filter MeasureTheory
namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

/-- An actual nonnegative unit-mass phase-space density. -/
structure PhaseSpaceDensity (d : ℕ) where
  value : (Fin d → ℂ) → ℝ
  measurable : Measurable value
  nonneg : ∀ a, 0 ≤ value a
  integral_one : (∫ a, value a) = 1

namespace PhaseSpaceDensity
variable (p : PhaseSpaceDensity d)

lemma integrable : Integrable p.value := integrable_of_integral_eq_one p.integral_one

def prior : Measure (Fin d → ℂ) := volume.withDensity (fun a => ENNReal.ofReal (p.value a))

instance prior_probability : IsProbabilityMeasure p.prior := by
  constructor
  rw [prior, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal p.integrable
    (Eventually.of_forall p.nonneg), p.integral_one]
  exact ENNReal.ofReal_one

def expandingPrior (n : ℕ) : Measure (Fin d → ℂ) :=
  p.prior.map (fun a => ((n : ℝ) + 1) • a)

instance expandingPrior_probability (n : ℕ) : IsProbabilityMeasure (p.expandingPrior n) := by
  unfold expandingPrior
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma integral_expandingPrior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : (Fin d → ℂ) → E) (hf : Continuous f) :
    (∫ a, f a ∂p.expandingPrior n) =
      ∫ z, p.value z • f (((n : ℝ) + 1) • z) := by
  rw [expandingPrior, integral_map (by fun_prop) hf.aestronglyMeasurable]
  rw [prior, integral_withDensity_eq_integral_toReal_smul p.measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (p.nonneg _)]

lemma integral_expandingPrior_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (b : Fin d → ℂ) (f : (Fin d → ℂ) → E) (hf : Continuous f) :
    (∫ a, f (a + b) ∂p.expandingPrior n) =
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

lemma translation_error_tendsto (b : Fin d → ℂ) :
    Tendsto (fun n : ℕ => ∫ x, |p.value (-(((n : ℝ) + 1)⁻¹ • b) + x) - p.value x|)
      atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h' : Tendsto (fun n : ℕ => -(((n : ℝ) + 1)⁻¹ • b)) atTop (𝓝 0) := by
    simpa only [zero_smul, neg_zero] using (hi.smul_const b).neg
  exact (integral_abs_translate_sub_tendsto p.value p.integrable).comp h'

/-- Actual CPTP averages under the chosen expanding density. -/
def foelnerChannel (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (n : ℕ) : QuantumChannel (Fock d) (Fock d) := covariantAverage (p.expandingPrior n) gain Φ

lemma foelnerChannel_covariance_bound (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (b : Fin d → ℂ) (A : TraceClass (Fock d)) (hA : 0 ≤ A.1) (n : ℕ) :
    ‖(p.foelnerChannel gain Φ n).toLinearMap (displacementTraceMap b A) -
      displacementTraceMap (gain • b) ((p.foelnerChannel gain Φ n).toLinearMap A)‖ ≤
      ‖A‖ * ∫ z, |p.value (-(((n : ℝ) + 1)⁻¹ • b) + z) - p.value z| := by
  let f : (Fin d → ℂ) → TraceClass (Fock d) :=
    fun a => (translatedChannel gain Φ a).toLinearMap A
  have hf : Continuous f := continuous_translatedChannel gain Φ A
  change ‖(covariantAverage (p.expandingPrior n) gain Φ).toLinearMap
    (displacementTraceMap b A) - displacementTraceMap (gain • b)
      ((covariantAverage (p.expandingPrior n) gain Φ).toLinearMap A)‖ ≤ _
  rw [covariantAverage_shift, ← map_sub, displacementTraceMap_norm]
  change ‖(∫ a, f (a + b) ∂p.expandingPrior n) - (∫ a, f a ∂p.expandingPrior n)‖ ≤ _
  rw [p.integral_expandingPrior_shift n b f hf, p.integral_expandingPrior n f hf]
  apply weighted_integral_difference_le
  · exact hf.comp (by fun_prop)
  · intro a
    exact (translatedChannel gain Φ (((n : ℝ) + 1) • a)).toPositiveTracePreservingMap.norm_map_of_nonneg A hA
  · exact (measurePreserving_add_left volume (-(((n : ℝ) + 1)⁻¹ • b))).integrable_comp_of_integrable
      p.integrable
  · exact p.integrable

end PhaseSpaceDensity

/-- The literal uniform Lebesgue density on a measurable finite-volume region.
Regions can be boxes, balls, or any other measurable set of positive finite volume. -/
def flatRegionDensity (s : Set (Fin d → ℂ)) (hs : MeasurableSet s)
    (hs0 : volume s ≠ 0) (hsf : volume s ≠ ⊤) : PhaseSpaceDensity d where
  value := s.indicator (fun _ => (volume.real s)⁻¹)
  measurable := measurable_const.indicator hs
  nonneg := fun a => Set.indicator_nonneg (fun _ _ => inv_nonneg.mpr measureReal_nonneg) a
  integral_one := by
    rw [integral_indicator_const _ hs, smul_eq_mul,
      mul_inv_cancel₀ ((measureReal_ne_zero_iff hsf).mpr hs0)]

/-- Integrating the flat prior is exactly the normalized flat-region payoff.
The dilation `n+1` turns the fixed reference region into an expanding window. -/
theorem integral_flatRegion_expandingPrior {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (s : Set (Fin d → ℂ)) (hs : MeasurableSet s)
    (hs0 : volume s ≠ 0) (hsf : volume s ≠ ⊤)
    (n : ℕ) (f : (Fin d → ℂ) → E) (hf : Continuous f) :
    (∫ a, f a ∂(flatRegionDensity s hs hs0 hsf).expandingPrior n) =
      (volume.real s)⁻¹ • ∫ z in s, f (((n : ℝ) + 1) • z) := by
  rw [PhaseSpaceDensity.integral_expandingPrior _ n f hf]
  change (∫ z, s.indicator (fun _ => (volume.real s)⁻¹) z •
    f (((n : ℝ) + 1) • z)) = _
  rw [show (fun z => s.indicator (fun _ => (volume.real s)⁻¹) z •
      f (((n : ℝ) + 1) • z)) =
    s.indicator (fun z => (volume.real s)⁻¹ • f (((n : ℝ) + 1) • z)) by
      funext z
      by_cases hz : z ∈ s <;> simp [hz]]
  rw [integral_indicator hs, integral_smul]

end Cloning.MultimodeCoherent
