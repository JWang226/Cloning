import Cloning.WeylGaussianPrior

/-! Explicit Gaussian Følner averages of actual quantum competitors.
The expanding Gaussian priors give vanishing covariance defect in the genuine
trace norm for every positive trace-class input. -/

noncomputable section
open scoped ComplexOrder BigOperators Topology
open Filter MeasureTheory

namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

/-- Integration against the expanding Gaussian prior is literal integration
against the fixed product Gaussian density after dilation. -/
theorem integral_expandingGaussianPrior {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : (Fin d → ℂ) → E) (hf : Continuous f) :
    (∫ a, f a ∂expandingGaussianPrior d n) =
      ∫ z, priorDensity z • f (((n : ℝ) + 1) • z) := by
  rw [expandingGaussianPrior, integral_map (by fun_prop) hf.aestronglyMeasurable]
  rw [gaussianPrior, integral_withDensity_eq_integral_toReal_smul
    continuous_priorDensity.measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (priorDensity_pos _).le]

/-- A fixed displacement of an expanding prior is a vanishing displacement
of its fixed reference density; this is an exact change of variables. -/
theorem integral_expandingGaussianPrior_shift {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (b : Fin d → ℂ) (f : (Fin d → ℂ) → E) (hf : Continuous f) :
    (∫ a, f (a + b) ∂expandingGaussianPrior d n) =
      ∫ z, priorDensity (-(((n : ℝ) + 1)⁻¹ • b) + z) •
        f (((n : ℝ) + 1) • z) := by
  rw [integral_expandingGaussianPrior n (fun a => f (a + b))
    (hf.comp (continuous_id.add continuous_const))]
  rw [← integral_add_left_eq_self
    (fun z => priorDensity z • f (((n : ℝ) + 1) • z + b))
    (-(((n : ℝ) + 1)⁻¹ • b))]
  congr 1
  funext z
  congr 1
  congr 1
  have hn : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  rw [smul_add, smul_neg, smul_smul, mul_inv_cancel₀ hn, one_smul]
  abel

/-- A general L¹ density perturbation estimate with an exact uniform norm
bound. This will be applied to the actual translated-channel family. -/
theorem weighted_integral_difference_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin d → ℂ) → E) (hf : Continuous f) (C : ℝ)
    (hn : ∀ a, ‖f a‖ = C) (p q : (Fin d → ℂ) → ℝ)
    (hp : Integrable p) (hq : Integrable q) :
    ‖(∫ a, p a • f a) - (∫ a, q a • f a)‖ ≤ C * ∫ a, |p a - q a| := by
  have hi (r : (Fin d → ℂ) → ℝ) (hr : Integrable r) :
      Integrable (fun a => r a • f a) := by
    apply (hr.norm.mul_const C).mono' (hr.aestronglyMeasurable.smul hf.aestronglyMeasurable)
    exact Eventually.of_forall (fun a => by simp [norm_smul, hn])
  rw [← integral_sub (hi p hp) (hi q hq)]
  calc
    _ ≤ ∫ a, ‖p a • f a - q a • f a‖ := norm_integral_le_integral_norm _
    _ = _ := by
      simp only [← sub_smul, norm_smul, hn, Real.norm_eq_abs]
      rw [integral_mul_const]
      ring

/-- A concrete sequence of CPTP competitors, using variance `(n+1)^2` priors. -/
def gaussianFoelnerChannel (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (n : ℕ) : QuantumChannel (Fock d) (Fock d) :=
  covariantAverage (expandingGaussianPrior d n) gain Φ

/-- Explicit covariance-error bound, valid at each finite averaging scale. -/
theorem gaussianFoelnerChannel_covariance_bound (gain : ℝ)
    (Φ : QuantumChannel (Fock d) (Fock d)) (b : Fin d → ℂ)
    (A : TraceClass (Fock d)) (hA : 0 ≤ A.1) (n : ℕ) :
    ‖(gaussianFoelnerChannel gain Φ n).toLinearMap (displacementTraceMap b A) -
      displacementTraceMap (gain • b) ((gaussianFoelnerChannel gain Φ n).toLinearMap A)‖ ≤
      ‖A‖ * ∫ z, |priorDensity (-(((n : ℝ) + 1)⁻¹ • b) + z) - priorDensity z| := by
  let f : (Fin d → ℂ) → TraceClass (Fock d) :=
    fun a => (translatedChannel gain Φ a).toLinearMap A
  have hf : Continuous f := continuous_translatedChannel gain Φ A
  change ‖(covariantAverage (expandingGaussianPrior d n) gain Φ).toLinearMap
    (displacementTraceMap b A) - displacementTraceMap (gain • b)
      ((covariantAverage (expandingGaussianPrior d n) gain Φ).toLinearMap A)‖ ≤ _
  rw [covariantAverage_shift, ← map_sub, displacementTraceMap_norm]
  change ‖(∫ a, f (a + b) ∂expandingGaussianPrior d n) -
    (∫ a, f a ∂expandingGaussianPrior d n)‖ ≤ _
  rw [integral_expandingGaussianPrior_shift n b f hf, integral_expandingGaussianPrior n f hf]
  apply weighted_integral_difference_le
  · exact hf.comp (by fun_prop)
  · intro a
    exact (translatedChannel gain Φ (((n : ℝ) + 1) • a)).toPositiveTracePreservingMap.norm_map_of_nonneg A hA
  · exact (measurePreserving_add_left volume (-(((n : ℝ) + 1)⁻¹ • b))).integrable_comp_of_integrable
      integrable_priorDensity
  · exact integrable_priorDensity

/-- The explicitly constructed Gaussian averages become displacement
covariant in trace norm, for every fixed positive trace-class input and every
phase-space displacement. No covariance or prior-limit assumption remains. -/
theorem gaussianFoelnerChannel_covariance_tendsto (gain : ℝ)
    (Φ : QuantumChannel (Fock d) (Fock d)) (b : Fin d → ℂ)
    (A : TraceClass (Fock d)) (hA : 0 ≤ A.1) :
    Tendsto (fun n => ‖(gaussianFoelnerChannel gain Φ n).toLinearMap (displacementTraceMap b A) -
      displacementTraceMap (gain • b) ((gaussianFoelnerChannel gain Φ n).toLinearMap A)‖)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n => norm_nonneg _) (gaussianFoelnerChannel_covariance_bound gain Φ b A hA)
  simpa only [mul_zero] using (prior_translation_error_tendsto b).const_mul ‖A‖

/-- The covariance defect as an actual continuous linear trace-class map. -/
def gaussianFoelnerDefect (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (b : Fin d → ℂ) (n : ℕ) : TraceClass (Fock d) →L[ℂ] TraceClass (Fock d) :=
  ((gaussianFoelnerChannel gain Φ n).toPositiveTracePreservingMap.toContinuousLinearMap).comp
      (displacementTraceMap b) -
    (displacementTraceMap (gain • b)).comp
      ((gaussianFoelnerChannel gain Φ n).toPositiveTracePreservingMap.toContinuousLinearMap)

@[simp] theorem gaussianFoelnerDefect_apply (gain : ℝ)
    (Φ : QuantumChannel (Fock d) (Fock d)) (b : Fin d → ℂ) (n : ℕ)
    (A : TraceClass (Fock d)) : gaussianFoelnerDefect gain Φ b n A =
      (gaussianFoelnerChannel gain Φ n).toLinearMap (displacementTraceMap b A) -
        displacementTraceMap (gain • b) ((gaussianFoelnerChannel gain Φ n).toLinearMap A) := rfl

/-- The same vanishing defect holds on every trace-class input, including
nonself-adjoint operators, as required for the common CP-limit extraction. -/
theorem gaussianFoelnerChannel_covariance_tendsto_all (gain : ℝ)
    (Φ : QuantumChannel (Fock d) (Fock d)) (b : Fin d → ℂ)
    (A : TraceClass (Fock d)) :
    Tendsto (fun n => ‖(gaussianFoelnerChannel gain Φ n).toLinearMap (displacementTraceMap b A) -
      displacementTraceMap (gain • b) ((gaussianFoelnerChannel gain Φ n).toLinearMap A)‖)
      atTop (𝓝 0) := by
  let D := gaussianFoelnerDefect gain Φ b
  have hpos (B : TraceClass (Fock d)) (hB : 0 ≤ B.1) :
      Tendsto (fun n => D n B) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (gaussianFoelnerChannel_covariance_tendsto gain Φ b B hB)
  have hself (B : TraceClass (Fock d)) (hB : IsSelfAdjoint B.1) :
      Tendsto (fun n => D n B) atTop (𝓝 0) := by
    have h := (hpos _ (TraceClass.positivePart_nonneg B hB)).sub
      (hpos _ (TraceClass.negativePart_nonneg B hB))
    simpa only [← map_sub, TraceClass.positivePart_sub_negativePart B hB, sub_zero] using h
  have h := (hself _ (TraceClass.realComponent_isSelfAdjoint A)).add
    ((hself _ (TraceClass.imaginaryComponent_isSelfAdjoint A)).const_smul Complex.I)
  have h' : Tendsto (fun n => D n A) atTop (𝓝 0) := by
    simpa only [← map_smul, ← map_add, TraceClass.realComponent_add_I_smul_imaginaryComponent A,
      smul_zero, add_zero] using h
  exact tendsto_zero_iff_norm_tendsto_zero.mp h'

end Cloning.MultimodeCoherent
