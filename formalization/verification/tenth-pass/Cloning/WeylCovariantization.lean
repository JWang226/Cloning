import Cloning.WeylMultimodeChannel
import Cloning.ChannelAveraging

/-! Actual probability averages of Weyl-translated quantum channels. All
continuity, measurability, integrability, complete positivity and normalization
are derived for the constructed Fock representation. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter MeasureTheory

namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

/-- Joint continuity of the Weyl trace-class action. -/
theorem continuous_displacementTraceMap_apply {Ω : Type*} [TopologicalSpace Ω]
    {a : Ω → (Fin d → ℂ)} {A : Ω → TraceClass (Fock d)}
    (ha : Continuous a) (hA : Continuous A) :
    Continuous (fun x => displacementTraceMap (a x) (A x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h1 : Tendsto (fun y => ‖A y - A x‖) (𝓝 x) (𝓝 0) := by
    simpa using ((hA.tendsto x).sub_const (A x)).norm
  have h2 : Tendsto (fun y => ‖displacementTraceMap (a y) (A x) -
      displacementTraceMap (a x) (A x)‖) (𝓝 x) (𝓝 0) := by
    simpa using (((continuous_displacementTraceMap (A x)).comp ha).tendsto x |>.sub_const
      (displacementTraceMap (a x) (A x))).norm
  apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa using h1.add h2)
  intro y
  calc
    _ ≤ ‖displacementTraceMap (a y) (A y) - displacementTraceMap (a y) (A x)‖ +
        ‖displacementTraceMap (a y) (A x) - displacementTraceMap (a x) (A x)‖ :=
      norm_sub_le_norm_sub_add_norm_sub ..
    _ = _ := by rw [← map_sub, displacementTraceMap_norm]

/-- Translate the input and undo the amplified output displacement. The gain
parameter is the amplitude gain (the manuscript uses `sqrt γ`). -/
def translatedChannel (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (a : Fin d → ℂ) : QuantumChannel (Fock d) (Fock d) :=
  (displacementChannel (-(gain • a))).comp (Φ.comp (displacementChannel a))

@[simp] theorem translatedChannel_apply (gain : ℝ)
    (Φ : QuantumChannel (Fock d) (Fock d)) (a : Fin d → ℂ) (A : TraceClass (Fock d)) :
    (translatedChannel gain Φ a).toLinearMap A =
      displacementTraceMap (-(gain • a)) (Φ.toLinearMap (displacementTraceMap a A)) := by
  simp only [displacementTraceMap_eq_channel]
  rfl

/-- Regularity of translated competitors is proved from the actual Weyl action. -/
theorem continuous_translatedChannel (gain : ℝ)
    (Φ : QuantumChannel (Fock d) (Fock d)) (A : TraceClass (Fock d)) :
    Continuous (fun a => (translatedChannel gain Φ a).toLinearMap A) := by
  simp only [translatedChannel_apply]
  apply continuous_displacementTraceMap_apply
  · exact (continuous_const.smul continuous_id).neg
  · exact Φ.toPositiveTracePreservingMap.continuous.comp (continuous_displacementTraceMap A)

/-- A concrete competitor obtained by averaging Weyl translates under any
probability prior. It is an actual CPTP map, with no measurability assumption. -/
def covariantAverage (μ : Measure (Fin d → ℂ)) [IsProbabilityMeasure μ]
    (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d)) : QuantumChannel (Fock d) (Fock d) :=
  QuantumChannel.average μ (translatedChannel gain Φ)
    (fun A => (continuous_translatedChannel gain Φ A).aestronglyMeasurable)

@[simp] theorem covariantAverage_apply (μ : Measure (Fin d → ℂ)) [IsProbabilityMeasure μ]
    (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d)) (A : TraceClass (Fock d)) :
    (covariantAverage μ gain Φ).toLinearMap A =
      ∫ a, displacementTraceMap (-(gain • a))
        (Φ.toLinearMap (displacementTraceMap a A)) ∂μ := by
  change (∫ a, (translatedChannel gain Φ a).toLinearMap A ∂μ) = _
  simp only [translatedChannel_apply]

/-- Translation identity before averaging. Weyl phases cancel exactly. -/
theorem translatedChannel_shift (gain : ℝ)
    (Φ : QuantumChannel (Fock d) (Fock d)) (a b : Fin d → ℂ) (A : TraceClass (Fock d)) :
    (translatedChannel gain Φ a).toLinearMap (displacementTraceMap b A) =
      displacementTraceMap (gain • b) ((translatedChannel gain Φ (a + b)).toLinearMap A) := by
  simp only [translatedChannel_apply, displacementTraceMap_add]
  rw [show gain • b + -(gain • (a + b)) = -(gain • a) by
    simp only [smul_add]
    abel]

/-- The averaged covariance defect is precisely a translation of the prior.
This is the exact identity needed before applying a Følner boundary estimate. -/
theorem covariantAverage_shift (μ : Measure (Fin d → ℂ)) [IsProbabilityMeasure μ]
    (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d)) (b : Fin d → ℂ)
    (A : TraceClass (Fock d)) :
    (covariantAverage μ gain Φ).toLinearMap (displacementTraceMap b A) =
      displacementTraceMap (gain • b)
        (∫ a, (translatedChannel gain Φ (a + b)).toLinearMap A ∂μ) := by
  have hi : Integrable (fun a => (translatedChannel gain Φ (a + b)).toLinearMap A) μ := by
    apply quantumChannel_family_integrable μ (fun a => translatedChannel gain Φ (a + b))
    intro B
    exact ((continuous_translatedChannel gain Φ B).comp
      (continuous_id.add continuous_const)).aestronglyMeasurable
  change (∫ a, (translatedChannel gain Φ a).toLinearMap (displacementTraceMap b A) ∂μ) = _
  simp_rw [translatedChannel_shift]
  exact (displacementTraceMap (gain • b)).integral_comp_comm hi

/-- The exact quantitative boundary estimate for translated quantum channels.
For a positive input, changing prior densities costs at most their L¹ distance
times its trace norm. No dimension or energy cutoff enters this bound. -/
theorem translatedChannel_weighted_difference_le
    (ν : Measure (Fin d → ℂ)) (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (A : TraceClass (Fock d)) (hA : 0 ≤ A.1)
    (p q : (Fin d → ℂ) → ℝ) (hp : Integrable p ν) (hq : Integrable q ν) :
    ‖(∫ a, p a • (translatedChannel gain Φ a).toLinearMap A ∂ν) -
      (∫ a, q a • (translatedChannel gain Φ a).toLinearMap A ∂ν)‖ ≤
      ‖A‖ * ∫ a, |p a - q a| ∂ν := by
  let f := fun a => (translatedChannel gain Φ a).toLinearMap A
  have hn (a : Fin d → ℂ) : ‖f a‖ = ‖A‖ :=
    (translatedChannel gain Φ a).toPositiveTracePreservingMap.norm_map_of_nonneg A hA
  have hm : AEStronglyMeasurable f ν := (continuous_translatedChannel gain Φ A).aestronglyMeasurable
  have hi (r : (Fin d → ℂ) → ℝ) (hr : Integrable r ν) :
      Integrable (fun a => r a • f a) ν := by
    apply (hr.norm.mul_const ‖A‖).mono' (hr.aestronglyMeasurable.smul hm)
    exact Eventually.of_forall (fun a => by simp [norm_smul, hn])
  change ‖(∫ a, p a • f a ∂ν) - (∫ a, q a • f a ∂ν)‖ ≤ _
  rw [← integral_sub (hi p hp) (hi q hq)]
  calc
    _ ≤ ∫ a, ‖p a • f a - q a • f a‖ ∂ν := norm_integral_le_integral_norm _
    _ = ‖A‖ * ∫ a, |p a - q a| ∂ν := by
      simp only [← sub_smul, norm_smul, hn, Real.norm_eq_abs]
      rw [integral_mul_const]
      ring

end Cloning.MultimodeCoherent
