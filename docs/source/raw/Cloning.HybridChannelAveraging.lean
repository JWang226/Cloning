import Cloning.HybridChannel
import Cloning.HybridL1Cone
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Bochner averaging of actual bounded hybrid maps. Integrability and a
competitor-independent bound follow from CP and preservation of integrated
trace. -/
noncomputable section
open scoped ComplexOrder Topology
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
variable {Ω Θ H K : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
  {μ : Measure Ω} (ν : Measure Θ) [IsProbabilityMeasure ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Integrated trace, as a bounded functional on the genuine L¹ space. -/
def integratedTrace : Lp (TraceClass H) 1 μ →L[ℂ] ℂ :=
  traceCLM.comp (L1.integralCLM' ℂ)

lemma integratedTrace_apply (A : Lp (TraceClass H) 1 μ) :
    integratedTrace A = ∫ y, traceCLM (A y) ∂μ := by
  change traceCLM (L1.integralCLM' ℂ A) = _
  rw [← L1.integral_eq', L1.integral_eq_integral]
  exact (traceCLM.integral_comp_comm (L1.integrable_coeFn A)).symm

variable (Λ : Θ → Channel H K μ)
    (hmeas : ∀ A : Lp (TraceClass H) 1 μ, AEStronglyMeasurable (fun t => (Λ t).map A) ν)

include hmeas
lemma channel_family_integrable (A : Lp (TraceClass H) 1 μ) :
    Integrable (fun t => (Λ t).map A) ν :=
  (integrable_const (2 * ‖A‖)).mono' (hmeas A)
    (Eventually.of_forall fun t => (Λ t).norm_le_two A)

def averageLinear : Lp (TraceClass H) 1 μ →ₗ[ℂ] Lp (TraceClass K) 1 μ where
  toFun A := ∫ t, (Λ t).map A ∂ν
  map_add' A B := by
    simp only [map_add]
    exact integral_add (channel_family_integrable ν Λ hmeas A)
      (channel_family_integrable ν Λ hmeas B)
  map_smul' c A := by simp only [map_smul, integral_smul, RingHom.id_apply]

lemma averageLinear_norm_le (A : Lp (TraceClass H) 1 μ) :
    ‖averageLinear ν Λ hmeas A‖ ≤ 2 * ‖A‖ := by
  change ‖∫ t, (Λ t).map A ∂ν‖ ≤ _
  apply (norm_integral_le_integral_norm _).trans
  have h := integral_mono (channel_family_integrable ν Λ hmeas A).norm
    (integrable_const (2 * ‖A‖)) (fun t => (Λ t).norm_le_two A)
  simpa using h

/-- The actual operator-valued L¹ average. -/
def averageCLM : Lp (TraceClass H) 1 μ →L[ℂ] Lp (TraceClass K) 1 μ :=
  (averageLinear ν Λ hmeas).mkContinuous 2 (averageLinear_norm_le ν Λ hmeas)

@[simp] lemma averageCLM_apply (A : Lp (TraceClass H) 1 μ) :
    averageCLM ν Λ hmeas A = ∫ t, (Λ t).map A ∂ν := rfl

lemma averageCLM_tracePreserving : L1TracePreserving (averageCLM ν Λ hmeas).toLinearMap := by
  intro A
  rw [← integratedTrace_apply, ← integratedTrace_apply]
  change integratedTrace (∫ t, (Λ t).map A ∂ν) = integratedTrace A
  rw [← integratedTrace.integral_comp_comm (channel_family_integrable ν Λ hmeas A)]
  have ht (t : Θ) : integratedTrace ((Λ t).map A) = integratedTrace A := by
    simp only [integratedTrace_apply]
    exact (Λ t).tracePreserving A
  simp only [ht, integral_const, probReal_univ, one_smul]

lemma averageCLM_completelyPositive : L1CompletelyPositive (averageCLM ν Λ hmeas).toLinearMap := by
  intro n A hA
  let B : Θ → Fin n → Fin n → Lp (TraceClass K) 1 μ := fun t i j => (Λ t).map (A i j)
  have hB : Integrable B ν := integrable_pi_iff.mpr fun i => integrable_pi_iff.mpr fun j =>
    channel_family_integrable ν Λ hmeas (A i j)
  have hp : L1BlockPositive (∫ t, B t ∂ν) := L1BlockPositive_integral hB
    (Eventually.of_forall fun t => (Λ t).completelyPositive n A hA)
  have he (i j : Fin n) : (∫ t, B t ∂ν) i j = ∫ t, (Λ t).map (A i j) ∂ν := by
    rw [eval_integral (fun i => hB.eval i) i,
      eval_integral (fun j => (hB.eval i).eval j) j]
  change L1BlockPositive (fun i j => averageCLM ν Λ hmeas (A i j))
  have heq : (fun i j => averageCLM ν Λ hmeas (A i j)) = ∫ t, B t ∂ν := by
    funext i j
    exact (he i j).symm
  rwa [heq]

/-- Probability averaging produces an actual completely positive trace-preserving
hybrid channel. All regularity except strong measurability is derived. -/
def Channel.average : Channel H K μ where
  map := averageCLM ν Λ hmeas
  completelyPositive := averageCLM_completelyPositive ν Λ hmeas
  tracePreserving := averageCLM_tracePreserving ν Λ hmeas

@[simp] lemma Channel.average_apply (A : Lp (TraceClass H) 1 μ) :
    (Channel.average ν Λ hmeas).map A = ∫ t, (Λ t).map A ∂ν := rfl

end Cloning.Hybrid
