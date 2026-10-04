import Cloning.InfiniteCompletelyPositive
import Cloning.InfiniteChannelTraceRepair
import Cloning.InfiniteChannelCovariance
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Probability averages of actual trace-class quantum channels are CPTP.
Measurability is the only family regularity premise; integrability is derived
from the proved trace-norm bounds. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory
namespace Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {H K Ω : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [MeasurableSpace Ω]

theorem integral_complex_nonneg {μ : Measure Ω} {f : Ω → ℂ}
    (hf : Integrable f μ) (hpos : ∀ x, 0 ≤ f x) : 0 ≤ ∫ x, f x ∂μ := by
  apply Complex.nonneg_iff.mpr
  constructor
  · change 0 ≤ Complex.reCLM (∫ x, f x ∂μ)
    rw [← Complex.reCLM.integral_comp_comm hf]
    exact integral_nonneg fun x => (Complex.nonneg_iff.mp (hpos x)).1
  · change 0 = Complex.imCLM (∫ x, f x ∂μ)
    rw [← Complex.imCLM.integral_comp_comm hf]
    have he : (fun x => (f x).im) = fun _ => (0 : ℝ) :=
      funext fun x => (Complex.nonneg_iff.mp (hpos x)).2.symm
    change 0 = (∫ x, (f x).im ∂μ)
    rw [he, integral_zero]

variable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Φ : Ω → QuantumChannel H K)
    (hmeas : ∀ A : TraceClass H, AEStronglyMeasurable (fun x => (Φ x).toLinearMap A) μ)

include hmeas

theorem quantumChannel_family_integrable (A : TraceClass H) :
    Integrable (fun x => (Φ x).toLinearMap A) μ := by
  apply (integrable_const (2 * ‖A‖)).mono' (hmeas A)
  exact Filter.Eventually.of_forall fun x => (Φ x).toPositiveTracePreservingMap.norm_map_le_two_mul A

def averagedChannelLinear : TraceClass H →ₗ[ℂ] TraceClass K where
  toFun A := ∫ x, (Φ x).toLinearMap A ∂μ
  map_add' A B := by
    simp only [map_add]
    exact integral_add (quantumChannel_family_integrable μ Φ hmeas A)
      (quantumChannel_family_integrable μ Φ hmeas B)
  map_smul' c A := by simp only [map_smul, integral_smul, RingHom.id_apply]

@[simp] theorem averagedChannelLinear_apply (A : TraceClass H) :
    averagedChannelLinear μ Φ hmeas A = ∫ x, (Φ x).toLinearMap A ∂μ := rfl

theorem averagedChannel_trace (A : TraceClass H) :
    traceCLM (averagedChannelLinear μ Φ hmeas A) = traceCLM A := by
  rw [averagedChannelLinear_apply,
    ← traceCLM.integral_comp_comm (quantumChannel_family_integrable μ Φ hmeas A)]
  have ht (x : Ω) : traceCLM ((Φ x).toLinearMap A) = traceCLM A :=
    (Φ x).trace_preserving A
  simp only [ht, integral_const, probReal_univ, one_smul]

theorem averagedChannel_completelyPositive :
    IsCompletelyPositive (averagedChannelLinear μ Φ hmeas) := by
  intro n A hA v
  let f : Ω → ℂ := fun x => ∑ i : Fin n, ∑ j : Fin n,
    ⟪v i, ((Φ x).toLinearMap (A i j)).1 (v j)⟫_ℂ
  have hi (i j : Fin n) : Integrable
      (fun x => ⟪v i, ((Φ x).toLinearMap (A i j)).1 (v j)⟫_ℂ) μ :=
    (traceClassMatrixCoefficient (v i) (v j)).integrable_comp
      (quantumChannel_family_integrable μ Φ hmeas (A i j))
  have hf : Integrable f μ := by
    apply integrable_finset_sum
    intro i hi'
    exact integrable_finset_sum _ (fun j hj => hi i j)
  have hp : 0 ≤ ∫ x, f x ∂μ :=
    integral_complex_nonneg hf (fun x => (Φ x).completelyPositive n A hA v)
  have he (i j : Fin n) :
      ⟪v i, (averagedChannelLinear μ Φ hmeas (A i j)).1 (v j)⟫_ℂ =
        ∫ x, ⟪v i, ((Φ x).toLinearMap (A i j)).1 (v j)⟫_ℂ ∂μ := by
    exact ((traceClassMatrixCoefficient (v i) (v j)).integral_comp_comm
      (quantumChannel_family_integrable μ Φ hmeas (A i j))).symm
  simp_rw [he]
  have hi' (i : Fin n) : Integrable
      (fun x => ∑ j : Fin n, ⟪v i, ((Φ x).toLinearMap (A i j)).1 (v j)⟫_ℂ) μ :=
    integrable_finset_sum _ (fun j hj => hi i j)
  simpa only [f, integral_finset_sum _ (fun i hi => hi' i),
    integral_finset_sum _ (fun j hj => hi _ j)] using hp

/-- The Bochner probability average, as an actual completely positive,
trace-preserving map on every trace-class input. -/
def QuantumChannel.average : QuantumChannel H K where
  toLinearMap := averagedChannelLinear μ Φ hmeas
  map_nonneg := (averagedChannel_completelyPositive μ Φ hmeas).map_nonneg
  trace_preserving := averagedChannel_trace μ Φ hmeas
  completelyPositive := averagedChannel_completelyPositive μ Φ hmeas

end Cloning.InfiniteTraceClass
