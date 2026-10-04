import Cloning.InfiniteTraceClassChannels
import Cloning.InfiniteTraceClassSeries

/-! Automatic trace-norm boundedness for positive maps with a scaled trace
bound. Trace preservation is not required, so weighted CP maps are included. -/

namespace Cloning.InfiniteTraceClass

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem norm_map_nonneg_le_of_trace_bound
    (Φ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hpos : ∀ A, 0 ≤ A.1 → 0 ≤ (Φ A).1) {c : ℝ}
    (htrace : ∀ A, 0 ≤ A.1 → (traceCLM (Φ A)).re ≤ c * (traceCLM A).re)
    (A : TraceClass H) (hA : 0 ≤ A.1) : ‖Φ A‖ ≤ c * ‖A‖ := by
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ (hpos A hA),
    TraceClass.norm_eq_trace_re_of_nonneg _ hA]
  exact htrace A hA

theorem norm_map_selfAdjoint_le_of_trace_bound
    (Φ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hpos : ∀ A, 0 ≤ A.1 → 0 ≤ (Φ A).1) {c : ℝ}
    (htrace : ∀ A, 0 ≤ A.1 → (traceCLM (Φ A)).re ≤ c * (traceCLM A).re)
    (A : TraceClass H) (hA : IsSelfAdjoint A.1) : ‖Φ A‖ ≤ c * ‖A‖ := by
  have hd := TraceClass.positivePart_sub_negativePart A hA
  calc
    ‖Φ A‖ = ‖Φ (TraceClass.positivePart A hA) -
        Φ (TraceClass.negativePart A hA)‖ := by rw [← map_sub, hd]
    _ ≤ ‖Φ (TraceClass.positivePart A hA)‖ +
        ‖Φ (TraceClass.negativePart A hA)‖ := norm_sub_le _ _
    _ ≤ c * ‖TraceClass.positivePart A hA‖ +
        c * ‖TraceClass.negativePart A hA‖ :=
      add_le_add
        (norm_map_nonneg_le_of_trace_bound Φ hpos htrace _
          (TraceClass.positivePart_nonneg A hA))
        (norm_map_nonneg_le_of_trace_bound Φ hpos htrace _
          (TraceClass.negativePart_nonneg A hA))
    _ = c * ‖A‖ := by
      rw [← mul_add, TraceClass.norm_positivePart_add_norm_negativePart A hA]

/-- A scaled positive-input trace bound implies continuity on the entire
complex trace-class Banach space, including non-self-adjoint inputs. -/
theorem norm_map_le_two_mul_of_trace_bound
    (Φ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hpos : ∀ A, 0 ≤ A.1 → 0 ≤ (Φ A).1) {c : ℝ} (hc : 0 ≤ c)
    (htrace : ∀ A, 0 ≤ A.1 → (traceCLM (Φ A)).re ≤ c * (traceCLM A).re)
    (A : TraceClass H) : ‖Φ A‖ ≤ (2 * c) * ‖A‖ := by
  have hd := TraceClass.realComponent_add_I_smul_imaginaryComponent A
  calc
    ‖Φ A‖ = ‖Φ (TraceClass.realComponent A) +
        Complex.I • Φ (TraceClass.imaginaryComponent A)‖ := by
      conv_lhs => rw [← hd]
      rw [map_add, map_smul]
    _ ≤ ‖Φ (TraceClass.realComponent A)‖ +
        ‖Complex.I • Φ (TraceClass.imaginaryComponent A)‖ := norm_add_le _ _
    _ = ‖Φ (TraceClass.realComponent A)‖ + ‖Φ (TraceClass.imaginaryComponent A)‖ := by
      simp [norm_smul]
    _ ≤ c * ‖TraceClass.realComponent A‖ + c * ‖TraceClass.imaginaryComponent A‖ :=
      add_le_add
        (norm_map_selfAdjoint_le_of_trace_bound Φ hpos htrace _
          (TraceClass.realComponent_isSelfAdjoint A))
        (norm_map_selfAdjoint_le_of_trace_bound Φ hpos htrace _
          (TraceClass.imaginaryComponent_isSelfAdjoint A))
    _ ≤ c * ‖A‖ + c * ‖A‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (TraceClass.norm_realComponent_le A) hc)
        (mul_le_mul_of_nonneg_left (TraceClass.norm_imaginaryComponent_le A) hc)
    _ = (2 * c) * ‖A‖ := by ring

/-- Boundedness is derived from positivity and the trace bound. -/
def toContinuousLinearMapOfTraceBound
    (Φ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hpos : ∀ A, 0 ≤ A.1 → 0 ≤ (Φ A).1) {c : ℝ} (hc : 0 ≤ c)
    (htrace : ∀ A, 0 ≤ A.1 → (traceCLM (Φ A)).re ≤ c * (traceCLM A).re) :
    TraceClass H →L[ℂ] TraceClass K :=
  Φ.mkContinuous (2 * c) (norm_map_le_two_mul_of_trace_bound Φ hpos hc htrace)

@[simp] theorem toContinuousLinearMapOfTraceBound_apply
    (Φ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hpos : ∀ A, 0 ≤ A.1 → 0 ≤ (Φ A).1) {c : ℝ} (hc : 0 ≤ c)
    (htrace : ∀ A, 0 ≤ A.1 → (traceCLM (Φ A)).re ≤ c * (traceCLM A).re)
    (A : TraceClass H) : toContinuousLinearMapOfTraceBound Φ hpos hc htrace A = Φ A := rfl

end
end Cloning.InfiniteTraceClass
