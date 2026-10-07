import Cloning.InfiniteIsometricChannel
import Cloning.InfinitePureStateContinuity

/-! All-input CPTP completions of actual rectangular contractions, with an
exact trace-norm formula for the replacement cost. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.InfiniteTraceClass
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A genuine Hilbert-space contraction gives a trace-nonincreasing conjugation.
The proof is the actual positive trace-class rank-one expansion. -/
theorem conjugationLinearMap_contraction_trace (V : H →L[ℂ] K)
    (hV : ∀ x, ‖V x‖ ≤ ‖x‖) (A : TraceClass H) (hA : 0 ≤ A.1) :
    (traceCLM (conjugationLinearMap V A)).re ≤ (traceCLM A).re := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hl : HasSum (fun i : w => ‖V (CFC.sqrt A.1 (b i))‖ ^ 2)
      (traceCLM (conjugationLinearMap V A)).re := by
    have h := (conjugationLinearMap_positive_hasSum V A hA b).mapL traceCLM
    simpa only [traceCLM_vectorProjector, Complex.ofReal_re] using Complex.hasSum_re h
  have hr : HasSum (fun i : w => ‖CFC.sqrt A.1 (b i)‖ ^ 2) (traceCLM A).re := by
    simpa only [norm_vectorProjector] using positive_rankOne_mass hA A.2 b
  exact hasSum_le (fun i => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hV _)) hl hr

/-- Apply the rectangular compression, then put exactly the missing trace in
an explicit fixed density state. This is CPTP on every complex trace-class input. -/
def QuantumChannel.ofContraction (V : H →L[ℂ] K) (hV : ∀ x, ‖V x‖ ≤ ‖x‖)
    (σ : DensityState K) : QuantumChannel H K :=
  QuantumChannel.traceRepair (conjugationLinearMap V) (conjugationLinearMap_completelyPositive V)
    (conjugationLinearMap_contraction_trace V hV) σ

@[simp] theorem QuantumChannel.ofContraction_apply (V : H →L[ℂ] K)
    (hV : ∀ x, ‖V x‖ ≤ ‖x‖) (σ : DensityState K) (A : TraceClass H) :
    (QuantumChannel.ofContraction V hV σ).toLinearMap A = conjugationLinearMap V A +
      (traceCLM A - traceCLM (conjugationLinearMap V A)) •
        TraceClass.ofOperator σ.op σ.traceClass := rfl

/-- Exact action on pure inputs, including the trace of their discarded component. -/
theorem QuantumChannel.ofContraction_vectorProjector (V : H →L[ℂ] K)
    (hV : ∀ x, ‖V x‖ ≤ ‖x‖) (σ : DensityState K) (x : H) :
    (QuantumChannel.ofContraction V hV σ).toLinearMap (vectorProjector x) =
      vectorProjector (V x) + ((‖x‖ ^ 2 - ‖V x‖ ^ 2 : ℝ) : ℂ) •
        TraceClass.ofOperator σ.op σ.traceClass := by
  rw [QuantumChannel.ofContraction_apply, conjugationLinearMap_vectorProjector,
    traceCLM_vectorProjector, traceCLM_vectorProjector]
  simp only [Complex.ofReal_sub, Complex.ofReal_pow]

/-- Compression is exact on every retained pure vector. -/
theorem QuantumChannel.ofContraction_vectorProjector_of_norm_eq (V : H →L[ℂ] K)
    (hV : ∀ x, ‖V x‖ ≤ ‖x‖) (σ : DensityState K) (x : H) (hx : ‖V x‖ = ‖x‖) :
    (QuantumChannel.ofContraction V hV σ).toLinearMap (vectorProjector x) =
      vectorProjector (V x) := by
  simp only [QuantumChannel.ofContraction_vectorProjector, hx, sub_self, Complex.ofReal_zero, zero_smul, add_zero]

/-- The trace-norm cost of the fallback is exactly the lost probability. -/
theorem QuantumChannel.ofContraction_repair_error (V : H →L[ℂ] K)
    (hV : ∀ x, ‖V x‖ ≤ ‖x‖) (σ : DensityState K) (A : TraceClass H) (hA : 0 ≤ A.1) :
    ‖(QuantumChannel.ofContraction V hV σ).toLinearMap A - conjugationLinearMap V A‖ =
      (traceCLM A).re - (traceCLM (conjugationLinearMap V A)).re :=
  norm_traceRepair_sub (conjugationLinearMap_completelyPositive V)
    (conjugationLinearMap_contraction_trace V hV) σ A hA

end Cloning.InfiniteTraceClass
