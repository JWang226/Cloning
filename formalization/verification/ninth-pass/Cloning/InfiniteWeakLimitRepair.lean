import Cloning.InfiniteChannelWeakLimit
import Cloning.InfiniteChannelTraceRepair

/-!
# Quantum-channel completion of actual weak limits

Complete positivity and trace nonincrease are derived from weak convergence,
then the trace deficit is repaired by a fixed density state.
-/

namespace Cloning.InfiniteTraceClass

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open Filter

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {α : Type*} {l : Filter α} [l.NeBot]

/-- An actual weak limit of channels can be completed to a channel without
assuming positivity, complete positivity, or trace preservation of the limit. -/
def QuantumChannel.weakLimitTraceRepair (Φ : α → QuantumChannel H K)
    (Ψ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hlim : ∀ A x y, Tendsto (fun a => ⟪x, ((Φ a).toLinearMap A).1 y⟫_ℂ) l
      (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ)) (σ : DensityState K) : QuantumChannel H K :=
  QuantumChannel.traceRepair Ψ (isCompletelyPositive_of_channel_weakLimit Φ Ψ hlim)
    (trace_le_of_channel_weakLimit Φ Ψ hlim) σ

@[simp] theorem QuantumChannel.weakLimitTraceRepair_apply
    (Φ : α → QuantumChannel H K) (Ψ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hlim : ∀ A x y, Tendsto (fun a => ⟪x, ((Φ a).toLinearMap A).1 y⟫_ℂ) l
      (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ)) (σ : DensityState K) (A : TraceClass H) :
    (QuantumChannel.weakLimitTraceRepair Φ Ψ hlim σ).toLinearMap A =
      Ψ A + (traceCLM A - traceCLM (Ψ A)) • TraceClass.ofOperator σ.op σ.traceClass := rfl

theorem QuantumChannel.weakLimitTraceRepair_dominates
    (Φ : α → QuantumChannel H K) (Ψ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hlim : ∀ A x y, Tendsto (fun a => ⟪x, ((Φ a).toLinearMap A).1 y⟫_ℂ) l
      (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ)) (σ : DensityState K) (A : TraceClass H)
    (hA : 0 ≤ A.1) :
    (Ψ A).1 ≤ ((QuantumChannel.weakLimitTraceRepair Φ Ψ hlim σ).toLinearMap A).1 :=
  le_traceRepair_of_nonneg (isCompletelyPositive_of_channel_weakLimit Φ Ψ hlim)
    (trace_le_of_channel_weakLimit Φ Ψ hlim) σ A hA

theorem QuantumChannel.weakLimitTraceRepair_norm_sub
    (Φ : α → QuantumChannel H K) (Ψ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hlim : ∀ A x y, Tendsto (fun a => ⟪x, ((Φ a).toLinearMap A).1 y⟫_ℂ) l
      (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ)) (σ : DensityState K) (A : TraceClass H)
    (hA : 0 ≤ A.1) :
    ‖(QuantumChannel.weakLimitTraceRepair Φ Ψ hlim σ).toLinearMap A - Ψ A‖ =
      (traceCLM A).re - (traceCLM (Ψ A)).re :=
  norm_traceRepair_sub (isCompletelyPositive_of_channel_weakLimit Φ Ψ hlim)
    (trace_le_of_channel_weakLimit Φ Ψ hlim) σ A hA

end
end Cloning.InfiniteTraceClass
