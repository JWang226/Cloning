import Cloning.InfiniteCompletelyPositive
import Cloning.InfiniteTraceClassWeakLimit

/-!
# Complete positivity and trace loss in weak limits of quantum channels

A pointwise weak-operator limit of genuine quantum channels is completely
positive and trace-nonincreasing on positive inputs. Complete positivity is
proved at every finite ancilla size by continuity of the finite quadratic
form. The trace bound uses the finite-diagonal Fatou argument; trace
preservation of the limit is not assumed or claimed.

The limit is supplied as a complex-linear map into the trace-class space.
Constructing such a limit or extracting a convergent subnet is separate.
-/

namespace Cloning.InfiniteTraceClass

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace BigOperators Topology
open Filter

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {α : Type*} {l : Filter α} [l.NeBot]

/-- Positivity of an actual finite operator matrix is closed under entrywise
weak-operator convergence. -/
theorem BlockPositive.of_weakOperator_tendsto {ι : Type*} [Fintype ι]
    (A : α → ι → ι → TraceClass K) (T : ι → ι → TraceClass K)
    (hA : ∀ a, BlockPositive (A a))
    (hlim : ∀ i j x y, Tendsto (fun a ↦ ⟪x, (A a i j).1 y⟫_ℂ) l
      (𝓝 ⟪x, (T i j).1 y⟫_ℂ)) : BlockPositive T := by
  intro x
  have hsum : Tendsto (fun a ↦ ∑ i, ∑ j, ⟪x i, (A a i j).1 (x j)⟫_ℂ) l
      (𝓝 (∑ i, ∑ j, ⟪x i, (T i j).1 (x j)⟫_ℂ)) :=
    tendsto_finset_sum _ (fun i _ ↦ tendsto_finset_sum _ (fun j _ ↦ hlim i j (x i) (x j)))
  exact ge_of_tendsto hsum (Eventually.of_forall fun a ↦ hA a x)

/-- All finite ancilla positivity tests pass to the channel weak limit. -/
theorem isCompletelyPositive_of_channel_weakLimit (Φ : α → QuantumChannel H K)
    (Ψ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hlim : ∀ A x y, Tendsto (fun a ↦ ⟪x, ((Φ a).toLinearMap A).1 y⟫_ℂ) l
      (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ)) : IsCompletelyPositive Ψ := by
  intro n A hA
  apply BlockPositive.of_weakOperator_tendsto (l := l)
    (fun a i j ↦ (Φ a).toLinearMap (A i j)) (fun i j ↦ Ψ (A i j))
    (fun a ↦ (Φ a).completelyPositive n A hA)
  intro i j x y
  exact hlim (A i j) x y

/-- Ordinary positivity of the weak limit is also derived, not assumed. -/
theorem nonneg_of_channel_weakLimit (Φ : α → QuantumChannel H K)
    (Ψ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hlim : ∀ A x y, Tendsto (fun a ↦ ⟪x, ((Φ a).toLinearMap A).1 y⟫_ℂ) l
      (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ)) (A : TraceClass H) (hA : 0 ≤ A.1) :
    0 ≤ (Ψ A).1 := by
  apply nonneg_of_inner_nonneg
  intro x
  apply ge_of_tendsto (hlim A x x)
  exact Eventually.of_forall fun a ↦
    (((Φ a).toLinearMap A).1.nonneg_iff_isPositive.mp ((Φ a).map_nonneg A hA)).inner_nonneg_right x

/-- Trace may decrease in a pointwise weak channel limit, but cannot increase
on a positive input. This uses the actual analytic trace. -/
theorem trace_le_of_channel_weakLimit (Φ : α → QuantumChannel H K)
    (Ψ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hlim : ∀ A x y, Tendsto (fun a ↦ ⟪x, ((Φ a).toLinearMap A).1 y⟫_ℂ) l
      (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ)) (A : TraceClass H) (hA : 0 ≤ A.1) :
    (traceCLM (Ψ A)).re ≤ (traceCLM A).re := by
  have hdiag (x : K) : Tendsto (fun a ↦ ⟪((Φ a).toLinearMap A).1 x, x⟫_ℂ) l
      (𝓝 ⟪(Ψ A).1 x, x⟫_ℂ) := by
    convert (hlim A x x).star using 1
    · ext a; exact (inner_conj_symm _ _).symm
    · congr 1; exact (inner_conj_symm _ _).symm
  obtain ⟨_, hclass, hbound⟩ := InfiniteTraceClassWeakLimit.traceClass_of_diagonal_tendsto
    (fun a ↦ ((Φ a).toLinearMap A).1) (Ψ A).1
    (fun a ↦ (Φ a).map_nonneg A hA) (fun a ↦ ((Φ a).toLinearMap A).2)
    (traceCLM A).re
    (fun a ↦ le_of_eq (congrArg Complex.re ((Φ a).trace_preserving A))) hdiag
  exact hbound

/-- The closure properties needed before completing the lost trace by a
replacement state. No CP or trace-nonincreasing premise is required. -/
theorem channel_weakLimit_properties (Φ : α → QuantumChannel H K)
    (Ψ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hlim : ∀ A x y, Tendsto (fun a ↦ ⟪x, ((Φ a).toLinearMap A).1 y⟫_ℂ) l
      (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ)) :
    IsCompletelyPositive Ψ ∧
      (∀ A : TraceClass H, 0 ≤ A.1 → 0 ≤ (Ψ A).1) ∧
      (∀ A : TraceClass H, 0 ≤ A.1 → (traceCLM (Ψ A)).re ≤ (traceCLM A).re) :=
  ⟨isCompletelyPositive_of_channel_weakLimit Φ Ψ hlim,
    nonneg_of_channel_weakLimit Φ Ψ hlim, trace_le_of_channel_weakLimit Φ Ψ hlim⟩

end
end Cloning.InfiniteTraceClass
