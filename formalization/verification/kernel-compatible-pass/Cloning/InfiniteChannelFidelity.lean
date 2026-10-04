import Cloning.InfiniteFidelityBlockBound
import Cloning.InfiniteFidelityWitness
import Cloning.InfiniteChannelAdjoint

/-!
# Fidelity data processing for genuine infinite-dimensional quantum channels

Complete positivity transports the constructed attaining operator block.
Trace preservation retains its objective, and the proved block trace bound
compares that objective with the output root fidelity.
-/

namespace Cloning.InfiniteFidelity

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace BigOperators
open InfiniteTraceClass

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Complete positivity and the derived adjoint law preserve fidelity blocks. -/
theorem channel_fidelityBlock (Φ : QuantumChannel H K) (A B X : TraceClass H)
    (hblock : BlockPositive (fidelityBlock A B X)) :
    BlockPositive (fidelityBlock (Φ.toLinearMap A) (Φ.toLinearMap B) (Φ.toLinearMap X)) := by
  have heq : fidelityBlock (Φ.toLinearMap A) (Φ.toLinearMap B) (Φ.toLinearMap X) =
      fun i j => Φ.toLinearMap (fidelityBlock A B X i j) := by
    funext i j
    dsimp only [fidelityBlock]
    split_ifs <;> try rfl
    exact (Φ.toPositiveTracePreservingMap.map_adjoint X).symm
  rw [heq]
  exact Φ.completelyPositive 2 _ hblock

/-- The two-vector form of the canonical block positivity condition. -/
lemma fidelityBlock_quadratic (A B X : TraceClass H)
    (hblock : BlockPositive (fidelityBlock A B X)) (x y : H) :
    0 ≤ ⟪x, A.1 x⟫_ℂ + ⟪x, X.1 y⟫_ℂ +
      ⟪y, (star X.1) x⟫_ℂ + ⟪y, B.1 y⟫_ℂ := by
  simpa [fidelityBlock, Fin.sum_univ_two, TraceClass.adjoint, add_assoc] using hblock ![x, y]

/-- Root fidelity is nondecreasing under an actual completely positive
trace-preserving map on arbitrary trace-class Hilbert-space operators. -/
theorem fidelity_data_processing (Φ : QuantumChannel H K) (A B : TraceClass H)
    (hA : 0 ≤ A.1) (hB : 0 ≤ B.1) :
    fidelity A.1 B.1 hA hB A.2 B.2 ≤
      fidelity (Φ.toLinearMap A).1 (Φ.toLinearMap B).1
        (Φ.toPositiveTracePreservingMap.map_nonneg A hA)
        (Φ.toPositiveTracePreservingMap.map_nonneg B hB)
        (Φ.toLinearMap A).2 (Φ.toLinearMap B).2 := by
  obtain ⟨X, hblock, htrace⟩ := exists_fidelityBlock_witness A B hA hB
  have hout := channel_fidelityBlock Φ A B X hblock
  have h := trace_re_le_fidelity_of_block (Φ.toLinearMap A) (Φ.toLinearMap B)
    (Φ.toLinearMap X) (Φ.toPositiveTracePreservingMap.map_nonneg A hA)
    (Φ.toPositiveTracePreservingMap.map_nonneg B hB)
    (fidelityBlock_quadratic _ _ _ hout)
  have ht : traceCLM (Φ.toLinearMap X) = traceCLM X :=
    Φ.toPositiveTracePreservingMap.trace_preserving X
  rwa [ht, htrace] at h

/-- Data processing for the actual normalized analytic density states. -/
theorem stateFidelity_data_processing (Φ : QuantumChannel H K) (ρ σ : DensityState H) :
    stateFidelity ρ σ ≤
      stateFidelity (Φ.toPositiveTracePreservingMap.mapState ρ)
        (Φ.toPositiveTracePreservingMap.mapState σ) :=
  fidelity_data_processing Φ (TraceClass.ofOperator ρ.op ρ.traceClass)
    (TraceClass.ofOperator σ.op σ.traceClass) ρ.positive σ.positive

end
end Cloning.InfiniteFidelity
