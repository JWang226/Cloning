import Cloning.InfiniteCompletelyPositive
import Cloning.InfiniteTraceClassCutoffConvergence

/-! Actual finite-output CPTP cutoffs, converging in trace norm uniformly on
compact sets of positive trace-class operators. -/

namespace Cloning.InfiniteTraceClass

noncomputable section
open Filter Topology
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [DecidableEq ι]

/-- The explicit finite basis cutoff, with complete positivity proved. -/
def QuantumChannel.finiteBasisCutoff (b : HilbertBasis ι ℂ H) (i₀ : ι)
    (s : Finset ι) : QuantumChannel H H where
  toPositiveTracePreservingMap := Cloning.InfiniteTraceClass.finiteBasisCutoff b i₀ s
  completelyPositive := projectionReplacement_completelyPositive
    (basisProjection b (insert i₀ s))
    (basisProjection_isStarProjection b (insert i₀ s))
    (DensityState.pure (b i₀) (b.orthonormal.norm_eq_one i₀))

theorem QuantumChannel.finiteBasisCutoff_supported (b : HilbertBasis ι ℂ H)
    (i₀ : ι) (s : Finset ι) (A : TraceClass H) :
    basisProjection b (insert i₀ s) *
        ((QuantumChannel.finiteBasisCutoff b i₀ s).toLinearMap A).1 *
        basisProjection b (insert i₀ s) =
      ((QuantumChannel.finiteBasisCutoff b i₀ s).toLinearMap A).1 :=
  Cloning.InfiniteTraceClass.finiteBasisCutoff_supported b i₀ s A

theorem QuantumChannel.finiteBasisCutoff_finiteDimensional_range
    (b : HilbertBasis ι ℂ H) (i₀ : ι) (s : Finset ι) (A : TraceClass H) :
    FiniteDimensional ℂ
      (LinearMap.range ((QuantumChannel.finiteBasisCutoff b i₀ s).toLinearMap A).1.toLinearMap) :=
  Cloning.InfiniteTraceClass.finiteBasisCutoff_finiteDimensional_range b i₀ s A

theorem QuantumChannel.finiteBasisCutoff_tendsto (b : HilbertBasis ι ℂ H)
    (i₀ : ι) (A : TraceClass H) (hA : 0 ≤ A.1) :
    Tendsto (fun s : Finset ι => (QuantumChannel.finiteBasisCutoff b i₀ s).toLinearMap A)
      atTop (𝓝 A) :=
  Cloning.InfiniteTraceClass.finiteBasisCutoff_tendsto b i₀ A hA

theorem QuantumChannel.finiteBasisCutoff_tendstoUniformlyOn
    (b : HilbertBasis ι ℂ H) (i₀ : ι) {S : Set (TraceClass H)}
    (hS : IsCompact S) (hpos : ∀ A ∈ S, 0 ≤ A.1) :
    TendstoUniformlyOn
      (fun s : Finset ι => (QuantumChannel.finiteBasisCutoff b i₀ s).toLinearMap)
      (fun A => A) atTop S :=
  Cloning.InfiniteTraceClass.finiteBasisCutoff_tendstoUniformlyOn b i₀ hS hpos

end
end Cloning.InfiniteTraceClass
