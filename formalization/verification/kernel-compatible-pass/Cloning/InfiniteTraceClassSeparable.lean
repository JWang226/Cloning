import Cloning.InfiniteTraceClassDecomposition
import Cloning.InfiniteTraceClassChannels
import Cloning.InfinitePureStateContinuity
import Mathlib.Topology.Algebra.Module.Basic

/-! Separability of the actual trace-class Banach space over a separable Hilbert space.
Positive operators are trace-norm limits of sums of vector projectors. Jordan and real/imaginary
decompositions then give density of the complex span of these projectors for all operators. -/

namespace Cloning.InfiniteTraceClass

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter TopologicalSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma continuous_vectorProjector : Continuous (vectorProjector : H → TraceClass H) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact vectorProjector_tendsto (tendsto_id : Tendsto (fun y : H => y) (𝓝 x) (𝓝 x))

/-- The complex span of actual vector projectors. -/
def projectorSpan : Submodule ℂ (TraceClass H) :=
  Submodule.span ℂ (Set.range (vectorProjector : H → TraceClass H))

lemma vectorProjector_mem_projectorSpan (x : H) : vectorProjector x ∈ projectorSpan (H := H) :=
  Submodule.subset_span (Set.mem_range_self x)

lemma nonneg_mem_projectorSpan_closure (A : TraceClass H) (hA : 0 ≤ A.1) :
    A ∈ (projectorSpan (H := H)).topologicalClosure := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hs := positive_rankOne_series hA A.2 b
  apply (projectorSpan (H := H)).isClosed_topologicalClosure.mem_of_tendsto hs
  apply Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro i hi
  exact (projectorSpan (H := H)).le_topologicalClosure
    (vectorProjector_mem_projectorSpan _)

lemma selfAdjoint_mem_projectorSpan_closure (A : TraceClass H) (hA : IsSelfAdjoint A.1) :
    A ∈ (projectorSpan (H := H)).topologicalClosure := by
  rw [← TraceClass.positivePart_sub_negativePart A hA]
  exact Submodule.sub_mem _
    (nonneg_mem_projectorSpan_closure _ (TraceClass.positivePart_nonneg A hA))
    (nonneg_mem_projectorSpan_closure _ (TraceClass.negativePart_nonneg A hA))

lemma mem_projectorSpan_closure (A : TraceClass H) :
    A ∈ (projectorSpan (H := H)).topologicalClosure := by
  rw [← TraceClass.realComponent_add_I_smul_imaginaryComponent A]
  apply Submodule.add_mem
  · exact selfAdjoint_mem_projectorSpan_closure _ (TraceClass.realComponent_isSelfAdjoint A)
  · exact Submodule.smul_mem _ _
      (selfAdjoint_mem_projectorSpan_closure _ (TraceClass.imaginaryComponent_isSelfAdjoint A))

lemma dense_projectorSpan : Dense (projectorSpan (H := H) : Set (TraceClass H)) := by
  intro A
  exact mem_projectorSpan_closure A

/-- The trace-norm topology is separable whenever the underlying Hilbert topology is separable. -/
instance instSeparableSpaceTraceClass [SeparableSpace H] : SeparableSpace (TraceClass H) := by
  apply dense_projectorSpan.isSeparable_iff.mp
  exact (isSeparable_range continuous_vectorProjector).span

end
end Cloning.InfiniteTraceClass
