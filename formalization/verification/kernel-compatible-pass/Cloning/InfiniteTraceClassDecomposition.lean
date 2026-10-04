import Cloning.InfiniteTraceClassSeries
import Cloning.InfiniteTraceClassPositive

/-!
# Positive trace-class operators as trace-norm sums of rank-one operators

For any Hilbert basis, a positive trace-class operator A has the actual
trace-norm convergent expansion Σᵢ |√A eᵢ⟩⟨√A eᵢ|. No spectral decomposition
or finite-rank approximation hypothesis is assumed.
-/

namespace Cloning.InfiniteTraceClass

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positive_rankOne_series {A : H →L[ℂ] H} (hA : 0 ≤ A)
    (hTC : IsTraceClass A) {w : Set H} (b : HilbertBasis w ℂ H) :
    HasSum (fun i : w => vectorProjector (CFC.sqrt A (b i)))
      (TraceClass.ofOperator A hTC) := by
  have hsquare := HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b
    (isHilbertSchmidt_sqrt hA hTC)
  have hs : Summable (fun i : w => vectorProjector (CFC.sqrt A (b i))) := by
    apply Summable.of_norm
    simpa only [norm_vectorProjector] using hsquare
  have heq : (∑' i : w, vectorProjector (CFC.sqrt A (b i))) =
      TraceClass.ofOperator A hTC := by
    apply Subtype.ext
    ext y
    have hleft := (hs.hasSum.mapL inclusionCLM).mapL
      (ContinuousLinearMap.apply ℂ H y)
    have hright := (b.hasSum_repr (CFC.sqrt A y)).mapL (CFC.sqrt A)
    have hsq : CFC.sqrt A (CFC.sqrt A y) = A y := by
      change (CFC.sqrt A * CFC.sqrt A) y = A y
      rw [CFC.sqrt_mul_sqrt_self A hA]
    rw [hsq] at hright
    have hsym := (CFC.sqrt_nonneg A).isSelfAdjoint.isSymmetric
    have hterms : (fun i : w =>
        (ContinuousLinearMap.apply ℂ H y) (inclusionCLM
          (vectorProjector (CFC.sqrt A (b i))))) =
        (fun i : w => CFC.sqrt A (b.repr (CFC.sqrt A y) i • b i)) := by
      funext i
      simp only [ContinuousLinearMap.apply_apply, inclusionCLM_apply, vectorProjector,
        TraceClass.ofOperator_coe, InnerProductSpace.rankOne_apply, map_smul,
        HilbertBasis.repr_apply_apply]
      exact congrArg (fun z : ℂ => z • CFC.sqrt A (b i)) (hsym (b i) y)
    rw [hterms] at hleft
    exact hleft.unique hright
  exact heq ▸ hs.hasSum

theorem positive_rankOne_mass {A : H →L[ℂ] H} (hA : 0 ≤ A)
    (hTC : IsTraceClass A) {w : Set H} (b : HilbertBasis w ℂ H) :
    HasSum (fun i : w => ‖vectorProjector (CFC.sqrt A (b i))‖)
      (trace A hTC).re := by
  simp only [norm_vectorProjector]
  exact (tsum_sqrt_norm_sq_eq_trace_re hA hTC b) ▸
    (HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b
      (isHilbertSchmidt_sqrt hA hTC)).hasSum

end
end Cloning.InfiniteTraceClass
