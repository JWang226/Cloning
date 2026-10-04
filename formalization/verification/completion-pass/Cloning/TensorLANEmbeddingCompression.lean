import Cloning.TensorLANEmbeddingTotal

/-! The concrete frame channels discard exactly the complementary physical
cutoff trace; the identity holds on all complex trace-class inputs. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.InfiniteTraceClass
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {H K J : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

theorem conjugationLinearMap_trace_eq_of_norm_eq (V : H →L[ℂ] K) (W : H →L[ℂ] J)
    (hVW : ∀ x, ‖V x‖ = ‖W x‖) (A : TraceClass H) :
    traceCLM (conjugationLinearMap V A) = traceCLM (conjugationLinearMap W A) := by
  have hpositive (B : TraceClass H) (hB : 0 ≤ B.1) :
      traceCLM (conjugationLinearMap V B) = traceCLM (conjugationLinearMap W B) := by
    obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
    have hl := (conjugationLinearMap_positive_hasSum V B hB b).mapL traceCLM
    have hr := (conjugationLinearMap_positive_hasSum W B hB b).mapL traceCLM
    simp only [traceCLM_vectorProjector, hVW] at hl
    simp only [traceCLM_vectorProjector] at hr
    exact hl.unique hr
  let D : TraceClass H →ₗ[ℂ] ℂ := traceCLM.toLinearMap.comp (conjugationLinearMap V) -
    traceCLM.toLinearMap.comp (conjugationLinearMap W)
  have hpos (B : TraceClass H) (hB : 0 ≤ B.1) : D B = 0 := sub_eq_zero.mpr (hpositive B hB)
  have hself (B : TraceClass H) (hB : IsSelfAdjoint B.1) : D B = 0 := by
    rw [← TraceClass.positivePart_sub_negativePart B hB, map_sub,
      hpos _ (TraceClass.positivePart_nonneg B hB),
      hpos _ (TraceClass.negativePart_nonneg B hB), sub_self]
  have hz : D A = 0 := by
    rw [← TraceClass.realComponent_add_I_smul_imaginaryComponent A, map_add, map_smul,
      hself _ (TraceClass.realComponent_isSelfAdjoint A),
      hself _ (TraceClass.imaginaryComponent_isSelfAdjoint A)]
    simp
  exact sub_eq_zero.mp hz

end Cloning.InfiniteTraceClass

namespace Cloning.TensorLAN
open Cloning.InfiniteTraceClass
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type*} [Fintype ι]
variable (S : Submodule ℂ H) [S.HasOrthogonalProjection]

/-- The transported compression has precisely the retained physical trace. -/
theorem frameTransport_compressed_trace (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (A : TraceClass H) :
    traceCLM (conjugationLinearMap (frameTransport S b f hf) A) =
      traceCLM (sandwichCLM S.starProjection S.starProjection A) := by
  have he := conjugationLinearMap_trace_eq_of_norm_eq (frameTransport S b f hf) S.starProjection
    (fun x => by
      change ‖basisFrameIsometry S b f hf (S.orthogonalProjection x)‖ = ‖S.starProjection x‖
      rw [LinearIsometry.norm_map]
      rfl) A
  rw [he]
  congr 1
  apply Subtype.ext
  ext x
  have hp : S.starProjection.adjoint = S.starProjection := isSelfAdjoint_starProjection S
  simp only [conjugationLinearMap_coe, operatorConjugation_apply, sandwichCLM_coe,
    ContinuousLinearMap.mul_apply, hp]

/-- The lost-trace coefficient is exactly the complementary cutoff block. -/
theorem frameTransport_trace_defect (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (A : TraceClass H) :
    traceCLM A - traceCLM (conjugationLinearMap (frameTransport S b f hf) A) =
      traceCLM (sandwichCLM (1 - S.starProjection) (1 - S.starProjection) A) := by
  rw [frameTransport_compressed_trace]
  have he := traceCLM_projection_split (isStarProjection_starProjection (U := S)) A
  linear_combination -he

/-- Exact all-input compression/transport/replacement formula. -/
theorem frameForwardChannel_apply (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (σ : DensityState K) (A : TraceClass H) :
    (frameForwardChannel S b f hf σ).toLinearMap A =
      conjugationLinearMap (frameTransport S b f hf) A +
        traceCLM (sandwichCLM (1 - S.starProjection) (1 - S.starProjection) A) •
          TraceClass.ofOperator σ.op σ.traceClass := by
  rw [frameForwardChannel, QuantumChannel.ofContraction_apply, frameTransport_trace_defect]

/-- The trace-norm cost of replacing the discarded physical tail. -/
theorem frameForwardChannel_lost_trace (b : OrthonormalBasis ι ℂ S)
    (f : ι → K) (hf : Orthonormal ℂ f) (σ : DensityState K)
    (A : TraceClass H) (hA : 0 ≤ A.1) :
    ‖(frameForwardChannel S b f hf σ).toLinearMap A -
      conjugationLinearMap (frameTransport S b f hf) A‖ =
        (traceCLM (sandwichCLM (1 - S.starProjection) (1 - S.starProjection) A)).re := by
  rw [frameForwardChannel, QuantumChannel.ofContraction_repair_error _ _ _ A hA,
    ← Complex.sub_re, frameTransport_trace_defect]

end Cloning.TensorLAN
