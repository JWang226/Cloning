import Cloning.InfiniteIsometricChannel

/-! An actual CPTP left inverse of every Hilbert-space isometric embedding.
The adjoint compression is completed by a fixed state on the discarded
subspace. No trace bound or recovery identity is assumed. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
namespace Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem conjugation_trace_le_of_contraction (V : H →L[ℂ] K)
    (hV : ∀ x, ‖V x‖ ≤ ‖x‖) (A : TraceClass H) (hA : 0 ≤ A.1) :
    (traceCLM (conjugationLinearMap V A)).re ≤ (traceCLM A).re := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hs := Complex.hasSum_re
    ((conjugationLinearMap_positive_hasSum V A hA b).mapL traceCLM)
  have ht := positive_rankOne_mass hA A.2 b
  simp only [traceCLM_vectorProjector, Complex.ofReal_re] at hs
  simp only [norm_vectorProjector] at ht
  change HasSum (fun i : w => ‖CFC.sqrt A.1 (b i)‖ ^ 2) (traceCLM A).re at ht
  rw [← hs.tsum_eq, ← ht.tsum_eq]
  exact Summable.tsum_le_tsum
    (fun i => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hV _))
    hs.summable ht.summable

theorem isometry_adjoint_apply_self (V : H →ₗᵢ[ℂ] K) (x : H) :
    V.toContinuousLinearMap.adjoint (V x) = x := by
  have h := V.toContinuousLinearMap.norm_map_iff_adjoint_comp_self.mp V.norm_map
  exact congrArg (fun T : H →L[ℂ] H => T x) h

theorem isometry_adjoint_norm_le (V : H →ₗᵢ[ℂ] K) (y : K) :
    ‖V.toContinuousLinearMap.adjoint y‖ ≤ ‖y‖ := by
  have hn : ‖V.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  have ha : ‖V.toContinuousLinearMap.adjoint‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hn
  exact (V.toContinuousLinearMap.adjoint.le_opNorm y).trans
    (by simpa using mul_le_mul_of_nonneg_right ha (norm_nonneg y))

/-- Adjoint compression with exact replacement of the missing trace. -/
def QuantumChannel.isometricRecovery (V : H →ₗᵢ[ℂ] K) (σ : DensityState H) :
    QuantumChannel K H :=
  QuantumChannel.traceRepair (conjugationLinearMap V.toContinuousLinearMap.adjoint)
    (conjugationLinearMap_completelyPositive _)
    (conjugation_trace_le_of_contraction _ (isometry_adjoint_norm_le V)) σ

theorem QuantumChannel.isometricRecovery_apply (V : H →ₗᵢ[ℂ] K)
    (σ : DensityState H) (A : TraceClass K) :
    (isometricRecovery V σ).toLinearMap A =
      conjugationLinearMap V.toContinuousLinearMap.adjoint A +
        (traceCLM A - traceCLM (conjugationLinearMap V.toContinuousLinearMap.adjoint A)) •
          TraceClass.ofOperator σ.op σ.traceClass := rfl

theorem conjugation_adjoint_isometry_cancel (V : H →ₗᵢ[ℂ] K) (A : TraceClass H) :
    conjugationLinearMap V.toContinuousLinearMap.adjoint
      (conjugationLinearMap V.toContinuousLinearMap A) = A := by
  apply Subtype.ext
  ext x
  change V.toContinuousLinearMap.adjoint
    (V (A.1 (V.toContinuousLinearMap.adjoint
      (V.toContinuousLinearMap.adjoint.adjoint x)))) = A.1 x
  rw [ContinuousLinearMap.adjoint_adjoint]
  change V.toContinuousLinearMap.adjoint
    (V (A.1 (V.toContinuousLinearMap.adjoint (V x)))) = A.1 x
  rw [isometry_adjoint_apply_self, isometry_adjoint_apply_self]

/-- Recovery holds for all trace-class inputs, including nonpositive ones. -/
theorem QuantumChannel.isometricRecovery_leftInverse (V : H →ₗᵢ[ℂ] K)
    (σ : DensityState H) (A : TraceClass H) :
    (isometricRecovery V σ).toLinearMap ((ofIsometry V).toLinearMap A) = A := by
  rw [isometricRecovery_apply]
  change conjugationLinearMap V.toContinuousLinearMap.adjoint
      (conjugationLinearMap V.toContinuousLinearMap A) +
    (traceCLM (conjugationLinearMap V.toContinuousLinearMap A) -
      traceCLM (conjugationLinearMap V.toContinuousLinearMap.adjoint
        (conjugationLinearMap V.toContinuousLinearMap A))) • _ = A
  rw [conjugation_adjoint_isometry_cancel, conjugationLinearMap_isometry_trace]
  simp

theorem QuantumChannel.isometricRecovery_vectorProjector (V : H →ₗᵢ[ℂ] K)
    (σ : DensityState H) (x : H) :
    (isometricRecovery V σ).toLinearMap (vectorProjector (V x)) = vectorProjector x := by
  rw [← ofIsometry_vectorProjector V x]
  exact isometricRecovery_leftInverse V σ _

end Cloning.InfiniteTraceClass
