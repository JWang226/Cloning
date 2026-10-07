import Cloning.InfiniteTraceClassNormalPart

/-! The analytic trace pairing, bundled as a continuous linear map in its
trace-class argument as well as its bounded-observable argument. -/

namespace Cloning.InfiniteTraceClass

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bilinear analytic trace pairing, with norm at most one. -/
def tracePairingCLM : TraceClass H →L[ℂ] ((H →L[ℂ] H) →L[ℂ] ℂ) :=
  LinearMap.mkContinuous
    { toFun := tracePairing
      map_add' := by
        intro A B
        ext W
        change traceCLM (traceClassRightMultiply (A + B) W) =
          traceCLM (traceClassRightMultiply A W) + traceCLM (traceClassRightMultiply B W)
        have heq : traceClassRightMultiply (A + B) W =
            traceClassRightMultiply A W + traceClassRightMultiply B W := by
          apply Subtype.ext
          change (A.1 + B.1) * W = A.1 * W + B.1 * W
          exact add_mul _ _ _
        rw [heq, map_add]
      map_smul' := by
        intro c A
        ext W
        change traceCLM (traceClassRightMultiply (c • A) W) =
          c • traceCLM (traceClassRightMultiply A W)
        have heq : traceClassRightMultiply (c • A) W =
            c • traceClassRightMultiply A W := by
          apply Subtype.ext
          change (c • A.1) * W = c • (A.1 * W)
          exact smul_mul_assoc _ _ _
        rw [heq, map_smul] }
    1 (fun T => by
      have ht : ‖(traceCLM : TraceClass H →L[ℂ] ℂ)‖ ≤ 1 := by
        apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro A
        simpa using norm_trace_le_traceNorm A.2
      have hmul : ‖traceClassRightMultiply T‖ ≤ ‖T‖ := by
        unfold traceClassRightMultiply
        exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul ht hmul (norm_nonneg _) zero_le_one))

@[simp] theorem tracePairingCLM_apply (T : TraceClass H) :
    tracePairingCLM T = tracePairing T := rfl

theorem norm_tracePairingCLM_le :
    ‖(tracePairingCLM : TraceClass H →L[ℂ] ((H →L[ℂ] H) →L[ℂ] ℂ))‖ ≤ 1 := by
  unfold tracePairingCLM
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

end
end Cloning.InfiniteTraceClass
