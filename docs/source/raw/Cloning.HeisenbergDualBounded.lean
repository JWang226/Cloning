import Cloning.HeisenbergDual

noncomputable section
namespace Cloning.InfiniteTraceClass
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

set_option backward.isDefEq.respectTransparency true in
/-- Boundedness of the reconstructed dual follows from the exact trace norm
of rank-one operators and the norm-one trace pairing. -/
theorem heisenbergDual_norm_le (Φ : TraceClass H →L[ℂ] TraceClass K)
    (A : K →L[ℂ] K) : ‖heisenbergDual Φ A‖ ≤ ‖Φ‖ * ‖A‖ := by
  change ‖traceClassDualOp (((tracePairingCLM (H := K)).flip A).comp Φ)‖ ≤ _
  refine (norm_traceClassDualOp_le (H := H) (((tracePairingCLM (H := K)).flip A).comp Φ)).trans ?_
  refine (ContinuousLinearMap.opNorm_comp_le ((tracePairingCLM (H := K)).flip A) Φ).trans ?_
  have hpair : ‖(tracePairingCLM (H := K)).flip A‖ ≤ ‖A‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro T
    change ‖tracePairing T A‖ ≤ ‖A‖ * ‖T‖
    calc
      _ ≤ ‖tracePairing T‖ * ‖A‖ := (tracePairing T).le_opNorm A
      _ ≤ ‖T‖ * ‖A‖ := mul_le_mul_of_nonneg_right
        ((tracePairingCLM.le_opNorm T).trans (by
          simpa using mul_le_mul_of_nonneg_right (norm_tracePairingCLM_le (H := K)) (norm_nonneg T)))
        (norm_nonneg A)
      _ = _ := mul_comm _ _
  exact (mul_le_mul_of_nonneg_right hpair (norm_nonneg Φ)).trans_eq (mul_comm _ _)

/-- The dual is a continuous linear map for operator norms as well. -/
def heisenbergDualCLM (Φ : TraceClass H →L[ℂ] TraceClass K) :
    (K →L[ℂ] K) →L[ℂ] (H →L[ℂ] H) :=
  (heisenbergDual Φ).mkContinuous ‖Φ‖ (heisenbergDual_norm_le Φ)

end Cloning.InfiniteTraceClass
