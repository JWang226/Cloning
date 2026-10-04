import Cloning.HeisenbergDual
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Partial trace of an actual Hilbert-sum vector, constructed as a convergent
series in the trace norm. The summand vectors need not be normalized. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexOrder ENNReal

namespace Cloning.WeylGNS
open InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {ι K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem component_norm_sq_hasSum (v : lp (fun _ : ι => K) 2) :
    HasSum (fun i => ‖v i‖ ^ 2) (‖v‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) v

theorem component_projector_summable (v : lp (fun _ : ι => K) 2) :
    Summable (fun i => vectorProjector (v i)) := by
  apply Summable.of_norm
  simpa only [norm_vectorProjector] using (component_norm_sq_hasSum v).summable

def componentState (v : lp (fun _ : ι => K) 2) : TraceClass K :=
  ∑' i, vectorProjector (v i)

theorem componentState_nonneg (v : lp (fun _ : ι => K) 2) :
    0 ≤ (componentState v).1 := by
  change 0 ≤ inclusionCLM (componentState v)
  rw [componentState, ContinuousLinearMap.map_tsum _ (component_projector_summable v)]
  apply tsum_nonneg
  intro i
  exact (InnerProductSpace.rankOne ℂ (v i) (v i)).nonneg_iff_isPositive.mpr
    (InnerProductSpace.isPositive_rankOne_self (v i))

theorem componentState_trace (v : lp (fun _ : ι => K) 2) :
    traceCLM (componentState v) = (‖v‖ ^ 2 : ℝ) := by
  rw [componentState, ContinuousLinearMap.map_tsum _ (component_projector_summable v)]
  simp only [traceCLM_vectorProjector]
  exact (Complex.hasSum_ofReal.mpr (component_norm_sq_hasSum v)).tsum_eq

theorem componentState_pairing (v : lp (fun _ : ι => K) 2) (A : K →L[ℂ] K) :
    tracePairing (componentState v) A = ∑' i, ⟪v i, A (v i)⟫_ℂ := by
  have h := (component_projector_summable v).hasSum.mapL
    ((ContinuousLinearMap.apply ℂ ℂ A).comp tracePairingCLM)
  change HasSum (fun i => tracePairing (vectorProjector (v i)) A)
    (tracePairing (componentState v) A) at h
  have he (i : ι) : tracePairing (vectorProjector (v i)) A = ⟪v i, A (v i)⟫_ℂ :=
    tracePairing_rankOneOperator (v i) (v i) A
  simp_rw [he] at h
  exact h.tsum_eq.symm

end Cloning.WeylGNS
