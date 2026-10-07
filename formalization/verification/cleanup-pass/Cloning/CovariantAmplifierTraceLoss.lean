import Cloning.HeisenbergDualResidual

/-! Covariant trace-nonincreasing maps inherit channel moment bounds with the
exact output trace retained, including the zero-success case. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexOrder
namespace Cloning.CovariantAmplifier
open InfiniteTraceClass MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

/-- Normalize the actual covariant CP map, apply a normalized-channel moment
bound, and restore its exact success trace. No success-probability parameter or
normalization premise on the competing map is supplied. -/
theorem covariant_tni_trace_scaled_moment_le
    (r : ℝ) (A : TraceClass (Fock d)) (hA : traceCLM A=1)
    (W : Fock d →L[ℂ] Fock d) (C : ℝ)
    (hmoment : ∀ Φ : QuantumChannel (Fock d) (Fock d),
      (∀ a T, Φ.toLinearMap (displacementTraceMap a T)=
        displacementTraceMap (r • a) (Φ.toLinearMap T)) →
      (tracePairing (Φ.toLinearMap A) W).re≤C)
    (Γ : TraceClass (Fock d) →ₗ[ℂ] TraceClass (Fock d))
    (hCP : IsCompletelyPositive Γ)
    (htrace : ∀ T, 0≤T.1 → (traceCLM (Γ T)).re≤(traceCLM T).re)
    (hcov : ∀ a T, Γ (displacementTraceMap a T)=displacementTraceMap (r • a) (Γ T)) :
    (tracePairing (Γ A) W).re≤(traceCLM (Γ A)).re*C := by
  rcases covariant_cpTNI_zero_or_scaled_channel Γ hCP.map_nonneg hCP htrace r hcov with
    hz | ⟨c,Φ,hc,_,heq,hΦ⟩
  · rw [hz]
    simp only [LinearMap.zero_apply, ← tracePairingCLM_apply, map_zero,
      ContinuousLinearMap.zero_apply, Complex.zero_re, zero_mul, le_refl]
  · have hs : (tracePairing (Γ A) W).re=c*(tracePairing (Φ.toLinearMap A) W).re := by
      rw [heq]
      change (tracePairingCLM ((c : ℂ) • Φ.toLinearMap A) W).re=_
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        tracePairingCLM_apply]
    have ht : traceCLM (Φ.toLinearMap A)=traceCLM A :=
      Φ.toPositiveTracePreservingMap.trace_preserving A
    have hmass : (traceCLM (Γ A)).re=c := by
      rw [heq]
      change (traceCLM ((c : ℂ) • Φ.toLinearMap A)).re=c
      rw [map_smul, ht, hA]
      simp
    rw [hs, hmass]
    exact mul_le_mul_of_nonneg_left (hmoment Φ hΦ) hc.le

end Cloning.CovariantAmplifier
