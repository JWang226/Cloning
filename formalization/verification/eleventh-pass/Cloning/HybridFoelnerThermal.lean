import Cloning.HybridFoelnerResidual

/-! The sharp thermal witness bound for the quantum residual of a hybrid
Følner limit. The classical trace factor survives normalization exactly. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass
open Cloning.MultimodeCoherent Cloning.MultimodeCoherentGaussianMixture Cloning.ThermalWitness
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {k s : ℕ}

/-- A covariant CP residual of success mass at most `c` has witness moment
at most `c` times the actual universal thermal least-noise value. -/
theorem covariant_scaled_thermal_witness_moment_le
    (Γ : TraceClass (Fock s) →ₗ[ℂ] TraceClass (Fock s))
    (hΓ : IsCompletelyPositive Γ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (htrace : ∀ X, 0 ≤ X.1 → (traceCLM (Γ X)).re ≤ c * (traceCLM X).re)
    (r : ℝ) (hr : 1 < r ^ 2)
    (hcov : ∀ z X, Γ (displacementTraceMap z X) = displacementTraceMap (r • z) (Γ X))
    {q : Fin s → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    (tracePairing (Γ (vectorMixture (numberBasis s) (productGeometric q)))
      (productWitnessOperator (numberBasis s) q (fun i => Thermal.amplified (r ^ 2) (q i)))).re ≤
      c * ∏ i, Thermal.fidelity (q i) (Thermal.amplified (r ^ 2) (q i)) := by
  have hF : 0 ≤ ∏ i, Thermal.fidelity (q i) (Thermal.amplified (r ^ 2) (q i)) := by
    apply Finset.prod_nonneg
    intro i _
    exact (Thermal.fidelity_pos (hq0 i).le (hq1 i)
      ((hq0 i).trans (Thermal.lt_amplified hr (hq1 i))).le
      (Thermal.amplified_lt_one (by linarith) (hq1 i))).le
  have hTNI (X : TraceClass (Fock s)) (hX : 0 ≤ X.1) :
      (traceCLM (Γ X)).re ≤ (traceCLM X).re :=
    (htrace X hX).trans (mul_le_of_le_one_left (trace_re_nonneg hX X.2) hc1)
  rcases covariant_cpTNI_zero_or_scaled_channel Γ hΓ.map_nonneg hΓ hTNI r hcov with
    hzero | ⟨v, Φ, hv, _, heq, hΦ⟩
  · subst Γ
    simpa only [LinearMap.zero_apply, ← tracePairingCLM_apply, map_zero,
      ContinuousLinearMap.zero_apply, Complex.zero_re] using mul_nonneg hc0 hF
  · have hvc : v ≤ c := by
      have ht := htrace (coherentProjector 0) (coherentProjector_nonneg 0)
      rw [heq] at ht
      change (traceCLM ((v : ℂ) • Φ.toLinearMap (coherentProjector 0))).re ≤ _ at ht
      have htp : traceCLM (Φ.toLinearMap (coherentProjector 0)) =
          traceCLM (coherentProjector 0) := Φ.trace_preserving _
      rw [map_smul, htp, coherentProjector_trace] at ht
      simpa only [smul_eq_mul, mul_one, Complex.ofReal_re, Complex.one_re] using ht
    have hs : (tracePairing (Γ (vectorMixture (numberBasis s) (productGeometric q)))
        (productWitnessOperator (numberBasis s) q
          (fun i => Thermal.amplified (r ^ 2) (q i)))).re =
        v * (tracePairing (Φ.toLinearMap (vectorMixture (numberBasis s) (productGeometric q)))
          (productWitnessOperator (numberBasis s) q
            (fun i => Thermal.amplified (r ^ 2) (q i)))).re := by
      rw [heq]
      change (tracePairingCLM ((v : ℂ) • _) _).re = _
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        tracePairingCLM_apply]
    rw [hs]
    exact (mul_le_mul_of_nonneg_left
      (covariant_thermal_witness_moment_le Φ r hΦ hr hq0 hq1) hv.le).trans
      (mul_le_mul_of_nonneg_right hvc hF)

/-- The residual extracted from a hybrid Gaussian model has moment at most
the product of the classical and orbital factors, including dimension zero. -/
theorem hybrid_residual_thermal_witness_moment_le
    (Γ : TraceClass (Fock s) →ₗ[ℂ] TraceClass (Fock s))
    (hΓ : IsCompletelyPositive Γ) (g : ℝ) (hg : 1 < g)
    (htrace : ∀ X, 0 ≤ X.1 → (traceCLM (Γ X)).re ≤
      Thermal.classicalBase g ^ ((k : ℝ) / 2) * (traceCLM X).re)
    (hcov : ∀ z X, Γ (displacementTraceMap z X) =
      displacementTraceMap (Real.sqrt g • z) (Γ X))
    {q : Fin s → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    (tracePairing (Γ (vectorMixture (numberBasis s) (productGeometric q)))
      (productWitnessOperator (numberBasis s) q (fun i => Thermal.amplified g (q i)))).re ≤
      Thermal.classicalBase g ^ ((k : ℝ) / 2) *
        ∏ i, Thermal.fidelity (q i) (Thermal.amplified g (q i)) := by
  have hg0 : 0 < g := by linarith
  have hc0 : 0 ≤ Thermal.classicalBase g ^ ((k : ℝ) / 2) :=
    Real.rpow_nonneg (Thermal.classicalBase_pos hg0).le _
  have hc1 : Thermal.classicalBase g ^ ((k : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one (Thermal.classicalBase_pos hg0).le
      (Thermal.classicalBase_le_one hg0.le) (by positivity)
  have hs : Real.sqrt g ^ 2 = g := Real.sq_sqrt hg0.le
  have h := covariant_scaled_thermal_witness_moment_le Γ hΓ hc0 hc1 htrace
    (Real.sqrt g) (by rwa [hs]) hcov hq0 hq1
  simpa only [hs] using h

end Cloning.Hybrid
