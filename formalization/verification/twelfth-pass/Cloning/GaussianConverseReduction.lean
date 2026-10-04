import Cloning.WeylFlatPriorThermal
import Cloning.HeisenbergDualResidual

/-! The actual orbital flat-prior converse reduces to one moment inequality
for genuine covariant CPTP channels. Averaging, compact-limit payoff transfer,
trace loss, and normalization are all proved; only the universal oscillator
moment remains a model-specific premise. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter MeasureTheory Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
open Cloning.Hybrid Cloning.ThermalWitness Cloning.MultimodeCoherentGaussianMixture
namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem covariant_tni_moment_le_of_channel_moment (gain : ℝ)
    (A : TraceClass (Fock d)) (W : Fock d →L[ℂ] Fock d) {C : ℝ} (hC : 0 ≤ C)
    (hmoment : ∀ Φ : QuantumChannel (Fock d) (Fock d),
      (∀ b X, Φ.toLinearMap (displacementTraceMap b X) =
        displacementTraceMap (gain • b) (Φ.toLinearMap X)) →
      (tracePairing (Φ.toLinearMap A) W).re ≤ C)
    (Γ : TraceClass (Fock d) →ₗ[ℂ] TraceClass (Fock d))
    (hCP : IsCompletelyPositive Γ)
    (htrace : ∀ X, 0 ≤ X.1 → (traceCLM (Γ X)).re ≤ (traceCLM X).re)
    (hcov : ∀ b X, Γ (displacementTraceMap b X) =
      displacementTraceMap (gain • b) (Γ X)) :
    (tracePairing (Γ A) W).re ≤ C := by
  rcases covariant_cpTNI_zero_or_scaled_channel Γ hCP.map_nonneg hCP htrace gain hcov with
    hzero | ⟨c, Φ, hc, hc1, heq, hΦ⟩
  · subst Γ
    simpa only [LinearMap.zero_apply, ← tracePairingCLM_apply, map_zero,
      ContinuousLinearMap.zero_apply, Complex.zero_re] using hC
  · have hs : (tracePairing (Γ A) W).re = c * (tracePairing (Φ.toLinearMap A) W).re := by
      rw [heq]
      change (tracePairingCLM ((c : ℂ) • Φ.toLinearMap A) W).re = _
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        tracePairingCLM_apply]
    rw [hs]
    exact (mul_le_mul_of_nonneg_left (hmoment Φ hΦ) hc.le).trans
      (mul_le_of_le_one_left hC hc1)

/-- Every scale-dependent competitor is controlled uniformly, once the
least-noise moment is proved for actual covariant channels. No normal-dual,
trace-normalization, averaging, compactness, or payoff-transfer premise remains. -/
theorem eventually_forall_flatBox_thermal_sq_le_of_channel_moment
    (gain : ℝ) (A : PositiveTraceClass (Fock d)) {q x : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1)
    (hmoment : ∀ Φ : QuantumChannel (Fock d) (Fock d),
      (∀ b X, Φ.toLinearMap (displacementTraceMap b X) =
        displacementTraceMap (gain • b) (Φ.toLinearMap X)) →
      (tracePairing (Φ.toLinearMap A.1) (productWitnessOperator (numberBasis d) q x)).re ≤
        ∏ i, Cloning.Thermal.fidelity (q i) (x i)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ Φ : QuantumChannel (Fock d) (Fock d),
      flatBoxPayoff gain Φ A
        (thermalPositive q (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i))) n ^ 2 ≤
          (∏ i, Cloning.Thermal.fidelity (q i) (x i)) ^ 2 + ε := by
  have hM : 0 ≤ ∏ i, Cloning.Thermal.fidelity (q i) (x i) := Finset.prod_nonneg
    (fun i _ => (Cloning.Thermal.fidelity_pos (hq0 i).le ((hqx i).trans (hx1 i))
      ((hq0 i).trans (hqx i)).le (hx1 i)).le)
  have h := (flatBoxDensity d).eventually_forall_orbitPayoff_sq_le_of_covariant_moment gain A
    (thermalPositive q (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i)))
    (productWitnessOperator (numberBasis d) q x)
    (productWitnessOperator_nonneg _ hq0 hqx hx1)
    (productWitnessOperator_compact _ hq0 hqx hx1) hM
    (fun ε hε => product_thermal_regularized_inverse_moment _ hq0 hqx hx1 hε)
    (covariant_tni_moment_le_of_channel_moment gain A.1 _ hM hmoment)
  simpa only [flatBoxPayoff_eq_integral, pow_two] using h

/-- The root-fidelity flat-prior bound, in the manuscript's convention. -/
theorem eventually_forall_flatBox_thermal_le_of_channel_moment
    (gain : ℝ) (A : PositiveTraceClass (Fock d)) {q x : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1)
    (hmoment : ∀ Φ : QuantumChannel (Fock d) (Fock d),
      (∀ b X, Φ.toLinearMap (displacementTraceMap b X) =
        displacementTraceMap (gain • b) (Φ.toLinearMap X)) →
      (tracePairing (Φ.toLinearMap A.1) (productWitnessOperator (numberBasis d) q x)).re ≤
        ∏ i, Cloning.Thermal.fidelity (q i) (x i)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ Φ : QuantumChannel (Fock d) (Fock d),
      flatBoxPayoff gain Φ A
        (thermalPositive q (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i))) n ≤
          (∏ i, Cloning.Thermal.fidelity (q i) (x i)) + ε := by
  intro ε hε
  have hM : 0 ≤ ∏ i, Cloning.Thermal.fidelity (q i) (x i) := Finset.prod_nonneg
    (fun i _ => (Cloning.Thermal.fidelity_pos (hq0 i).le ((hqx i).trans (hx1 i))
      ((hq0 i).trans (hqx i)).le (hx1 i)).le)
  have h := eventually_forall_flatBox_thermal_sq_le_of_channel_moment gain A hq0 hqx hx1 hmoment
    (ε ^ 2) (sq_pos_of_pos hε)
  filter_upwards [h] with n hn
  intro Φ
  have hb := hn Φ
  nlinarith [sq_nonneg (flatBoxPayoff gain Φ A
    (thermalPositive q (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i))) n -
      (∏ i, Cloning.Thermal.fidelity (q i) (x i)) - ε)]

end Cloning.MultimodeCoherent
