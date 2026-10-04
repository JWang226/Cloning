import Cloning.UniversalLeastNoiseThermalTest
import Cloning.ThermalWitnessGeometric
import Cloning.GaussianConverseReduction

/-! The universal orbital thermal Gaussian converse for actual channels.
The least-noise fidelity-witness moment follows directly from complete positivity,
and the growing-box bound holds uniformly over all competitors at each scale.
No quantum Bochner reconstruction, seeded-channel classification, or assumed
moment inequality occurs in the hypotheses. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter MeasureTheory Cloning.InfiniteTraceClass
open Cloning.ThermalWitness Cloning.MultimodeCoherentGaussianMixture
namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ}

/-- The exact thermal fidelity witness satisfies the least-noise moment
bound for every covariant CPTP channel, including non-Gaussian joint noise. -/
theorem covariant_thermal_witness_moment_le
    (Φ : QuantumChannel (Fock d) (Fock d)) (r : ℝ)
    (hcov : ∀ a T, Φ.toLinearMap (displacementTraceMap a T) =
      displacementTraceMap (r • a) (Φ.toLinearMap T))
    (hr : 1 < r ^ 2) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    (tracePairing (Φ.toLinearMap (vectorMixture (numberBasis d) (productGeometric q)))
      (productWitnessOperator (numberBasis d) q (fun i => Thermal.amplified (r ^ 2) (q i)))).re ≤
      ∏ i, Thermal.fidelity (q i) (Thermal.amplified (r ^ 2) (q i)) := by
  let x : Fin d → ℝ := fun i => Thermal.amplified (r ^ 2) (q i)
  have hqx : ∀ i, q i < x i := fun i => Thermal.lt_amplified hr (hq1 i)
  have hx1 : ∀ i, x i < 1 := fun i => Thermal.amplified_lt_one (by linarith) (hq1 i)
  let y := witnessGeometricParameter q x
  have hy0 : ∀ i, 0 < y i := witnessGeometricParameter_pos hq0 hqx
  have hy1 : ∀ i, y i < 1 := witnessGeometricParameter_lt_one hq0 hqx
  have hbound := covariant_thermal_test_moment_le Φ r hcov hr hq0 hq1 hy0 hy1
  change (tracePairing (Φ.toLinearMap (vectorMixture (numberBasis d) (productGeometric q)))
    (productWitnessOperator (numberBasis d) q x)).re ≤ ∏ i, Thermal.fidelity (q i) (x i)
  rw [← product_thermal_witness_moment (numberBasis d) hq0 hqx hx1,
    productWitnessOperator_eq_scale_geometric (numberBasis d) hq0 hqx hx1]
  have hs (T : TraceClass (Fock d)) :
      (tracePairing T ((witnessGeometricScale q x : ℂ) •
        (vectorMixture (numberBasis d) (productGeometric y)).1)).re =
      witnessGeometricScale q x *
        (tracePairing T (vectorMixture (numberBasis d) (productGeometric y)).1).re := by
    change ((tracePairingCLM T) ((witnessGeometricScale q x : ℂ) • _)).re = _
    rw [map_smul]
    simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, tracePairingCLM_apply]
  rw [hs, hs]
  exact mul_le_mul_of_nonneg_left hbound (witnessGeometricScale_pos hq0 hqx hx1).le

/-- Uniform expanding-box converse. The channel may depend on the radius;
the eventual radius is chosen before the arbitrary channel. -/
theorem eventually_forall_flatBox_thermal_le
    (r : ℝ) (hr : 1 < r ^ 2) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ Φ : QuantumChannel (Fock d) (Fock d),
      flatBoxPayoff r Φ (thermalPositive q (fun i => (hq0 i).le) hq1)
        (thermalPositive q (fun i => (hq0 i).le) hq1) n ≤
          (∏ i, Thermal.fidelity (q i) (Thermal.amplified (r ^ 2) (q i))) + ε := by
  exact eventually_forall_flatBox_thermal_le_of_channel_moment r
    (thermalPositive q (fun i => (hq0 i).le) hq1) hq0
    (fun i => Thermal.lt_amplified hr (hq1 i))
    (fun i => Thermal.amplified_lt_one (by linarith) (hq1 i))
    (fun Φ hΦ => covariant_thermal_witness_moment_le Φ r hΦ hr hq0 hq1)

/-- Universal orbital Gaussian converse in the order `limsup sup_channel`.
The payoff is the literal normalized Lebesgue integral on expanding boxes. -/
theorem limsup_flatBox_thermal_le
    (r : ℝ) (hr : 1 < r ^ 2) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    Filter.limsup (flatBoxOptimalPayoff r
      (thermalPositive q (fun i => (hq0 i).le) hq1)
      (thermalPositive q (fun i => (hq0 i).le) hq1)) atTop ≤
        ∏ i, Thermal.fidelity (q i) (Thermal.amplified (r ^ 2) (q i)) :=
  limsup_flatBoxOptimalPayoff_le r _ _ (eventually_forall_flatBox_thermal_le r hr hq0 hq1)

/-- The manuscript's orbital factor with physical amplitude gain `sqrt γ`.
Every mode parameter lies strictly between zero and one; zero modes are allowed. -/
theorem limsup_flatBox_thermal_le_modeFactor
    (γ : ℝ) (hγ : 1 < γ) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    Filter.limsup (flatBoxOptimalPayoff (Real.sqrt γ)
      (thermalPositive q (fun i => (hq0 i).le) hq1)
      (thermalPositive q (fun i => (hq0 i).le) hq1)) atTop ≤
        ∏ i, Thermal.modeFactor γ (q i) := by
  have hs : Real.sqrt γ ^ 2 = γ := Real.sq_sqrt (by linarith)
  have h := limsup_flatBox_thermal_le (Real.sqrt γ) (by rwa [hs]) hq0 hq1
  simp_rw [hs, Thermal.fidelity_amplified_eq_modeFactor hγ (hq0 _).le (hq1 _)] at h
  exact h

end Cloning.MultimodeCoherent
