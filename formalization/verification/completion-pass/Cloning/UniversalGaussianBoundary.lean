import Cloning.UniversalGaussianRealBox
import Cloning.ThermalParameterContinuity

/-! The orbital Gaussian converse at vacuum thermal parameters. The proof
passes through actual trace-norm convergence, with a root-fidelity modulus
uniform over all channels, translations, and averaging radii. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter MeasureTheory Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
open Cloning.Hybrid
namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

/-- Reference-state perturbation is uniform over the actual competing channel
and over the displacement, including arbitrarily large displacements. -/
theorem orbitPayoff_self_le_add_reference_error (r : ℝ)
    (Φ : QuantumChannel (Fock d) (Fock d))
    (A C : PositiveTraceClass (Fock d)) (z : Fin d → ℂ) :
    orbitPayoff r Φ A A z ≤ orbitPayoff r Φ C C z +
      Real.sqrt ‖A.1 - C.1‖ * (Real.sqrt ‖A.1‖ + Real.sqrt ‖C.1‖) := by
  rw [orbitPayoff_eq_translated, orbitPayoff_eq_translated]
  let Ψ := (translatedChannel r Φ z).toPositiveTracePreservingMap
  have h := PositiveTraceClass.rootFidelity_continuity
    (PositiveTraceClass.map Ψ A) A (PositiveTraceClass.map Ψ C) C
  have hc := Ψ.norm_map_sub_le A.1 C.1 A.2 C.2
  have hm : ‖(PositiveTraceClass.map Ψ C).1‖ = ‖C.1‖ :=
    Ψ.norm_map_of_nonneg C.1 C.2
  rw [hm] at h
  have hb : |(PositiveTraceClass.map Ψ A).rootFidelity A -
      (PositiveTraceClass.map Ψ C).rootFidelity C| ≤
      Real.sqrt ‖A.1 - C.1‖ * (Real.sqrt ‖A.1‖ + Real.sqrt ‖C.1‖) := by
    apply h.trans
    rw [mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hc)
      (Real.sqrt_nonneg _)) le_rfl
  have hle := (le_abs_self _).trans hb
  dsimp only [Ψ] at hle
  linarith

/-- The same perturbation cost for every probability prior. -/
theorem integral_orbitPayoff_self_le_add_reference_error
    (μ : Measure (Fin d → ℂ)) [IsProbabilityMeasure μ] (r : ℝ)
    (Φ : QuantumChannel (Fock d) (Fock d)) (A C : PositiveTraceClass (Fock d)) :
    (∫ z, orbitPayoff r Φ A A z ∂μ) ≤ (∫ z, orbitPayoff r Φ C C z ∂μ) +
      Real.sqrt ‖A.1 - C.1‖ * (Real.sqrt ‖A.1‖ + Real.sqrt ‖C.1‖) := by
  have h := integral_mono (integrable_orbitPayoff μ r Φ A A)
    ((integrable_orbitPayoff μ r Φ C C).add (integrable_const
      (Real.sqrt ‖A.1-C.1‖ * (Real.sqrt ‖A.1‖ + Real.sqrt ‖C.1‖))))
    (orbitPayoff_self_le_add_reference_error r Φ A C)
  simpa only [Pi.add_apply, integral_add (integrable_orbitPayoff μ r Φ C C) (integrable_const _),
    integral_const, probReal_univ, one_smul] using h

/-- Uniform expanding-box estimates are closed under trace-norm convergence
of the physical reference state. The approximation is fixed before the
radius, and the radius is fixed before the arbitrary channel. -/
theorem eventually_forall_flatBox_le_of_reference_tendsto (r : ℝ)
    (A : ℕ → PositiveTraceClass (Fock d)) (B : PositiveTraceClass (Fock d))
    (hA : Tendsto A atTop (𝓝 B)) (c : ℕ → ℝ) {C : ℝ}
    (hc : Tendsto c atTop (𝓝 C))
    (hbound : ∀ m, ∀ ε > 0, ∀ᶠ n in atTop, ∀ Φ : QuantumChannel (Fock d) (Fock d),
      flatBoxPayoff r Φ (A m) (A m) n ≤ c m + ε) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ Φ : QuantumChannel (Fock d) (Fock d),
      flatBoxPayoff r Φ B B n ≤ C + ε := by
  intro ε hε
  have hv : Tendsto (fun m => (A m).1) atTop (𝓝 B.1) :=
    continuous_subtype_val.tendsto _ |>.comp hA
  have he : Tendsto (fun m => Real.sqrt ‖B.1 - (A m).1‖ *
      (Real.sqrt ‖B.1‖ + Real.sqrt ‖(A m).1‖)) atTop (𝓝 0) := by
    convert ((tendsto_const_nhds.sub hv).norm.sqrt).mul
      (tendsto_const_nhds.add hv.norm.sqrt) using 1
    simp
  have hsum : Tendsto (fun m => c m + Real.sqrt ‖B.1-(A m).1‖ *
      (Real.sqrt ‖B.1‖ + Real.sqrt ‖(A m).1‖)) atTop (𝓝 C) := by
    simpa using hc.add he
  have hnear : ∀ᶠ m in atTop, c m + Real.sqrt ‖B.1-(A m).1‖ *
      (Real.sqrt ‖B.1‖ + Real.sqrt ‖(A m).1‖) < C + ε/2 :=
    hsum.eventually_lt_const (by linarith : C < C + ε/2)
  obtain ⟨m, hm⟩ := hnear.exists
  filter_upwards [hbound m (ε/2) (by linarith)] with n hn
  intro Φ
  have hp := integral_orbitPayoff_self_le_add_reference_error
    ((flatBoxDensity d).expandingPrior n) r Φ B (A m)
  rw [← flatBoxPayoff_eq_integral, ← flatBoxPayoff_eq_integral] at hp
  linarith [hn Φ]

/-- The universal integer-box converse, allowing any exact vacuum modes. -/
theorem eventually_forall_flatBox_thermal_le_modeFactor_nonneg
    (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ Φ : QuantumChannel (Fock d) (Fock d),
      flatBoxPayoff (Real.sqrt g) Φ (thermalPositive q hq0 hq1)
        (thermalPositive q hq0 hq1) n ≤ (∏ i, Thermal.modeFactor g (q i)) + ε := by
  apply eventually_forall_flatBox_le_of_reference_tendsto (Real.sqrt g)
    (fun m => thermalPositive (Thermal.positiveApprox q m)
      (fun i => (Thermal.positiveApprox_pos q hq0 m i).le)
      (Thermal.positiveApprox_lt_one q hq1 m))
    (thermalPositive q hq0 hq1) (thermalPositive_positiveApprox_tendsto q hq0 hq1)
    (fun m => ∏ i, Thermal.modeFactor g (Thermal.positiveApprox q m i))
    (modeFactor_positiveApprox_tendsto g (zero_lt_one.trans hg) q hq0)
  intro m
  have hs : Real.sqrt g ^ 2 = g := Real.sq_sqrt (zero_lt_one.trans hg).le
  have h := eventually_forall_flatBox_thermal_le (Real.sqrt g) (by rwa [hs])
    (Thermal.positiveApprox_pos q hq0 m) (Thermal.positiveApprox_lt_one q hq1 m)
  simpa only [hs, Thermal.fidelity_amplified_eq_modeFactor hg
    (Thermal.positiveApprox_pos q hq0 m _).le (Thermal.positiveApprox_lt_one q hq1 m _)] using h

/-- Uniform upper bound for all sufficiently large real radii and every
actual channel, including nonnegative thermal parameters. -/
theorem eventually_forall_realFlatBox_thermal_le_modeFactor_nonneg
    (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    ∀ ε > 0, ∀ᶠ L : ℝ in atTop, ∀ Φ : QuantumChannel (Fock d) (Fock d),
      realFlatBoxPayoff (Real.sqrt g) Φ (thermalPositive q hq0 hq1)
        (thermalPositive q hq0 hq1) L ≤ (∏ i, Thermal.modeFactor g (q i)) + ε :=
  eventually_forall_realFlatBox_le_of_integer (Real.sqrt g) _ _
    (eventually_forall_flatBox_thermal_le_modeFactor_nonneg g hg hq0 hq1)

theorem limsup_flatBox_thermal_le_modeFactor_nonneg
    (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    Filter.limsup (flatBoxOptimalPayoff (Real.sqrt g)
      (thermalPositive q hq0 hq1) (thermalPositive q hq0 hq1)) atTop ≤
        ∏ i, Thermal.modeFactor g (q i) :=
  limsup_flatBoxOptimalPayoff_le (Real.sqrt g) _ _
    (eventually_forall_flatBox_thermal_le_modeFactor_nonneg g hg hq0 hq1)

/-- The channel supremum remains inside the real-radius limit at the vacuum
boundary; no channel choice is assumed continuous in the thermal parameters. -/
theorem limsup_realFlatBox_thermal_le_modeFactor_nonneg
    (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    Filter.limsup (realFlatBoxOptimalPayoff (Real.sqrt g)
      (thermalPositive q hq0 hq1) (thermalPositive q hq0 hq1)) atTop ≤
        ∏ i, Thermal.modeFactor g (q i) :=
  limsup_realFlatBoxOptimalPayoff_le (Real.sqrt g) _ _
    (eventually_forall_realFlatBox_thermal_le_modeFactor_nonneg g hg hq0 hq1)

end Cloning.MultimodeCoherent
