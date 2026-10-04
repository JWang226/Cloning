import Cloning.HybridGaussianRealBox
import Cloning.ThermalParameterContinuity

/-! The genuine hybrid Gaussian converse including vacuum modes. Fixed
Gaussian preparation transports trace-norm continuity to operator-valued L1;
a channel-independent fidelity modulus transports the uniform converse. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter MeasureTheory Cloning.InfiniteTraceClass
open Cloning.MultimodeCoherent Cloning.MultimodeCoherentGaussianMixture Cloning.ThermalWitness
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k s : ℕ}

/-- Fixed Gaussian preparation is continuous on the actual trace-class
space, with its exact normalized L1 norm. -/
theorem continuous_gaussian_prepareL1 (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) :
    Continuous (prepareL1 (H := Fock s) (GaussianAffinity.productDensity a)
      (GaussianAffinity.integrable_productDensity a ha)) := by
  let P := prepareL1 (H := Fock s) (GaussianAffinity.productDensity a)
    (GaussianAffinity.integrable_productDensity a ha)
  have hp (X : TraceClass (Fock s)) : ‖P X‖ ≤ 1 * ‖X‖ := by
    rw [norm_prepareL1 _ _ (GaussianAffinity.productDensity_nonneg a)
      (GaussianAffinity.integral_productDensity a ha), one_mul]
  exact (P.mkContinuous 1 hp).continuous

/-- The centered hybrid reference approaches vacuum parameters in the
actual positive cone of operator-valued L1. -/
theorem gaussianThermalPositive_positiveApprox_tendsto
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    Tendsto (fun n => gaussianThermalPositive a ha (Thermal.positiveApprox q n)
      (fun i => (Thermal.positiveApprox_pos q hq0 n i).le)
      (Thermal.positiveApprox_lt_one q hq1 n)) atTop
      (𝓝 (gaussianThermalPositive a ha q hq0 hq1)) := by
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun n => (gaussianThermalField a ha (Thermal.positiveApprox q n)
    (fun i => (Thermal.positiveApprox_pos q hq0 n i).le)
    (Thermal.positiveApprox_lt_one q hq1 n)).toL1) atTop
    (𝓝 (gaussianThermalField a ha q hq0 hq1).toL1)
  simp_rw [gaussianThermalField_toL1]
  exact (continuous_gaussian_prepareL1 a ha).tendsto _ |>.comp
    (productThermal_tendsto (fun n i => (Thermal.positiveApprox_pos q hq0 n i).le)
      (Thermal.positiveApprox_lt_one q hq1) hq0 hq1 (Thermal.positiveApprox_tendsto q))

/-- Reference perturbation has one modulus for every channel and every
phase-space displacement. The factor two comes from the proved whole-space
operator norm bound for physical hybrid channels. -/
theorem orbitPayoff_self_le_add_reference_error (r : ℝ) (Λ : HybridChannel k s)
    (A C : HybridPositive k s) (ξ : PhaseSpace k s) :
    orbitPayoff r Λ A A ξ ≤ orbitPayoff r Λ C C ξ +
      (Real.sqrt (2 * ‖A.1 - C.1‖) * Real.sqrt ‖A.1‖ +
        Real.sqrt ‖A.1 - C.1‖ * Real.sqrt ‖C.1‖) := by
  rw [orbitPayoff_eq_translated, orbitPayoff_eq_translated]
  let Γ := translatedChannel r Λ ξ
  have h := PositiveL1.rootFidelity_continuity (A.map Γ) A (C.map Γ) C
  rw [PositiveL1.norm_map] at h
  have hd : ‖(A.map Γ).1 - (C.map Γ).1‖ ≤ 2 * ‖A.1 - C.1‖ := by
    change ‖Γ.map A.1 - Γ.map C.1‖ ≤ _
    rw [← map_sub]
    exact Γ.norm_le_two _
  have hb := h.trans (add_le_add
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hd) (Real.sqrt_nonneg _)) le_rfl)
  have hle := (le_abs_self _).trans hb
  dsimp only [Γ] at hle
  linarith

/-- Averaging over any probability prior preserves the same uniform
reference-state modulus. -/
theorem integral_orbitPayoff_self_le_add_reference_error
    (ν : Measure (PhaseSpace k s)) [IsProbabilityMeasure ν]
    (r : ℝ) (Λ : HybridChannel k s) (A C : HybridPositive k s) :
    (∫ ξ, orbitPayoff r Λ A A ξ ∂ν) ≤ (∫ ξ, orbitPayoff r Λ C C ξ ∂ν) +
      (Real.sqrt (2 * ‖A.1 - C.1‖) * Real.sqrt ‖A.1‖ +
        Real.sqrt ‖A.1 - C.1‖ * Real.sqrt ‖C.1‖) := by
  have h := integral_mono (integrable_orbitPayoff ν r Λ A A)
    ((integrable_orbitPayoff ν r Λ C C).add (integrable_const
      (Real.sqrt (2 * ‖A.1 - C.1‖) * Real.sqrt ‖A.1‖ +
        Real.sqrt ‖A.1 - C.1‖ * Real.sqrt ‖C.1‖)))
    (orbitPayoff_self_le_add_reference_error r Λ A C)
  simpa only [Pi.add_apply, integral_add (integrable_orbitPayoff ν r Λ C C)
    (integrable_const _), integral_const, probReal_univ, one_smul] using h

namespace PhaseDensity
variable (p : PhaseDensity k s)

/-- Uniform channel bounds pass to L1 limits of reference states. The
approximation index is chosen before both radius and arbitrary competitor. -/
theorem eventually_forall_orbitPayoff_le_of_reference_tendsto (r : ℝ)
    (A : ℕ → HybridPositive k s) (B : HybridPositive k s)
    (hA : Tendsto A atTop (𝓝 B)) (c : ℕ → ℝ) {C : ℝ}
    (hc : Tendsto c atTop (𝓝 C))
    (hbound : ∀ m, ∀ ε > 0, ∀ᶠ n in atTop, ∀ Λ : HybridChannel k s,
      (∫ ξ, orbitPayoff r Λ (A m) (A m) ξ ∂p.expandingPrior n) ≤ c m + ε) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ Λ : HybridChannel k s,
      (∫ ξ, orbitPayoff r Λ B B ξ ∂p.expandingPrior n) ≤ C + ε := by
  intro ε hε
  have hv : Tendsto (fun m => (A m).1) atTop (𝓝 B.1) :=
    continuous_subtype_val.tendsto _ |>.comp hA
  let E := fun m => Real.sqrt (2 * ‖B.1 - (A m).1‖) * Real.sqrt ‖B.1‖ +
    Real.sqrt ‖B.1 - (A m).1‖ * Real.sqrt ‖(A m).1‖
  have he : Tendsto E atTop (𝓝 0) := by
    have hd := ((tendsto_const_nhds (x := B.1)).sub hv).norm
    convert (((hd.const_mul 2).sqrt).mul tendsto_const_nhds).add
      (hd.sqrt.mul hv.norm.sqrt) using 1
    simp
  have hsum : Tendsto (fun m => c m + E m) atTop (𝓝 C) := by
    simpa using hc.add he
  obtain ⟨m, hm⟩ := (hsum.eventually_lt_const (by linarith : C < C + ε / 2)).exists
  filter_upwards [hbound m (ε / 2) (by linarith)] with n hn
  intro Λ
  have hp := integral_orbitPayoff_self_le_add_reference_error
    (p.expandingPrior n) r Λ B (A m)
  change (∫ ξ, orbitPayoff r Λ B B ξ ∂p.expandingPrior n) ≤
    (∫ ξ, orbitPayoff r Λ (A m) (A m) ξ ∂p.expandingPrior n) + E m at hp
  linarith [hn Λ]

/-- The actual expanding-prior Gaussian converse permits any collection of
exact vacuum modes while remaining uniform over all hybrid competitors. -/
theorem eventually_forall_gaussian_orbitPayoff_le_modeFactor_nonneg
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ Λ : HybridChannel k s,
      (∫ ξ, orbitPayoff (Real.sqrt g) Λ
        (gaussianThermalPositive a ha q hq0 hq1)
        (gaussianThermalPositive a ha q hq0 hq1) ξ ∂p.expandingPrior n) ≤
      Thermal.classicalBase g ^ ((k : ℝ) / 2) *
        (∏ i, Thermal.modeFactor g (q i)) + ε := by
  apply p.eventually_forall_orbitPayoff_le_of_reference_tendsto (Real.sqrt g)
    (fun m => gaussianThermalPositive a ha (Thermal.positiveApprox q m)
      (fun i => (Thermal.positiveApprox_pos q hq0 m i).le)
      (Thermal.positiveApprox_lt_one q hq1 m))
    (gaussianThermalPositive a ha q hq0 hq1)
    (gaussianThermalPositive_positiveApprox_tendsto a ha q hq0 hq1)
    (fun m => Thermal.classicalBase g ^ ((k : ℝ) / 2) *
      ∏ i, Thermal.modeFactor g (Thermal.positiveApprox q m i))
    ((modeFactor_positiveApprox_tendsto g (zero_lt_one.trans hg) q hq0).const_mul _)
  intro m
  exact p.eventually_forall_gaussian_orbitPayoff_le_modeFactor a ha g hg _
    (Thermal.positiveApprox_pos q hq0 m) (Thermal.positiveApprox_lt_one q hq1 m)

end PhaseDensity

/-- Nonnegative thermal spectra in every sufficiently large real physical
box, with one threshold for all actual hybrid channels. -/
theorem eventually_forall_realFlatBox_gaussian_le_modeFactor_nonneg
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    ∀ ε > 0, ∀ᶠ L : ℝ in atTop, ∀ Λ : HybridChannel k s,
      realFlatBoxPayoff (Real.sqrt g) Λ
        (gaussianThermalPositive a ha q hq0 hq1)
        (gaussianThermalPositive a ha q hq0 hq1) L ≤
      Thermal.classicalBase g ^ ((k : ℝ) / 2) * (∏ i, Thermal.modeFactor g (q i)) + ε := by
  apply eventually_forall_realFlatBox_le_of_integer
  simpa only [flatBoxPayoff_eq_integral] using
    (flatBoxDensity k s).eventually_forall_gaussian_orbitPayoff_le_modeFactor_nonneg
      a ha g hg q hq0 hq1

/-- The full `limsup sup_channel` converse on literal normalized real boxes
includes the vacuum boundary of the thermal parameter space. -/
theorem limsup_realFlatBox_gaussian_le_modeFactor_nonneg
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    Filter.limsup (realFlatBoxOptimalPayoff (Real.sqrt g)
      (gaussianThermalPositive a ha q hq0 hq1)
      (gaussianThermalPositive a ha q hq0 hq1)) atTop ≤
      Thermal.classicalBase g ^ ((k : ℝ) / 2) * (∏ i, Thermal.modeFactor g (q i)) :=
  limsup_realFlatBoxOptimalPayoff_le _ _ _
    (eventually_forall_realFlatBox_gaussian_le_modeFactor_nonneg a ha g hg q hq0 hq1)

end Cloning.Hybrid
