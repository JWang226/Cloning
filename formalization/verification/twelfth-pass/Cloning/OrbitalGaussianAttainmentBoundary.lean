import Cloning.ThermalParameterContinuity
import Cloning.OrbitalGaussianAttainment
import Cloning.UniversalGaussianBoundary

/-!
# Physical Gaussian orbital attainment including vacuum modes

The same spectrum-independent amplifier attains the orbital factor when any
thermal parameters are exactly zero. The actual thermal output identity is
obtained by trace-norm continuity, and the fidelity identities remain literal
positive-operator and Lebesgue-integral equalities.
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter MeasureTheory Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
open Cloning.Hybrid Cloning.ThermalWitness Cloning.MultimodeCoherentGaussianMixture
open Cloning.InfiniteDiagonalFidelity Cloning.MultimodeAmplifier
namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

theorem gainChannel_map_thermalPositive_nonneg (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    PositiveTraceClass.map (gainChannel g hg).toPositiveTracePreservingMap
      (thermalPositive q hq0 hq1) =
      thermalPositive (fun i => Thermal.amplified g (q i))
        (fun i => (hq0 i).trans (Thermal.lt_amplified hg (hq1 i)).le)
        (fun i => Thermal.amplified_lt_one (zero_lt_one.trans hg) (hq1 i)) := by
  apply Subtype.ext
  exact gainChannel_productThermal_nonneg g hg hq0 hq1

/-- Pointwise physical attainment, including any combination of exact vacuum
and mixed thermal modes. -/
theorem gainChannel_orbitPayoff_nonneg (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (a : Fin d → ℂ) :
    orbitPayoff (Real.sqrt g) (gainChannel g hg)
      (thermalPositive q hq0 hq1) (thermalPositive q hq0 hq1) a =
      ∏ i, Thermal.modeFactor g (q i) := by
  rw [orbitPayoff_eq_rootFidelity_of_covariant (Real.sqrt g) (gainChannel g hg)
    (gainChannel_covariant g hg), gainChannel_map_thermalPositive_nonneg,
    PositiveTraceClass.rootFidelity_comm, thermalPositive_rootFidelity]
  apply Finset.prod_congr rfl
  intro i _
  exact Thermal.fidelity_amplified_eq_modeFactor hg (hq0 i) (hq1 i)

theorem gainChannel_integral_orbitPayoff_nonneg
    (μ : Measure (Fin d → ℂ)) [IsProbabilityMeasure μ]
    (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    (∫ a, orbitPayoff (Real.sqrt g) (gainChannel g hg)
      (thermalPositive q hq0 hq1) (thermalPositive q hq0 hq1) a ∂μ) =
      ∏ i, Thermal.modeFactor g (q i) := by
  simp_rw [gainChannel_orbitPayoff_nonneg g hg hq0 hq1]
  simp

theorem gainChannel_flatBoxPayoff_nonneg (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (n : ℕ) :
    flatBoxPayoff (Real.sqrt g) (gainChannel g hg)
      (thermalPositive q hq0 hq1) (thermalPositive q hq0 hq1) n =
      ∏ i, Thermal.modeFactor g (q i) := by
  rw [flatBoxPayoff_eq_integral]
  exact gainChannel_integral_orbitPayoff_nonneg _ g hg hq0 hq1

theorem gainChannel_realFlatBoxPayoff_nonneg (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (L : ℝ) :
    realFlatBoxPayoff (Real.sqrt g) (gainChannel g hg)
      (thermalPositive q hq0 hq1) (thermalPositive q hq0 hq1) L =
      ∏ i, Thermal.modeFactor g (q i) := by
  unfold realFlatBoxPayoff
  simp_rw [gainChannel_orbitPayoff_nonneg g hg hq0 hq1]
  simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
  change (volume.real (phaseSpaceUnitBox d))⁻¹ *
    (volume.real (phaseSpaceUnitBox d) * _) = _
  rw [← mul_assoc, inv_mul_cancel₀ (phaseSpaceUnitBox_volume_real_pos d).ne', one_mul]

theorem gainChannel_normalized_box_nonneg (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) {L : ℝ} (hL : 0 < L) :
    (volume.real (phaseSpaceBox d L))⁻¹ *
      (∫ a in phaseSpaceBox d L, orbitPayoff (Real.sqrt g) (gainChannel g hg)
        (thermalPositive q hq0 hq1) (thermalPositive q hq0 hq1) a) =
      ∏ i, Thermal.modeFactor g (q i) := by
  rw [← realFlatBoxPayoff_eq_normalized_box _ _ _ _ hL]
  exact gainChannel_realFlatBoxPayoff_nonneg g hg hq0 hq1 L

theorem modeFactor_le_realFlatBoxOptimalPayoff_nonneg
    (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (L : ℝ) :
    (∏ i, Thermal.modeFactor g (q i)) ≤ realFlatBoxOptimalPayoff (Real.sqrt g)
      (thermalPositive q hq0 hq1) (thermalPositive q hq0 hq1) L := by
  let A := thermalPositive q hq0 hq1
  have hb : BddAbove (Set.range (fun Φ : QuantumChannel (Fock d) (Fock d) =>
      realFlatBoxPayoff (Real.sqrt g) Φ A A L)) := by
    refine ⟨Real.sqrt ‖A.1‖ * Real.sqrt ‖A.1‖, ?_⟩
    rintro _ ⟨Φ, rfl⟩
    exact realFlatBoxPayoff_le_sqrt _ Φ A A L
  rw [← gainChannel_realFlatBoxPayoff_nonneg g hg hq0 hq1 L]
  exact le_csSup hb (Set.mem_range_self (gainChannel g hg))

/-- The optimal average root fidelity converges to the attained orbital
factor for every nonnegative thermal spectrum, including exact vacuum modes.
The supremum ranges over all actual channels at each real radius. -/
theorem realFlatBoxOptimalPayoff_tendsto_modeFactor_nonneg
    (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    Tendsto (realFlatBoxOptimalPayoff (Real.sqrt g)
      (thermalPositive q hq0 hq1) (thermalPositive q hq0 hq1)) atTop
      (𝓝 (∏ i, Thermal.modeFactor g (q i))) := by
  let A := thermalPositive q hq0 hq1
  let F : ℝ := ∏ i, Thermal.modeFactor g (q i)
  have hupper := eventually_forall_realFlatBox_thermal_le_modeFactor_nonneg g hg hq0 hq1
  have hopt : ∀ ε > 0, ∀ᶠ L : ℝ in atTop,
      realFlatBoxOptimalPayoff (Real.sqrt g) A A L ≤ F + ε := by
    intro ε hε
    filter_upwards [hupper ε hε] with L hL
    apply csSup_le ⟨_, Set.mem_range_self (gainChannel g hg)⟩
    rintro _ ⟨Φ, rfl⟩
    exact hL Φ
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall fun L =>
      hc.trans_le (modeFactor_le_realFlatBoxOptimalPayoff_nonneg g hg hq0 hq1 L)
  · intro c hc
    filter_upwards [hopt ((c - F) / 2) (by change F < c at hc; linarith)] with L hL
    change F < c at hc
    change realFlatBoxOptimalPayoff (Real.sqrt g) A A L < c
    linarith

end Cloning.MultimodeCoherent
