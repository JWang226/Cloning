import Cloning.AmplifierWeylThermal
import Cloning.UniversalGaussianRealBox
import Cloning.InfiniteDiagonalFidelity

/-!
# Physical Gaussian attainment of the orbital fidelity bound

The constructed quantum-limited amplifier sends every displaced product
thermal state to the corresponding displaced amplified thermal state.
Its root fidelity with the target orbit is the same exact mode-factor product
at every displacement. Consequently it attains every probability average,
and the optimal expanding real-box payoff converges to that product.
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

theorem thermalPositive_rootFidelity {q x : Fin d → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1) :
    (thermalPositive q hq0 hq1).rootFidelity (thermalPositive x hx0 hx1) =
      ∏ i, Thermal.fidelity (q i) (x i) := by
  change stateFidelity (productGeometricState (numberBasis d) q hq0 hq1)
    (productGeometricState (numberBasis d) x hx0 hx1) = _
  exact stateFidelity_productGeometric (numberBasis d) q x hq0 hq1 hx0 hx1

theorem orbitPayoff_eq_rootFidelity_of_covariant
    (gain : ℝ) (Φ : QuantumChannel (Fock d) (Fock d))
    (hcov : ∀ a A, Φ.toLinearMap (displacementTraceMap a A) =
      displacementTraceMap (gain • a) (Φ.toLinearMap A))
    (A B : PositiveTraceClass (Fock d)) (a : Fin d → ℂ) :
    orbitPayoff gain Φ A B a =
      (PositiveTraceClass.map Φ.toPositiveTracePreservingMap A).rootFidelity B := by
  have he : PositiveTraceClass.map Φ.toPositiveTracePreservingMap (displacedPositive a A) =
      displacedPositive (gain • a) (PositiveTraceClass.map Φ.toPositiveTracePreservingMap A) := by
    apply Subtype.ext
    simpa only [PositiveTraceClass.map, displacedPositive_val] using hcov a A.1
  rw [orbitPayoff, he, displacedPositive_rootFidelity]

/-- The physical amplifier achieves the exact orbital root fidelity at
every phase-space displacement, with no averaging or limit. -/
theorem gainChannel_orbitPayoff (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (a : Fin d → ℂ) :
    orbitPayoff (Real.sqrt g) (gainChannel g hg)
      (thermalPositive q (fun i => (hq0 i).le) hq1)
      (thermalPositive q (fun i => (hq0 i).le) hq1) a =
      ∏ i, Thermal.modeFactor g (q i) := by
  let x : Fin d → ℝ := fun i => Thermal.amplified g (q i)
  have hx0 (i : Fin d) : 0 ≤ x i :=
    ((hq0 i).trans (Thermal.lt_amplified hg (hq1 i))).le
  have hx1 (i : Fin d) : x i < 1 := Thermal.amplified_lt_one (by linarith) (hq1 i)
  have hmap : PositiveTraceClass.map (gainChannel g hg).toPositiveTracePreservingMap
      (thermalPositive q (fun i => (hq0 i).le) hq1) = thermalPositive x hx0 hx1 := by
    apply Subtype.ext
    exact gainChannel_productThermal g hg hq0 hq1
  rw [orbitPayoff_eq_rootFidelity_of_covariant (Real.sqrt g) (gainChannel g hg)
    (gainChannel_covariant g hg), hmap, PositiveTraceClass.rootFidelity_comm,
    thermalPositive_rootFidelity]
  apply Finset.prod_congr rfl
  intro i _
  exact Thermal.fidelity_amplified_eq_modeFactor hg (hq0 i).le (hq1 i)

/-- Any probability prior, not only a flat box, has exactly this attained
average root fidelity. -/
theorem gainChannel_integral_orbitPayoff (μ : Measure (Fin d → ℂ)) [IsProbabilityMeasure μ]
    (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    (∫ a, orbitPayoff (Real.sqrt g) (gainChannel g hg)
      (thermalPositive q (fun i => (hq0 i).le) hq1)
      (thermalPositive q (fun i => (hq0 i).le) hq1) a ∂μ) =
      ∏ i, Thermal.modeFactor g (q i) := by
  simp_rw [gainChannel_orbitPayoff g hg hq0 hq1]
  simp

theorem gainChannel_flatBoxPayoff (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (n : ℕ) :
    flatBoxPayoff (Real.sqrt g) (gainChannel g hg)
      (thermalPositive q (fun i => (hq0 i).le) hq1)
      (thermalPositive q (fun i => (hq0 i).le) hq1) n =
      ∏ i, Thermal.modeFactor g (q i) := by
  rw [flatBoxPayoff_eq_integral]
  exact gainChannel_integral_orbitPayoff _ g hg hq0 hq1

theorem gainChannel_realFlatBoxPayoff (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (L : ℝ) :
    realFlatBoxPayoff (Real.sqrt g) (gainChannel g hg)
      (thermalPositive q (fun i => (hq0 i).le) hq1)
      (thermalPositive q (fun i => (hq0 i).le) hq1) L =
      ∏ i, Thermal.modeFactor g (q i) := by
  unfold realFlatBoxPayoff
  simp_rw [gainChannel_orbitPayoff g hg hq0 hq1]
  simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
  change (volume.real (phaseSpaceUnitBox d))⁻¹ *
    (volume.real (phaseSpaceUnitBox d) * _) = _
  rw [← mul_assoc, inv_mul_cancel₀ (phaseSpaceUnitBox_volume_real_pos d).ne', one_mul]

/-- Attainment for the literal normalized Lebesgue integral on each positive
real-radius box. -/
theorem gainChannel_normalized_box (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) {L : ℝ} (hL : 0 < L) :
    (volume.real (phaseSpaceBox d L))⁻¹ *
      (∫ a in phaseSpaceBox d L, orbitPayoff (Real.sqrt g) (gainChannel g hg)
        (thermalPositive q (fun i => (hq0 i).le) hq1)
        (thermalPositive q (fun i => (hq0 i).le) hq1) a) =
      ∏ i, Thermal.modeFactor g (q i) := by
  rw [← realFlatBoxPayoff_eq_normalized_box _ _ _ _ hL]
  exact gainChannel_realFlatBoxPayoff g hg hq0 hq1 L

/-- A single physical amplifier supplies a lower bound for every competing
channel supremum, independently of the box radius. -/
theorem modeFactor_le_realFlatBoxOptimalPayoff (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (L : ℝ) :
    (∏ i, Thermal.modeFactor g (q i)) ≤ realFlatBoxOptimalPayoff (Real.sqrt g)
      (thermalPositive q (fun i => (hq0 i).le) hq1)
      (thermalPositive q (fun i => (hq0 i).le) hq1) L := by
  let A := thermalPositive q (fun i => (hq0 i).le) hq1
  have hb : BddAbove (Set.range (fun Φ : QuantumChannel (Fock d) (Fock d) =>
      realFlatBoxPayoff (Real.sqrt g) Φ A A L)) := by
    refine ⟨Real.sqrt ‖A.1‖ * Real.sqrt ‖A.1‖, ?_⟩
    rintro _ ⟨Φ, rfl⟩
    exact realFlatBoxPayoff_le_sqrt _ Φ A A L
  rw [← gainChannel_realFlatBoxPayoff g hg hq0 hq1 L]
  exact le_csSup hb (Set.mem_range_self (gainChannel g hg))

/-- The optimal average root fidelity has an actual limit over arbitrary
real expanding boxes, with the channel supremum taken before the limit. -/
theorem realFlatBoxOptimalPayoff_tendsto_modeFactor
    (g : ℝ) (hg : 1 < g) {q : Fin d → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    Tendsto (realFlatBoxOptimalPayoff (Real.sqrt g)
      (thermalPositive q (fun i => (hq0 i).le) hq1)
      (thermalPositive q (fun i => (hq0 i).le) hq1)) atTop
      (𝓝 (∏ i, Thermal.modeFactor g (q i))) := by
  let A := thermalPositive q (fun i => (hq0 i).le) hq1
  let F : ℝ := ∏ i, Thermal.modeFactor g (q i)
  have hs : Real.sqrt g ^ 2 = g := Real.sq_sqrt (by linarith)
  have hupper := eventually_forall_realFlatBox_thermal_le (Real.sqrt g) (by rwa [hs]) hq0 hq1
  simp_rw [hs, Thermal.fidelity_amplified_eq_modeFactor hg (hq0 _).le (hq1 _)] at hupper
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
    exact Eventually.of_forall fun L => hc.trans_le (modeFactor_le_realFlatBoxOptimalPayoff g hg hq0 hq1 L)
  · intro c hc
    filter_upwards [hopt ((c - F) / 2) (by change F < c at hc; linarith)] with L hL
    change F < c at hc
    change realFlatBoxOptimalPayoff (Real.sqrt g) A A L < c
    linarith

end Cloning.MultimodeCoherent
