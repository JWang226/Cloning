import Cloning.HybridGaussianAttainment
import Cloning.HybridGaussianRealBox

/-! The exact hybrid Gaussian optimum for arbitrary real expanding boxes,
with channel optimization taken before the limit. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k s : ℕ}

theorem gaussianAmplifierChannel_realFlatBoxPayoff
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (L : ℝ) :
    realFlatBoxPayoff (Real.sqrt g) (gaussianAmplifierChannel g hg)
      (gaussianThermalPositive a ha q hq0 hq1)
      (gaussianThermalPositive a ha q hq0 hq1) L =
      Thermal.classicalBase g ^ ((k : ℝ) / 2) * ∏ i, Thermal.modeFactor g (q i) :=
  realFlatBoxPayoff_eq_of_orbitPayoff_const _ _ _ _
    (gaussianAmplifierChannel_orbitPayoff a ha g hg q hq0 hq1) L

/-- Every positive real-radius box has the exact attained normalized value. -/
theorem gaussianAmplifierChannel_normalized_box
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) {L : ℝ} (hL : 0 < L) :
    (volume.real (phaseSpaceBox k s L))⁻¹ *
      (∫ ξ in phaseSpaceBox k s L, orbitPayoff (Real.sqrt g) (gaussianAmplifierChannel g hg)
        (gaussianThermalPositive a ha q hq0 hq1)
        (gaussianThermalPositive a ha q hq0 hq1) ξ) =
      Thermal.classicalBase g ^ ((k : ℝ) / 2) * ∏ i, Thermal.modeFactor g (q i) := by
  rw [← realFlatBoxPayoff_eq_normalized_box _ _ _ _ hL]
  exact gaussianAmplifierChannel_realFlatBoxPayoff a ha g hg q hq0 hq1 L

theorem modeFactor_le_realFlatBoxOptimalPayoff
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (L : ℝ) :
    Thermal.classicalBase g ^ ((k : ℝ) / 2) * (∏ i, Thermal.modeFactor g (q i)) ≤
      realFlatBoxOptimalPayoff (Real.sqrt g)
        (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1)
        (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1) L := by
  rw [← gaussianAmplifierChannel_realFlatBoxPayoff a ha g hg q (fun i => (hq0 i).le) hq1 L]
  exact realFlatBoxPayoff_le_optimal _ _ _ _ L

/-- The actual optimal Gaussian hybrid root fidelity converges to the full
classical--orbital product factor along all real box radii. -/
theorem realFlatBoxOptimalPayoff_tendsto_modeFactor
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    Tendsto (realFlatBoxOptimalPayoff (Real.sqrt g)
      (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1)
      (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1)) atTop
      (𝓝 (Thermal.classicalBase g ^ ((k : ℝ) / 2) * ∏ i, Thermal.modeFactor g (q i))) := by
  let A := gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1
  let F : ℝ := Thermal.classicalBase g ^ ((k : ℝ) / 2) * ∏ i, Thermal.modeFactor g (q i)
  have hupper := eventually_forall_realFlatBox_gaussian_le_modeFactor a ha g hg q hq0 hq1
  have hopt : ∀ ε > 0, ∀ᶠ L : ℝ in atTop,
      realFlatBoxOptimalPayoff (Real.sqrt g) A A L ≤ F + ε := by
    intro ε hε
    filter_upwards [hupper ε hε] with L hL
    apply csSup_le ⟨_, Set.mem_range_self (gaussianAmplifierChannel g hg)⟩
    rintro _ ⟨Λ, rfl⟩
    exact hL Λ
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall fun L => hc.trans_le
      (modeFactor_le_realFlatBoxOptimalPayoff a ha g hg q hq0 hq1 L)
  · intro c hc
    filter_upwards [hopt ((c - F) / 2) (by change F < c at hc; linarith)] with L hL
    change F < c at hc
    change realFlatBoxOptimalPayoff (Real.sqrt g) A A L < c
    linarith

end Cloning.Hybrid
