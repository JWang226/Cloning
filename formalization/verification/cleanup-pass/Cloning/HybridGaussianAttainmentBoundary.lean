import Cloning.HybridGaussianAttainmentRealBox
import Cloning.HybridGaussianBoundary

/-! The exact hybrid Gaussian optimum also includes vacuum modes. Physical
attainment is already proved on the entire nonnegative thermal parameter range. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k s : ℕ}

namespace PhaseDensity

theorem modeFactor_le_gaussianOptimalPayoff_nonneg (p : PhaseDensity k s)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (n : ℕ) :
    Thermal.classicalBase g ^ ((k : ℝ) / 2) * (∏ i, Thermal.modeFactor g (q i)) ≤
      p.gaussianOptimalPayoff (Real.sqrt g)
        (gaussianThermalPositive a ha q hq0 hq1)
        (gaussianThermalPositive a ha q hq0 hq1) n := by
  rw [← gaussianAmplifierChannel_integral_orbitPayoff (p.expandingPrior n) a ha g hg q hq0 hq1]
  exact integral_orbitPayoff_le_optimal p _ _ _ _ n

/-- Exact optimized expanding-prior hybrid fidelity, including any subset
of vacuum modes. -/
theorem gaussianOptimalPayoff_tendsto_modeFactor_nonneg (p : PhaseDensity k s)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    Tendsto (p.gaussianOptimalPayoff (Real.sqrt g)
      (gaussianThermalPositive a ha q hq0 hq1)
      (gaussianThermalPositive a ha q hq0 hq1)) atTop
      (𝓝 (Thermal.classicalBase g ^ ((k : ℝ) / 2) * ∏ i, Thermal.modeFactor g (q i))) := by
  let A := gaussianThermalPositive a ha q hq0 hq1
  let F : ℝ := Thermal.classicalBase g ^ ((k : ℝ) / 2) * ∏ i, Thermal.modeFactor g (q i)
  have hupper := p.eventually_forall_gaussian_orbitPayoff_le_modeFactor_nonneg a ha g hg q hq0 hq1
  have hopt : ∀ ε > 0, ∀ᶠ n in atTop,
      p.gaussianOptimalPayoff (Real.sqrt g) A A n ≤ F + ε := by
    intro ε hε
    filter_upwards [hupper ε hε] with n hn
    apply csSup_le ⟨_, Set.mem_range_self (gaussianAmplifierChannel g hg)⟩
    rintro _ ⟨Λ, rfl⟩
    exact hn Λ
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall fun n => hc.trans_le
      (modeFactor_le_gaussianOptimalPayoff_nonneg p a ha g hg q hq0 hq1 n)
  · intro c hc
    filter_upwards [hopt ((c - F) / 2) (by change F < c at hc; linarith)] with n hn
    change F < c at hc
    change p.gaussianOptimalPayoff (Real.sqrt g) A A n < c
    linarith

end PhaseDensity

theorem modeFactor_le_realFlatBoxOptimalPayoff_nonneg
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (L : ℝ) :
    Thermal.classicalBase g ^ ((k : ℝ) / 2) * (∏ i, Thermal.modeFactor g (q i)) ≤
      realFlatBoxOptimalPayoff (Real.sqrt g)
        (gaussianThermalPositive a ha q hq0 hq1)
        (gaussianThermalPositive a ha q hq0 hq1) L := by
  rw [← gaussianAmplifierChannel_realFlatBoxPayoff a ha g hg q hq0 hq1 L]
  exact realFlatBoxPayoff_le_optimal _ _ _ _ L

/-- The complete hybrid Gaussian value for actual arbitrary CPTP channels,
all real box radii, and nonnegative thermal parameters. -/
theorem realFlatBoxOptimalPayoff_tendsto_modeFactor_nonneg
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    Tendsto (realFlatBoxOptimalPayoff (Real.sqrt g)
      (gaussianThermalPositive a ha q hq0 hq1)
      (gaussianThermalPositive a ha q hq0 hq1)) atTop
      (𝓝 (Thermal.classicalBase g ^ ((k : ℝ) / 2) * ∏ i, Thermal.modeFactor g (q i))) := by
  let A := gaussianThermalPositive a ha q hq0 hq1
  let F : ℝ := Thermal.classicalBase g ^ ((k : ℝ) / 2) * ∏ i, Thermal.modeFactor g (q i)
  have hupper := eventually_forall_realFlatBox_gaussian_le_modeFactor_nonneg a ha g hg q hq0 hq1
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
      (modeFactor_le_realFlatBoxOptimalPayoff_nonneg a ha g hg q hq0 hq1 L)
  · intro c hc
    filter_upwards [hopt ((c - F) / 2) (by change F < c at hc; linarith)] with L hL
    change F < c at hc
    change realFlatBoxOptimalPayoff (Real.sqrt g) A A L < c
    linarith

end Cloning.Hybrid
