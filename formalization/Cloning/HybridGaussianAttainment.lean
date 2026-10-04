import Cloning.HybridGaussianAttainmentAction
import Cloning.HybridGaussianAttainmentFidelity
import Cloning.HybridGaussianConverse

/-! Exact attainment and optimized Gaussian hybrid fidelity. The optimization
is over actual completely positive, trace-preserving maps on operator-valued
L1, independently at each expanding-prior scale. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k s : ℕ}

/-- A covariant physical hybrid channel has the same orbit payoff everywhere. -/
theorem orbitPayoff_eq_rootFidelity_of_covariant
    (r : ℝ) (Λ : HybridChannel k s)
    (hcov : ∀ ξ A, Λ.map (hybridTranslation ξ A) =
      hybridTranslation (r • ξ) (Λ.map A))
    (A B : HybridPositive k s) (ξ : PhaseSpace k s) :
    orbitPayoff r Λ A B ξ = (A.map Λ).rootFidelity B := by
  have he : (translatedPositive ξ A).map Λ =
      translatedPositive (r • ξ) (A.map Λ) := by
    apply Subtype.ext
    exact hcov ξ A.1
  rw [orbitPayoff, he, translatedPositive_rootFidelity]

lemma integral_orbitPayoff_le_sqrt (ν : Measure (PhaseSpace k s)) [IsProbabilityMeasure ν]
    (r : ℝ) (Λ : HybridChannel k s) (A B : HybridPositive k s) :
    (∫ ξ, orbitPayoff r Λ A B ξ ∂ν) ≤ Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖ := by
  calc
    _ ≤ ∫ _ξ : PhaseSpace k s, Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖ ∂ν := by
      apply integral_mono (integrable_orbitPayoff ν r Λ A B) (integrable_const _)
      intro ξ
      rw [orbitPayoff_eq_translated]
      simpa only [PositiveL1.norm_map] using
        PositiveL1.rootFidelity_le_sqrt (A.map (translatedChannel r Λ ξ)) B
    _ = _ := by simp

/-- The physical classical dilation and quantum-limited amplifier attain the
full Gaussian hybrid fidelity at every joint displacement. -/
theorem gaussianAmplifierChannel_orbitPayoff
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (ξ : PhaseSpace k s) :
    orbitPayoff (Real.sqrt g) (gaussianAmplifierChannel g hg)
      (gaussianThermalPositive a ha q hq0 hq1)
      (gaussianThermalPositive a ha q hq0 hq1) ξ =
      Thermal.classicalBase g ^ ((k : ℝ) / 2) * ∏ i, Thermal.modeFactor g (q i) := by
  rw [orbitPayoff_eq_rootFidelity_of_covariant _ _ (gaussianAmplifierChannel_covariant g hg),
    gaussianAmplifierChannel_gaussianThermalPositive a ha g hg q hq0 hq1]
  exact gaussianThermalField_amplified_toPositiveL1_rootFidelity a ha g hg q
    hq0 hq1

/-- The attained value holds under any probability prior. -/
theorem gaussianAmplifierChannel_integral_orbitPayoff
    (ν : Measure (PhaseSpace k s)) [IsProbabilityMeasure ν]
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    (∫ ξ, orbitPayoff (Real.sqrt g) (gaussianAmplifierChannel g hg)
      (gaussianThermalPositive a ha q hq0 hq1)
      (gaussianThermalPositive a ha q hq0 hq1) ξ ∂ν) =
      Thermal.classicalBase g ^ ((k : ℝ) / 2) * ∏ i, Thermal.modeFactor g (q i) := by
  simp_rw [gaussianAmplifierChannel_orbitPayoff a ha g hg q hq0 hq1]
  simp

namespace PhaseDensity

/-- The actual optimal average payoff, allowing a new arbitrary CPTP hybrid
channel at every scale. -/
def gaussianOptimalPayoff (p : PhaseDensity k s) (r : ℝ)
    (A B : HybridPositive k s) (n : ℕ) : ℝ :=
  sSup (Set.range (fun Λ : HybridChannel k s => ∫ ξ, orbitPayoff r Λ A B ξ ∂p.expandingPrior n))

lemma gaussianOptimalPayoff_bddAbove (p : PhaseDensity k s) (r : ℝ)
    (A B : HybridPositive k s) (n : ℕ) :
    BddAbove (Set.range (fun Λ : HybridChannel k s =>
      ∫ ξ, orbitPayoff r Λ A B ξ ∂p.expandingPrior n)) := by
  refine ⟨Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖, ?_⟩
  rintro _ ⟨Λ, rfl⟩
  exact integral_orbitPayoff_le_sqrt _ r Λ A B

lemma integral_orbitPayoff_le_optimal (p : PhaseDensity k s) (r : ℝ)
    (Λ : HybridChannel k s) (A B : HybridPositive k s) (n : ℕ) :
    (∫ ξ, orbitPayoff r Λ A B ξ ∂p.expandingPrior n) ≤ p.gaussianOptimalPayoff r A B n :=
  le_csSup (gaussianOptimalPayoff_bddAbove p r A B n) (Set.mem_range_self Λ)

/-- A single physical channel bounds the optimum below at every scale. -/
theorem modeFactor_le_gaussianOptimalPayoff (p : PhaseDensity k s)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (n : ℕ) :
    Thermal.classicalBase g ^ ((k : ℝ) / 2) * (∏ i, Thermal.modeFactor g (q i)) ≤
      p.gaussianOptimalPayoff (Real.sqrt g)
        (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1)
        (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1) n := by
  rw [← gaussianAmplifierChannel_integral_orbitPayoff (p.expandingPrior n) a ha g hg q (fun i => (hq0 i).le) hq1]
  exact integral_orbitPayoff_le_optimal p _ _ _ _ n

/-- The full optimized Gaussian hybrid problem has this exact limit, with
supremum over channels before the expanding-prior limit. -/
theorem gaussianOptimalPayoff_tendsto_modeFactor (p : PhaseDensity k s)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    Tendsto (p.gaussianOptimalPayoff (Real.sqrt g)
      (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1)
      (gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1)) atTop
      (𝓝 (Thermal.classicalBase g ^ ((k : ℝ) / 2) * ∏ i, Thermal.modeFactor g (q i))) := by
  let A := gaussianThermalPositive a ha q (fun i => (hq0 i).le) hq1
  let F : ℝ := Thermal.classicalBase g ^ ((k : ℝ) / 2) * ∏ i, Thermal.modeFactor g (q i)
  have hupper := p.eventually_forall_gaussian_orbitPayoff_le_modeFactor a ha g hg q hq0 hq1
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
      (modeFactor_le_gaussianOptimalPayoff p a ha g hg q hq0 hq1 n)
  · intro c hc
    filter_upwards [hopt ((c - F) / 2) (by change F < c at hc; linarith)] with n hn
    change F < c at hc
    change p.gaussianOptimalPayoff (Real.sqrt g) A A n < c
    linarith

end PhaseDensity
end Cloning.Hybrid
