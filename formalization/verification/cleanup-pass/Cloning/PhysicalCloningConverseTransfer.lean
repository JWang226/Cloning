import Cloning.PhysicalCloningConverseChart
import Cloning.MixedGaussianConverse

/-! The Gaussian converse applied to the literal physical tensor-state
root-fidelity payoff, over every physical CPTP competitor. -/
noncomputable section
open scoped Topology BigOperators ComplexOrder
open Filter MeasureTheory
namespace Cloning.PhysicalCloningConverse
open Cloning.PCT Cloning.PCTPhysicalState Cloning.TensorCloning
open Cloning.InfiniteTraceClass Cloning.InfiniteFidelity Cloning.Hybrid Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The normalized positive trace-class state used by the physical payoff,
with exactly the same operator in the analytic density-state packaging. -/
def positiveDensity (ρ : PositiveTraceClass H) (hρ : ‖ρ.1‖ = 1) : DensityState H where
  op := ρ.1.1
  positive := ρ.2
  traceClass := ρ.1.2
  trace_one := by
    rw [trace_eq_traceNorm_of_nonneg ρ.2 ρ.1.2]
    change (‖ρ.1‖ : ℂ) = 1
    rw [hρ]
    rfl

@[simp] theorem statePositive_positiveDensity (ρ : PositiveTraceClass H) (hρ : ‖ρ.1‖ = 1) :
    MixedLANTransfer.statePositive (positiveDensity ρ hρ) = ρ := rfl

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def tensorDensity (ρ : Cloning.MatrixFidelity.State A) (n : ℕ) :
    DensityState (Register (Fin n → A)) := positiveDensity (tensorState ρ n) (norm_tensorState ρ n)

@[simp] theorem statePositive_tensorDensity (ρ : Cloning.MatrixFidelity.State A) (n : ℕ) :
    MixedLANTransfer.statePositive (tensorDensity ρ n) = tensorState ρ n := rfl

@[simp] theorem tensorDensity_fidelity (n m : ℕ)
    (Φ : QuantumChannel (Register (Fin n → A)) (Register (Fin m → A)))
    (ρ : Cloning.MatrixFidelity.State A) :
    stateFidelity (Φ.toPositiveTracePreservingMap.mapState (tensorDensity ρ n)) (tensorDensity ρ m) =
      statePayoff n m Φ ρ := rfl

variable {k s : ℕ}

/-- An explicit conditional comparison theorem. The only hypotheses are
trace-norm LAN estimates for the genuine physical tensor states; all payoff,
normalization, composition, integration and minimax adapters are discharged. -/
theorem limsup_statePayoff_le_modeFactor_of_approximations
    {P : Type*} [Nonempty P] (ρ : P → Cloning.MatrixFidelity.State A)
    (m : ℕ → ℕ) (prior : PhaseDensity k s)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (g : ℝ) (hg : 1 < g)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (S : ∀ n, HybridToQuantum (Fock s) (Register (Fin n → A)) (volume : Measure (Fin k → ℝ)))
    (T : ∀ n, QuantumToHybrid (Register (Fin (m n) → A)) (Fock s) (volume : Measure (Fin k → ℝ)))
    (localChart : ℕ → PhaseSpace k s → P) (δ η : ℕ → ℕ → ℝ)
    (hδ : ∀ L, ∀ᶠ n in atTop, ∀ᵐ ξ ∂prior.expandingPrior L,
      ‖(S n).map (translatedPositive ξ (gaussianThermalPositive a ha q hq0 hq1)).1 -
        (tensorState (ρ (localChart n ξ)) n).1‖ ≤ δ L n)
    (hη : ∀ L, ∀ᶠ n in atTop, ∀ᵐ ξ ∂prior.expandingPrior L,
      ‖(T n).map (tensorState (ρ (localChart n ξ)) (m n)).1 -
        (translatedPositive (Real.sqrt g • ξ) (gaussianThermalPositive a ha q hq0 hq1)).1‖ ≤ η L n)
    (hδlim : ∀ L, Tendsto (δ L) atTop (𝓝 0))
    (hηlim : ∀ L, Tendsto (η L) atTop (𝓝 0)) :
    limsup (fun n => LAN.minimaxValue (fun Φ u => statePayoff n (m n) Φ (ρ u))) atTop ≤
      Thermal.classicalBase g ^ ((k : ℝ)/2) * ∏ i, Thermal.modeFactor g (q i) := by
  letI : ∀ n, Nonempty (QuantumChannel (Register (Fin n → A)) (Register (Fin (m n) → A))) :=
    fun n => ⟨QuantumChannel.ofContraction 0 (by intro x; simp)
      (tensorDensity (ρ (Classical.arbitrary P)) (m n))⟩
  exact MixedLANTransfer.limsup_minimax_le_modeFactor_of_mixed_approximation
    prior a ha g hg q hq0 hq1 S (fun _ Φ => Φ) T
    (fun n u => tensorDensity (ρ u) n) (fun n u => tensorDensity (ρ u) (m n))
    localChart δ η hδ hη hδlim hηlim

end Cloning.PhysicalCloningConverse
