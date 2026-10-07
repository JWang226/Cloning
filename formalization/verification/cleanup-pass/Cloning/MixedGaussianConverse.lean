import Cloning.MixedLANTransfer
import Cloning.HybridGaussianAttainmentBoundary

/-! Link the actual mixed-channel comparison to the proved optimized Gaussian
value, in the required fixed-window then large-window order. Physical mixed-state
LAN maps and their approximation bounds remain explicit construction obligations. -/

noncomputable section
open scoped ComplexOrder Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
open Cloning.Hybrid Cloning.MultimodeCoherent
namespace Cloning.MixedLANTransfer
set_option backward.isDefEq.respectTransparency false

variable {k s : ℕ}

theorem norm_gaussianThermalPositive (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    ‖(gaussianThermalPositive a ha q hq0 hq1).1‖ = 1 := by
  change ‖(gaussianThermalField a ha q hq0 hq1).toL1‖ = 1
  rw [PositiveField.norm_toL1, gaussianThermalField, PositiveField.mass_product]
  exact GaussianAffinity.integral_productDensity a ha

theorem norm_translatedPositive (X : HybridPositive k s) (ξ : PhaseSpace k s) :
    ‖(translatedPositive ξ X).1‖ = ‖X.1‖ := PositiveL1.norm_map _ X

variable {A B : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- At a fixed window, the finite quantum minimax is bounded by the genuine
optimized hybrid orbit fidelity plus the sharp comparison error. -/
theorem minimax_le_gaussianOptimalPayoff
    {I P : Type*} [Nonempty I] (p : PhaseDensity k s) (L : ℕ) (r : ℝ)
    (X : HybridPositive k s) (hX : ‖X.1‖ = 1)
    (S : HybridToQuantum (Fock s) A (volume : Measure (Fin k → ℝ)))
    (M : I → QuantumChannel A B)
    (T : QuantumToHybrid B (Fock s) (volume : Measure (Fin k → ℝ)))
    (ρ : P → DensityState A) (σ : P → DensityState B)
    (localChart : PhaseSpace k s → P) (δ η : ℝ)
    (hδ : ∀ᵐ ξ ∂p.expandingPrior L,
      ‖S.map (translatedPositive ξ X).1 - (statePositive (ρ (localChart ξ))).1‖ ≤ δ)
    (hη : ∀ᵐ ξ ∂p.expandingPrior L,
      ‖T.map (statePositive (σ (localChart ξ))).1 - (translatedPositive (r • ξ) X).1‖ ≤ η) :
    LAN.minimaxValue (fun i u =>
      stateFidelity ((M i).toPositiveTracePreservingMap.mapState (ρ u)) (σ u)) ≤
      p.gaussianOptimalPayoff r X X L + (Real.sqrt δ + Real.sqrt η) := by
  exact minimax_le_bayesValue_ae (p.expandingPrior L) S M T ρ σ
    (fun ξ => translatedPositive ξ X) (fun ξ => translatedPositive (r • ξ) X)
    (fun ξ => (norm_translatedPositive X ξ).trans hX)
    (fun ξ => (norm_translatedPositive X (r • ξ)).trans hX)
    localChart δ η hδ hη (fun N => integrable_orbitPayoff (p.expandingPrior L) r N X X)

/-- Actual quantum minimax fidelity is nonnegative for any nonempty family of
competitors and any nonempty physical parameter set. -/
theorem quantum_minimax_nonneg {I P : Type*} [Nonempty I] [Nonempty P]
    (M : I → QuantumChannel A B) (ρ : P → DensityState A) (σ : P → DensityState B) :
    0 ≤ LAN.minimaxValue (fun i u =>
      stateFidelity ((M i).toPositiveTracePreservingMap.mapState (ρ u)) (σ u)) := by
  exact LAN.candidate_le_minimaxValue _ (Classical.arbitrary I) 0
    (fun _ _ => stateFidelity_le_one _ _)
    (fun _ => stateFidelity_nonneg _ _) (fun _ _ => stateFidelity_nonneg _ _)

omit [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] in
/-- Once the actual mixed LAN approximations are constructed, the sharp converse
follows for varying tensor-power Hilbert spaces. The maps are chosen by sample
size alone; no growing-window or window-uniform LAN assumption is used. -/
theorem limsup_minimax_le_modeFactor_of_mixed_approximation
    {Q R : ℕ → Type*} [∀ n, NormedAddCommGroup (Q n)] [∀ n, InnerProductSpace ℂ (Q n)]
    [∀ n, CompleteSpace (Q n)] [∀ n, NormedAddCommGroup (R n)]
    [∀ n, InnerProductSpace ℂ (R n)] [∀ n, CompleteSpace (R n)]
    {I : ℕ → Type*} [∀ n, Nonempty (I n)] {P : Type*} [Nonempty P]
    (p : PhaseDensity k s) (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (g : ℝ) (hg : 1 < g) (q : Fin s → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (S : ∀ n, HybridToQuantum (Fock s) (Q n) (volume : Measure (Fin k → ℝ)))
    (M : ∀ n, I n → QuantumChannel (Q n) (R n))
    (T : ∀ n, QuantumToHybrid (R n) (Fock s) (volume : Measure (Fin k → ℝ)))
    (ρ : ∀ n, P → DensityState (Q n)) (σ : ∀ n, P → DensityState (R n))
    (localChart : ℕ → PhaseSpace k s → P) (δ η : ℕ → ℕ → ℝ)
    (hδ : ∀ L, ∀ᶠ n in atTop, ∀ᵐ ξ ∂p.expandingPrior L,
      ‖(S n).map (translatedPositive ξ (gaussianThermalPositive a ha q hq0 hq1)).1 -
        (statePositive (ρ n (localChart n ξ))).1‖ ≤ δ L n)
    (hη : ∀ L, ∀ᶠ n in atTop, ∀ᵐ ξ ∂p.expandingPrior L,
      ‖(T n).map (statePositive (σ n (localChart n ξ))).1 -
        (translatedPositive (Real.sqrt g • ξ) (gaussianThermalPositive a ha q hq0 hq1)).1‖ ≤ η L n)
    (hδlim : ∀ L, Tendsto (δ L) atTop (𝓝 0))
    (hηlim : ∀ L, Tendsto (η L) atTop (𝓝 0)) :
    limsup (fun n => LAN.minimaxValue (fun i u =>
      stateFidelity ((M n i).toPositiveTracePreservingMap.mapState (ρ n u)) (σ n u))) atTop ≤
        Thermal.classicalBase g ^ ((k : ℝ) / 2) * ∏ i, Thermal.modeFactor g (q i) := by
  let X := gaussianThermalPositive a ha q hq0 hq1
  apply LAN.two_scale_limsup_le _ (p.gaussianOptimalPayoff (Real.sqrt g) X X)
    (fun L n => Real.sqrt (δ L n) + Real.sqrt (η L n)) _
    (fun n => quantum_minimax_nonneg (M n) (ρ n) (σ n))
  · intro L
    filter_upwards [hδ L, hη L] with n hd he
    exact minimax_le_gaussianOptimalPayoff p L (Real.sqrt g) X
      (norm_gaussianThermalPositive a ha q hq0 hq1) (S n) (M n) (T n)
      (ρ n) (σ n) (localChart n) (δ L n) (η L n) hd he
  · intro L
    exact transfer_error_tendsto (hδlim L) (hηlim L)
  · exact p.gaussianOptimalPayoff_tendsto_modeFactor_nonneg a ha g hg q hq0 hq1

end Cloning.MixedLANTransfer
