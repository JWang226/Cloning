import Cloning.InfiniteFidelityContinuity
import Cloning.InfiniteChannelFidelity
import Cloning.InfiniteCompletelyPositive
import Cloning.LAN

/-!
# LAN comparison estimates on actual Hilbert-space density operators

The trace distance and root fidelity here are the analytic quantities for
trace-class operators on arbitrary complex Hilbert spaces. Positivity and
trace preservation imply the contraction estimate used below; fidelity
continuity is derived from the proved Powers–Størmer inequality. Only the
quantitative approximation estimates are supplied as hypotheses.
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open Filter MeasureTheory
open Cloning.InfiniteTraceClass Cloning.InfiniteFidelity

namespace Cloning.InfiniteLANTransfer

set_option backward.isDefEq.respectTransparency false

variable {A B G H : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual trace distance contracts under every positive trace-preserving map. -/
theorem stateTraceDistance_map_le (M : PositiveTracePreservingMap A B)
    (ρ σ : DensityState A) :
    stateTraceDistance (M.mapState ρ) (M.mapState σ) ≤ stateTraceDistance ρ σ := by
  simp only [stateTraceDistance_eq_norm]
  exact M.norm_map_sub_le (TraceClass.ofOperator ρ.op ρ.traceClass)
    (TraceClass.ofOperator σ.op σ.traceClass) ρ.positive σ.positive

/-- The trace-distance approximation survives composition with arbitrary
positive trace-preserving maps. -/
theorem composition_approximation
    (S : PositiveTracePreservingMap G A) (M : PositiveTracePreservingMap A B)
    (T : PositiveTracePreservingMap B H)
    (ρ : DensityState A) (Φ : DensityState G) {δ : ℝ}
    (hδ : stateTraceDistance (S.mapState Φ) ρ ≤ δ) :
    stateTraceDistance (T.mapState (M.mapState ρ))
      (T.mapState (M.mapState (S.mapState Φ))) ≤ δ := by
  exact (stateTraceDistance_map_le T _ _).trans
    ((stateTraceDistance_map_le M _ _).trans (by rwa [stateTraceDistance_comm]))

/-- Perturbation of both experiments costs the square roots of their actual
trace-distance errors, independently of all Hilbert-space dimensions. -/
theorem fidelity_transfer_perturbation
    (S : PositiveTracePreservingMap G A) (M : PositiveTracePreservingMap A B)
    (T : PositiveTracePreservingMap B H)
    (ρ : DensityState A) (σ : DensityState B) (Φ : DensityState G) (Ψ : DensityState H)
    {δ η : ℝ}
    (hδ : stateTraceDistance (S.mapState Φ) ρ ≤ δ)
    (hη : stateTraceDistance (T.mapState σ) Ψ ≤ η) :
    |stateFidelity (T.mapState (M.mapState ρ)) (T.mapState σ) -
      stateFidelity (T.mapState (M.mapState (S.mapState Φ))) Ψ| ≤
        Real.sqrt δ + Real.sqrt η :=
  stateFidelity_continuity_of_traceNorm_le _ _ _ _
    (composition_approximation S M T ρ Φ hδ) hη

/-- The actual density-state action of a CPTP map. -/
abbrev mapState (M : QuantumChannel A B) (ρ : DensityState A) : DensityState B :=
  M.toPositiveTracePreservingMap.mapState ρ

/-- Composition of actual channels acts by composition on density operators. -/
theorem mapState_comp (T : QuantumChannel B H) (M : QuantumChannel A B)
    (ρ : DensityState A) :
    mapState (T.comp M) ρ = mapState T (mapState M ρ) := rfl

/-- The manuscript's channel-composition transfer estimate for genuine
possibly infinite-dimensional quantum experiments. Complete positivity,
trace-norm contraction, and fidelity continuity are proved channel laws. -/
theorem fidelity_transfer
    (S : QuantumChannel G A) (M : QuantumChannel A B) (T : QuantumChannel B H)
    (ρ : DensityState A) (σ : DensityState B) (Φ : DensityState G) (Ψ : DensityState H)
    {δ η : ℝ}
    (hδ : stateTraceDistance (mapState S Φ) ρ ≤ δ)
    (hη : stateTraceDistance (mapState T σ) Ψ ≤ η) :
    stateFidelity (mapState M ρ) σ ≤
      stateFidelity (mapState T (mapState M (mapState S Φ))) Ψ +
        Real.sqrt δ + Real.sqrt η := by
  have hcont := fidelity_transfer_perturbation S.toPositiveTracePreservingMap
    M.toPositiveTracePreservingMap T.toPositiveTracePreservingMap ρ σ Φ Ψ hδ hη
  have hdata := stateFidelity_data_processing T (mapState M ρ) σ
  have hle := (le_abs_self
    (stateFidelity (mapState T (mapState M ρ)) (mapState T σ) -
      stateFidelity (mapState T (mapState M (mapState S Φ))) Ψ)).trans hcont
  linarith

/-- Uniform approximation by two actual comparison channels transfers the
worst-case fidelity to the optimized Bayes fidelity in the comparison model.
Only approximation errors and integrability of the comparison payoffs are
assumed; existence of model-specific LAN channels is not asserted. -/
theorem minimax_le_bayesValue
    {I P Θ : Type*} [Nonempty I] [MeasurableSpace Θ]
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (S : QuantumChannel G A) (M : I → QuantumChannel A B) (T : QuantumChannel B H)
    (ρ : P → DensityState A) (σ : P → DensityState B)
    (Φ : Θ → DensityState G) (Ψ : Θ → DensityState H)
    (localChart : Θ → P) (δ η : ℝ)
    (hδ : ∀ θ, stateTraceDistance (mapState S (Φ θ)) (ρ (localChart θ)) ≤ δ)
    (hη : ∀ θ, stateTraceDistance (mapState T (σ (localChart θ))) (Ψ θ) ≤ η)
    (hintegrable : ∀ N : QuantumChannel G H,
      Integrable (fun θ => stateFidelity (mapState N (Φ θ)) (Ψ θ)) prior) :
    Cloning.LAN.minimaxValue (fun i p => stateFidelity (mapState (M i) (ρ p)) (σ p)) ≤
      Cloning.LAN.bayesValue prior
        (fun (N : QuantumChannel G H) θ => stateFidelity (mapState N (Φ θ)) (Ψ θ)) +
          (Real.sqrt δ + Real.sqrt η) := by
  apply Cloning.LAN.minimax_le_bayesValue prior _ _ localChart
    (fun i => T.comp ((M i).comp S)) _
    (fun _ _ => stateFidelity_nonneg _ _)
  · intro i θ
    simpa only [mapState_comp, add_assoc] using fidelity_transfer S (M i) T
      (ρ (localChart θ)) (σ (localChart θ)) (Φ θ) (Ψ θ) (hδ θ) (hη θ)
  · exact hintegrable
  · intro N θ
    exact stateFidelity_le_one _ _

/-- Vanishing comparison errors give a vanishing dimension-independent
fidelity error. This is a statement about the actual transfer modulus. -/
theorem transfer_error_tendsto {δ η : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (δ n) + Real.sqrt (η n)) atTop (𝓝 0) :=
  Cloning.LAN.transfer_error_tendsto hδ hη

end Cloning.InfiniteLANTransfer
