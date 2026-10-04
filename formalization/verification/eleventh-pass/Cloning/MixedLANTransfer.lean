import Cloning.MixedChannelsFidelity
import Cloning.LAN

/-! LAN converse transfer between actual quantum and hybrid experiments.
The only model-specific inputs are trace-norm approximation errors. Composition,
data processing, and the sharp square-root modulus follow from the proved laws
of genuine mixed CPTP channels; existence of mixed-state LAN maps is not asserted. -/

noncomputable section
open scoped ComplexOrder Topology
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.InfiniteFidelity Cloning.Hybrid
namespace Cloning.MixedLANTransfer
set_option backward.isDefEq.respectTransparency false

variable {Ω A B G H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The genuine positive trace-class operator underlying an analytic density state. -/
def statePositive (ρ : DensityState A) : PositiveTraceClass A :=
  ⟨TraceClass.ofOperator ρ.op ρ.traceClass, ρ.positive⟩

@[simp] theorem norm_statePositive (ρ : DensityState A) : ‖(statePositive ρ).1‖ = 1 := by
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ (statePositive ρ).2]
  change (trace ρ.op ρ.traceClass).re = 1
  rw [ρ.trace_one]
  rfl

@[simp] theorem rootFidelity_statePositive (ρ σ : DensityState A) :
    (statePositive ρ).rootFidelity (statePositive σ) = stateFidelity ρ σ := rfl

/-- The transferred competitor is an actual channel on the whole hybrid space. -/
def transferred (S : HybridToQuantum G A μ) (M : QuantumChannel A B)
    (T : QuantumToHybrid B H μ) : Hybrid.Channel G H μ :=
  (T.compQuantum M).compHybridToQuantum S

@[simp] theorem transferred_apply (S : HybridToQuantum G A μ) (M : QuantumChannel A B)
    (T : QuantumToHybrid B H μ) (X : Lp (TraceClass G) 1 μ) :
    (transferred S M T).map X = T.map (M.toLinearMap (S.map X)) := rfl

/-- The quantum-to-hybrid comparison contracts the input approximation error
uniformly over the competing quantum channel. -/
theorem composition_approximation
    (S : HybridToQuantum G A μ) (M : QuantumChannel A B) (T : QuantumToHybrid B H μ)
    (ρ : PositiveTraceClass A) (Φ : PositiveL1 G μ) {δ : ℝ}
    (hδ : ‖S.map Φ.1 - ρ.1‖ ≤ δ) :
    ‖T.map (M.toLinearMap ρ.1) - (transferred S M T).map Φ.1‖ ≤ δ := by
  rw [transferred_apply]
  apply (T.norm_map_sub_le _ _
    (M.toPositiveTracePreservingMap.map_nonneg ρ.1 ρ.2)
    (M.toPositiveTracePreservingMap.map_nonneg _ (S.map_nonneg Φ.1 Φ.2))).trans
  apply (M.toPositiveTracePreservingMap.norm_map_sub_le _ _ ρ.2
    (S.map_nonneg Φ.1 Φ.2)).trans
  rwa [norm_sub_rev]

/-- Sharp mixed-experiment root-fidelity comparison: the error has no dimension,
competitor, or channel-norm constant. -/
theorem fidelity_transfer
    (S : HybridToQuantum G A μ) (M : QuantumChannel A B) (T : QuantumToHybrid B H μ)
    (ρ : PositiveTraceClass A) (σ : PositiveTraceClass B)
    (Φ : PositiveL1 G μ) (Ψ : PositiveL1 H μ)
    (hσ : ‖σ.1‖ = 1) (hΦ : ‖Φ.1‖ = 1) {δ η : ℝ}
    (hδ : ‖S.map Φ.1 - ρ.1‖ ≤ δ) (hη : ‖T.map σ.1 - Ψ.1‖ ≤ η) :
    (ρ.map M.toPositiveTracePreservingMap).rootFidelity σ ≤
      (Φ.map (transferred S M T)).rootFidelity Ψ + Real.sqrt δ + Real.sqrt η := by
  have hcont := PositiveL1.rootFidelity_continuity
    (T.mapPositive (ρ.map M.toPositiveTracePreservingMap)) (T.mapPositive σ)
    (Φ.map (transferred S M T)) Ψ
  have hBnorm : ‖(T.mapPositive σ).1‖ = 1 :=
    (T.norm_map_of_nonneg σ.1 σ.2).trans hσ
  have hCnorm : ‖(Φ.map (transferred S M T)).1‖ = 1 :=
    (PositiveL1.norm_map _ Φ).trans hΦ
  rw [hBnorm, hCnorm, Real.sqrt_one, mul_one, mul_one] at hcont
  have hd := composition_approximation S M T ρ Φ hδ
  have hcont' :
      |(T.mapPositive (ρ.map M.toPositiveTracePreservingMap)).rootFidelity (T.mapPositive σ) -
        (Φ.map (transferred S M T)).rootFidelity Ψ| ≤ Real.sqrt δ + Real.sqrt η :=
    hcont.trans (add_le_add (Real.sqrt_le_sqrt hd) (Real.sqrt_le_sqrt hη))
  have hdata := T.fidelity_data_processing (ρ.map M.toPositiveTracePreservingMap) σ
  have hle := (le_abs_self
    ((T.mapPositive (ρ.map M.toPositiveTracePreservingMap)).rootFidelity (T.mapPositive σ) -
      (Φ.map (transferred S M T)).rootFidelity Ψ)).trans hcont'
  linarith

/-- The same sharp transfer stated directly for analytic quantum density states. -/
theorem stateFidelity_transfer
    (S : HybridToQuantum G A μ) (M : QuantumChannel A B) (T : QuantumToHybrid B H μ)
    (ρ : DensityState A) (σ : DensityState B) (Φ : PositiveL1 G μ) (Ψ : PositiveL1 H μ)
    (hΦ : ‖Φ.1‖ = 1) {δ η : ℝ}
    (hδ : ‖S.map Φ.1 - (statePositive ρ).1‖ ≤ δ)
    (hη : ‖T.map (statePositive σ).1 - Ψ.1‖ ≤ η) :
    stateFidelity (M.toPositiveTracePreservingMap.mapState ρ) σ ≤
      (Φ.map (transferred S M T)).rootFidelity Ψ + Real.sqrt δ + Real.sqrt η :=
  fidelity_transfer S M T (statePositive ρ) (statePositive σ) Φ Ψ
    (norm_statePositive σ) hΦ hδ hη

/-- Uniform approximation gives the minimax bound against a supremum over all
actual hybrid channels. The comparison maps are fixed before the competitor. -/
theorem minimax_le_bayesValue
    {I P Θ : Type*} [Nonempty I] [MeasurableSpace Θ]
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (S : HybridToQuantum G A μ) (M : I → QuantumChannel A B) (T : QuantumToHybrid B H μ)
    (ρ : P → DensityState A) (σ : P → DensityState B)
    (Φ : Θ → PositiveL1 G μ) (Ψ : Θ → PositiveL1 H μ)
    (hΦ : ∀ θ, ‖(Φ θ).1‖ = 1) (hΨ : ∀ θ, ‖(Ψ θ).1‖ = 1)
    (localChart : Θ → P) (δ η : ℝ)
    (hδ : ∀ θ, ‖S.map (Φ θ).1 - (statePositive (ρ (localChart θ))).1‖ ≤ δ)
    (hη : ∀ θ, ‖T.map (statePositive (σ (localChart θ))).1 - (Ψ θ).1‖ ≤ η)
    (hintegrable : ∀ N : Hybrid.Channel G H μ,
      Integrable (fun θ => ((Φ θ).map N).rootFidelity (Ψ θ)) prior) :
    LAN.minimaxValue (fun i p =>
      stateFidelity ((M i).toPositiveTracePreservingMap.mapState (ρ p)) (σ p)) ≤
      LAN.bayesValue prior
        (fun (N : Hybrid.Channel G H μ) θ => ((Φ θ).map N).rootFidelity (Ψ θ)) +
          (Real.sqrt δ + Real.sqrt η) := by
  apply LAN.minimax_le_bayesValue prior _ _ localChart (fun i => transferred S (M i) T) _
    (fun _ _ => stateFidelity_nonneg _ _)
  · intro i θ
    simpa only [add_assoc] using stateFidelity_transfer S (M i) T
      (ρ (localChart θ)) (σ (localChart θ)) (Φ θ) (Ψ θ) (hΦ θ) (hδ θ) (hη θ)
  · exact hintegrable
  · intro N θ
    simpa only [PositiveL1.norm_map, hΦ θ, hΨ θ, Real.sqrt_one, mul_one] using
      ((Φ θ).map N).rootFidelity_le_sqrt (Ψ θ)

theorem transfer_error_tendsto {δ η : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (δ n) + Real.sqrt (η n)) atTop (𝓝 0) :=
  LAN.transfer_error_tendsto hδ hη

/-- Prior-almost-everywhere approximation suffices: a compact-supported prior
requires estimates only on its compact window, even if the chart is defined on
the entire phase space. -/
theorem minimax_le_bayesValue_ae
    {I P Θ : Type*} [Nonempty I] [MeasurableSpace Θ]
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (S : HybridToQuantum G A μ) (M : I → QuantumChannel A B) (T : QuantumToHybrid B H μ)
    (ρ : P → DensityState A) (σ : P → DensityState B)
    (Φ : Θ → PositiveL1 G μ) (Ψ : Θ → PositiveL1 H μ)
    (hΦ : ∀ θ, ‖(Φ θ).1‖ = 1) (hΨ : ∀ θ, ‖(Ψ θ).1‖ = 1)
    (localChart : Θ → P) (δ η : ℝ)
    (hδ : ∀ᵐ θ ∂prior, ‖S.map (Φ θ).1 - (statePositive (ρ (localChart θ))).1‖ ≤ δ)
    (hη : ∀ᵐ θ ∂prior, ‖T.map (statePositive (σ (localChart θ))).1 - (Ψ θ).1‖ ≤ η)
    (hintegrable : ∀ N : Hybrid.Channel G H μ,
      Integrable (fun θ => ((Φ θ).map N).rootFidelity (Ψ θ)) prior) :
    LAN.minimaxValue (fun i p =>
      stateFidelity ((M i).toPositiveTracePreservingMap.mapState (ρ p)) (σ p)) ≤
      LAN.bayesValue prior
        (fun (N : Hybrid.Channel G H μ) θ => ((Φ θ).map N).rootFidelity (Ψ θ)) +
          (Real.sqrt δ + Real.sqrt η) := by
  let f : I → P → ℝ := fun i p =>
    stateFidelity ((M i).toPositiveTracePreservingMap.mapState (ρ p)) (σ p)
  let g : Hybrid.Channel G H μ → Θ → ℝ := fun N θ => ((Φ θ).map N).rootFidelity (Ψ θ)
  have hupper (N : Hybrid.Channel G H μ) (θ : Θ) : g N θ ≤ 1 := by
    simpa only [g, PositiveL1.norm_map, hΦ θ, hΨ θ, Real.sqrt_one, mul_one] using
      ((Φ θ).map N).rootFidelity_le_sqrt (Ψ θ)
  have hbdd : BddAbove (Set.range (fun N => ∫ θ, g N θ ∂prior)) := by
    refine ⟨1, ?_⟩
    rintro x ⟨N, rfl⟩
    have h := integral_mono (hintegrable N) (integrable_const (1 : ℝ)) (hupper N)
    simpa only [integral_const, probReal_univ, one_smul] using h
  change (⨆ i, ⨅ p, f i p) ≤ _
  apply ciSup_le
  intro i
  have hbelow : BddBelow (Set.range (f i)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨p, rfl⟩
    exact stateFidelity_nonneg _ _
  have hpoint : ∀ᵐ θ ∂prior,
      (⨅ p, f i p) ≤ g (transferred S (M i) T) θ + (Real.sqrt δ + Real.sqrt η) := by
    filter_upwards [hδ, hη] with θ hd he
    apply (ciInf_le hbelow (localChart θ)).trans
    simpa only [f, g, add_assoc] using stateFidelity_transfer S (M i) T
      (ρ (localChart θ)) (σ (localChart θ)) (Φ θ) (Ψ θ) (hΦ θ) hd he
  have havg := integral_mono_ae (integrable_const (⨅ p, f i p))
    ((hintegrable (transferred S (M i) T)).add
      (integrable_const (Real.sqrt δ + Real.sqrt η))) hpoint
  simp only [Pi.add_apply] at havg
  rw [integral_add (hintegrable (transferred S (M i) T)) (integrable_const _)] at havg
  simp only [integral_const, probReal_univ, one_smul] at havg
  exact havg.trans (add_le_add (le_ciSup hbdd (transferred S (M i) T)) le_rfl)

end Cloning.MixedLANTransfer
