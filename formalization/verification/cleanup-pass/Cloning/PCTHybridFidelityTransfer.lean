import Cloning.PCTHybridFidelity
import Cloning.MixedChannelsReverseFidelity

/-! Two-sided physical fidelity transfer through actual mixed channels.
The four trace-norm approximation inputs remain explicit. The theorem supplies
only the final fidelity squeeze; it does not assert physical mixed-state LAN. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
open Cloning.Hybrid
namespace Cloning.MixedLANTransfer
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω H K : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Both directions of actual mixed-channel data processing give a quantitative
fidelity sandwich, with trace norms unscaled by a factor of one half. -/
theorem fidelity_sandwich_of_twoWay_mixed
    (T : QuantumToHybrid H K μ) (S : HybridToQuantum K H μ)
    (ρ σ : PositiveTraceClass H) (A B : PositiveL1 K μ)
    (hρ : ‖ρ.1‖ = 1) (hσ : ‖σ.1‖ = 1) (hA : ‖A.1‖ = 1) (hB : ‖B.1‖ = 1) :
    A.rootFidelity B -
        (Real.sqrt ‖S.map A.1 - ρ.1‖ + Real.sqrt ‖S.map B.1 - σ.1‖) ≤
      ρ.rootFidelity σ ∧
    ρ.rootFidelity σ ≤ A.rootFidelity B +
        (Real.sqrt ‖T.map ρ.1 - A.1‖ + Real.sqrt ‖T.map σ.1 - B.1‖) := by
  have hf := T.fidelity_data_processing ρ σ
  have hr := S.fidelity_data_processing A B
  have hcF := PositiveL1.rootFidelity_continuity (T.mapPositive ρ) (T.mapPositive σ) A B
  have hcR := PositiveTraceClass.rootFidelity_continuity
    (S.mapPositive A) (S.mapPositive B) ρ σ
  have hTF : ‖(T.mapPositive σ).1‖ = 1 := (T.norm_map_of_nonneg σ.1 σ.2).trans hσ
  have hSR : ‖(S.mapPositive B).1‖ = 1 := (S.norm_map_of_nonneg B.1 B.2).trans hB
  rw [hTF, hA, Real.sqrt_one, mul_one, mul_one] at hcF
  rw [hSR, hρ, Real.sqrt_one, mul_one, mul_one] at hcR
  have hF := (abs_le.mp hcF).2
  have hR := (abs_le.mp hcR).2
  dsimp only [QuantumToHybrid.mapPositive, HybridToQuantum.mapPositive] at hF hR hf hr
  constructor <;> linarith

/-- The comparison Hilbert space is fixed but physical tensor registers may
vary with sample size. Four genuine trace-norm limits imply the exact physical
fidelity limit; no conclusion about LAN existence is part of the statement. -/
theorem fidelity_tendsto_of_twoWay_mixed_approximation
    {Q : ℕ → Type*} [∀ n, NormedAddCommGroup (Q n)] [∀ n, InnerProductSpace ℂ (Q n)]
    [∀ n, CompleteSpace (Q n)]
    (T : ∀ n, QuantumToHybrid (Q n) K μ) (S : ∀ n, HybridToQuantum K (Q n) μ)
    (ρ σ : ∀ n, PositiveTraceClass (Q n)) (A B : PositiveL1 K μ)
    (hρ : ∀ n, ‖(ρ n).1‖ = 1) (hσ : ∀ n, ‖(σ n).1‖ = 1)
    (hA : ‖A.1‖ = 1) (hB : ‖B.1‖ = 1)
    (hTA : Tendsto (fun n => ‖(T n).map (ρ n).1 - A.1‖) atTop (𝓝 0))
    (hTB : Tendsto (fun n => ‖(T n).map (σ n).1 - B.1‖) atTop (𝓝 0))
    (hSA : Tendsto (fun n => ‖(S n).map A.1 - (ρ n).1‖) atTop (𝓝 0))
    (hSB : Tendsto (fun n => ‖(S n).map B.1 - (σ n).1‖) atTop (𝓝 0)) :
    Tendsto (fun n => (ρ n).rootFidelity (σ n)) atTop (𝓝 (A.rootFidelity B)) := by
  have he : Tendsto (fun n =>
      (Real.sqrt ‖(T n).map (ρ n).1 - A.1‖ + Real.sqrt ‖(T n).map (σ n).1 - B.1‖) +
      (Real.sqrt ‖(S n).map A.1 - (ρ n).1‖ + Real.sqrt ‖(S n).map B.1 - (σ n).1‖))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, zero_add] using (hTA.sqrt.add hTB.sqrt).add (hSA.sqrt.add hSB.sqrt)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ he
  intro n
  rw [Real.norm_eq_abs, abs_le]
  have hb := fidelity_sandwich_of_twoWay_mixed (T n) (S n) (ρ n) (σ n) A B
    (hρ n) (hσ n) hA hB
  have hF : 0 ≤ Real.sqrt ‖(T n).map (ρ n).1 - A.1‖ +
      Real.sqrt ‖(T n).map (σ n).1 - B.1‖ := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hR : 0 ≤ Real.sqrt ‖(S n).map A.1 - (ρ n).1‖ +
      Real.sqrt ‖(S n).map B.1 - (σ n).1‖ := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  constructor <;> linarith [hb.1, hb.2]

end Cloning.MixedLANTransfer
