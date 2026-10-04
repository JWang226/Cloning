import Cloning.PCTHybridFidelityTransfer
import Cloning.MixedChannelsBounded

/-! Pointwise mixed-state approximations pass through genuine Bochner mixtures,
including unbounded Gaussian support and changing physical registers. Local LAN
is an explicit input; the integration and final fidelity squeeze are proved. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
open Cloning.Hybrid
namespace Cloning.MixedLANTransfer
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Z : Type*} [MeasurableSpace Z] {ν : Measure Z} [IsFiniteMeasure ν]

/-- Scalar dominated convergence works even when the Banach target varies with
sample size. The error bound is the trace distance bound for normalized states. -/
theorem norm_integral_sub_tendsto_of_pointwise
    {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
    [∀ n, CompleteSpace (E n)] (f g : ∀ n, Z → E n)
    (hf : ∀ n, Integrable (f n) ν) (hg : ∀ n, Integrable (g n) ν)
    (hb : ∀ n, ∀ᵐ z ∂ν, ‖f n z - g n z‖ ≤ 2)
    (hpoint : ∀ᵐ z ∂ν, Tendsto (fun n => ‖f n z - g n z‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖(∫ z, f n z ∂ν) - ∫ z, g n z ∂ν‖) atTop (𝓝 0) := by
  have hi : Tendsto (fun n => ∫ z, ‖f n z - g n z‖ ∂ν) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ : Z => (2 : ℝ))
      (fun n => ((hf n).sub (hg n)).norm.aestronglyMeasurable) (integrable_const _)
      (fun n => (hb n).mono fun z hz => by simpa only [norm_norm] using hz) hpoint
    simpa using h
  apply squeeze_zero (fun n => norm_nonneg _) _ hi
  intro n
  rw [← integral_sub (hf n) (hg n)]
  exact norm_integral_le_integral_norm _

variable {Ω K : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {Q : ℕ → Type*} [∀ n, NormedAddCommGroup (Q n)] [∀ n, InnerProductSpace ℂ (Q n)]
  [∀ n, CompleteSpace (Q n)]

/-- Integrate forward pointwise approximation using only a finite mixing measure.
All physical and comparison integrands are genuine normalized positive states. -/
theorem forward_mixture_tendsto
    (T : ∀ n, QuantumToHybrid (Q n) K μ)
    (ρ : ∀ n, Z → PositiveTraceClass (Q n)) (B : Z → PositiveL1 K μ)
    (hρ : ∀ n z, ‖(ρ n z).1‖ = 1) (hB : ∀ z, ‖(B z).1‖ = 1)
    (hiρ : ∀ n, Integrable (fun z => (ρ n z).1) ν)
    (hiB : Integrable (fun z => (B z).1) ν)
    (hpoint : ∀ᵐ z ∂ν, Tendsto (fun n => ‖(T n).map (ρ n z).1 - (B z).1‖)
      atTop (𝓝 0)) :
    Tendsto (fun n => ‖(T n).map (∫ z, (ρ n z).1 ∂ν) - ∫ z, (B z).1 ∂ν‖)
      atTop (𝓝 0) := by
  have h := norm_integral_sub_tendsto_of_pointwise
    (fun n z => (T n).map (ρ n z).1) (fun _ z => (B z).1)
    (fun n => (T n).map.integrable_comp (hiρ n)) (fun _ => hiB)
    (fun n => Eventually.of_forall fun z => by
      calc
        _ ≤ ‖(T n).map (ρ n z).1‖ + ‖(B z).1‖ := norm_sub_le _ _
        _ = 2 := by rw [(T n).norm_map_of_nonneg _ (ρ n z).2, hρ, hB]; norm_num)
    hpoint
  simpa only [(T _).map.integral_comp_comm (hiρ _)] using h

/-- The reverse mixture estimate permits the physical Hilbert space to change
with n; dominated convergence is applied only to the scalar trace error. -/
theorem reverse_mixture_tendsto
    (S : ∀ n, HybridToQuantum K (Q n) μ)
    (ρ : ∀ n, Z → PositiveTraceClass (Q n)) (B : Z → PositiveL1 K μ)
    (hρ : ∀ n z, ‖(ρ n z).1‖ = 1) (hB : ∀ z, ‖(B z).1‖ = 1)
    (hiρ : ∀ n, Integrable (fun z => (ρ n z).1) ν)
    (hiB : Integrable (fun z => (B z).1) ν)
    (hpoint : ∀ᵐ z ∂ν, Tendsto (fun n => ‖(S n).map (B z).1 - (ρ n z).1‖)
      atTop (𝓝 0)) :
    Tendsto (fun n => ‖(S n).map (∫ z, (B z).1 ∂ν) - ∫ z, (ρ n z).1 ∂ν‖)
      atTop (𝓝 0) := by
  have h := norm_integral_sub_tendsto_of_pointwise
    (fun n z => (S n).map (B z).1) (fun n z => (ρ n z).1)
    (fun n => (S n).map.integrable_comp hiB) hiρ
    (fun n => Eventually.of_forall fun z => by
      calc
        _ ≤ ‖(S n).map (B z).1‖ + ‖(ρ n z).1‖ := norm_sub_le _ _
        _ = 2 := by rw [(S n).norm_map_of_nonneg _ (B z).2, hB, hρ]; norm_num)
    hpoint
  simpa only [(S _).map.integral_comp_comm hiB] using h

/-- A physical output close to the integrated local model has the comparison
fidelity limit once the two pointwise LAN directions and seed errors are given.
No uniform approximation over the unbounded mixing support is assumed. -/
theorem fidelity_tendsto_of_mixed_mixture
    (T : ∀ n, QuantumToHybrid (Q n) K μ) (S : ∀ n, HybridToQuantum K (Q n) μ)
    (ρ σ : ∀ n, PositiveTraceClass (Q n)) (A B : PositiveL1 K μ)
    (R : ∀ n, Z → PositiveTraceClass (Q n)) (G : Z → PositiveL1 K μ)
    (hρ : ∀ n, ‖(ρ n).1‖ = 1) (hσ : ∀ n, ‖(σ n).1‖ = 1)
    (hA : ‖A.1‖ = 1) (hB : ‖B.1‖ = 1)
    (hR : ∀ n z, ‖(R n z).1‖ = 1) (hG : ∀ z, ‖(G z).1‖ = 1)
    (hiR : ∀ n, Integrable (fun z => (R n z).1) ν)
    (hiG : Integrable (fun z => (G z).1) ν)
    (hmixture : B.1 = ∫ z, (G z).1 ∂ν)
    (hphysical : Tendsto (fun n => ‖(σ n).1 - ∫ z, (R n z).1 ∂ν‖) atTop (𝓝 0))
    (hTA : Tendsto (fun n => ‖(T n).map (ρ n).1 - A.1‖) atTop (𝓝 0))
    (hSA : Tendsto (fun n => ‖(S n).map A.1 - (ρ n).1‖) atTop (𝓝 0))
    (hTG : ∀ᵐ z ∂ν, Tendsto (fun n => ‖(T n).map (R n z).1 - (G z).1‖)
      atTop (𝓝 0))
    (hSG : ∀ᵐ z ∂ν, Tendsto (fun n => ‖(S n).map (G z).1 - (R n z).1‖)
      atTop (𝓝 0)) :
    Tendsto (fun n => (ρ n).rootFidelity (σ n)) atTop (𝓝 (A.rootFidelity B)) := by
  have hforward := forward_mixture_tendsto T R G hR hG hiR hiG hTG
  have hreverse := reverse_mixture_tendsto S R G hR hG hiR hiG hSG
  rw [← hmixture] at hforward hreverse
  apply fidelity_tendsto_of_twoWay_mixed_approximation T S ρ σ A B hρ hσ hA hB hTA
  · apply squeeze_zero (fun n => norm_nonneg _) _
      (by simpa using (hphysical.const_mul 2).add hforward)
    intro n
    calc
      _ ≤ ‖(T n).map (σ n).1 - (T n).map (∫ z, (R n z).1 ∂ν)‖ +
          ‖(T n).map (∫ z, (R n z).1 ∂ν) - B.1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * ‖(σ n).1 - ∫ z, (R n z).1 ∂ν‖ +
          ‖(T n).map (∫ z, (R n z).1 ∂ν) - B.1‖ := by
        apply add_le_add _ le_rfl
        rw [← map_sub]
        exact (T n).norm_le_two _
  · exact hSA
  · apply squeeze_zero (fun n => norm_nonneg _) _ (by simpa using hreverse.add hphysical)
    intro n
    calc
      _ ≤ ‖(S n).map B.1 - ∫ z, (R n z).1 ∂ν‖ +
          ‖(∫ z, (R n z).1 ∂ν) - (σ n).1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = _ := by rw [norm_sub_rev (∫ z, (R n z).1 ∂ν) (σ n).1]

end Cloning.MixedLANTransfer
