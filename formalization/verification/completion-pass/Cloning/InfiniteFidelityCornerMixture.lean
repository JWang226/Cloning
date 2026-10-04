import Cloning.InfiniteFidelityCornerLimit
import Cloning.InfiniteFidelityFiniteMixture

/-! Normalized finite mixtures on varying Hilbert spaces inherit a common
corner limit. The number and weights of components may change arbitrarily. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology Classical
open Filter
namespace Cloning.InfiniteFidelityCorner
open Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem tendsto_probability_weighted_complex
    {J : ℕ → Type*} [∀ N, Fintype (J N)]
    (q : ∀ N, J N → ℝ) (hq : ∀ N i, 0 ≤ q N i)
    (hs : ∀ N, ∑ i, q N i = 1) (z : ∀ N, J N → ℂ) (c : ℂ)
    (hz : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, ‖z N i-c‖ < ε) :
    Tendsto (fun N ↦ ∑ i, (q N i : ℂ) * z N i) atTop (𝓝 c) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hz (ε/2) (by positivity)] with N hN
  rw [dist_eq_norm]
  have he : (∑ i, (q N i : ℂ) * z N i)-c =
      ∑ i, (q N i : ℂ) * (z N i-c) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Complex.ofReal_sum, hs N, Complex.ofReal_one, one_mul]
  rw [he]
  calc
    ‖∑ i, (q N i : ℂ) * (z N i-c)‖ ≤ ∑ i, ‖(q N i : ℂ) * (z N i-c)‖ := norm_sum_le _ _
    _ ≤ ∑ i, q N i * (ε/2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hq N i)]
      exact mul_le_mul_of_nonneg_left (hN i).le (hq N i)
    _ = ε/2 := by rw [← Finset.sum_mul, hs N, one_mul]
    _ < ε := by linarith

theorem finiteMixture_norm_one
    {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Fintype J] (q : J → ℝ) (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i = 1)
    (A : J → PositiveTraceClass H) (hA : ∀ i, ‖(A i).1‖ = 1) :
    ‖(PositiveTraceClass.finiteMixture q hq A).1‖ = 1 := by
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ (PositiveTraceClass.finiteMixture q hq A).2]
  change (traceCLM (PositiveTraceClass.finiteMixture q hq A).1).re = 1
  simp only [PositiveTraceClass.finiteMixture_val, map_sum, map_smul, Complex.re_sum,
    smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have ht i : (traceCLM (A i).1).re = 1 := by
    change (trace (A i).1.1 (A i).1.2).re = 1
    rw [← TraceClass.norm_eq_trace_re_of_nonneg _ (A i).2, hA i]
  simp only [ht, mul_one]
  exact hs

section Varying
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {G : ℕ → Type*}
  [∀ N, NormedAddCommGroup (G N)] [∀ N, InnerProductSpace ℂ (G N)] [∀ N, CompleteSpace (G N)]
variable {J : ℕ → Type*} [∀ N, Fintype (J N)]
variable (I : ℕ → Type*) [∀ R, Fintype (I R)] [∀ R, DecidableEq (I R)]

/-- Uniform convergence of component coefficients is enough for exact mixture
fidelity convergence. Positivity and unit mass supply the physical tail bounds. -/
theorem tendsto_finiteMixture_rootFidelity_of_corner_coefficients
    (q : ∀ N, J N → ℝ) (hq : ∀ N i, 0 ≤ q N i) (hs : ∀ N, ∑ i, q N i = 1)
    (A : ∀ N, J N → PositiveTraceClass (G N)) (B : ∀ N, PositiveTraceClass (G N))
    (C D : PositiveTraceClass H)
    (hA : ∀ N i, ‖(A N i).1‖ = 1) (hB : ∀ N, ‖(B N).1‖ = 1)
    (hC : ‖C.1‖ = 1) (hD : ‖D.1‖ = 1)
    (v : ∀ N R, I R → G N) (w : ∀ R, I R → H)
    (hv : ∀ R, ∀ᶠ N in atTop, Orthonormal ℂ (v N R))
    (hw : ∀ R, Orthonormal ℂ (w R))
    (hCA : ∀ R i j (ε : ℝ), 0 < ε → ∀ᶠ N in atTop, ∀ a : J N,
      ‖⟪v N R i, (A N a).1.1 (v N R j)⟫_ℂ - ⟪w R i, C.1.1 (w R j)⟫_ℂ‖ < ε)
    (hDB : ∀ R i j, Tendsto (fun N ↦ ⟪v N R i, (B N).1.1 (v N R j)⟫_ℂ)
      atTop (𝓝 ⟪w R i, D.1.1 (w R j)⟫_ℂ))
    (hCm : Tendsto (fun R ↦ mass (w R) C.1) atTop (𝓝 1))
    (hDm : Tendsto (fun R ↦ mass (w R) D.1) atTop (𝓝 1)) :
    Tendsto (fun N ↦ (PositiveTraceClass.finiteMixture (q N) (hq N) (A N)).rootFidelity (B N))
      atTop (𝓝 (C.rootFidelity D)) := by
  apply tendsto_rootFidelity_of_corner_coefficients I _ B C D
    (fun N ↦ finiteMixture_norm_one (q N) (hq N) (hs N) (A N) (hA N)) hB hC hD
    v w hv hw ?_ hDB hCm hDm
  intro R i j
  have h := tendsto_probability_weighted_complex q hq hs
    (fun N a ↦ ⟪v N R i, (A N a).1.1 (v N R j)⟫_ℂ)
    ⟪w R i, C.1.1 (w R j)⟫_ℂ (hCA R i j)
  convert h using 1
  ext N
  change ⟪v N R i, inclusionCLM
    (∑ a, (q N a : ℂ) • (A N a).1) (v N R j)⟫_ℂ = _
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, inner_sum, inner_smul_right, inclusionCLM_apply]

end Varying
end Cloning.InfiniteFidelityCorner
