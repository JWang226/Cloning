import Cloning.UniformCoherent
import Cloning.MultimodeCoherent

/-! Strong Hilbert convergence from concrete number coefficients and exact
normalization. This allows complex phases to vary and includes zero coefficients. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace Cloning.GeneralCoherent
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Unit vectors in an occupation Hilbert space converge in norm when every
complex coefficient converges to that of a unit vector. The proof uses finite
number cutoffs and the actual Hilbert inner product. -/
theorem lp_tendsto_of_coefficients {ι : Type*}
    (x : ℕ → lp (fun _ : ι => ℂ) 2) (y : lp (fun _ : ι => ℂ) 2)
    (hx : ∀ n, ‖x n‖ = 1) (hy : ‖y‖ = 1)
    (hpoint : ∀ i, Tendsto (fun n => x n i) atTop (𝓝 (y i))) :
    Tendsto x atTop (𝓝 y) := by
  classical
  have hi : Tendsto (fun n => ⟪x n, y⟫_ℂ) atTop (𝓝 ⟪y, y⟫_ℂ) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hf := lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) y
    obtain ⟨S, hS⟩ := (hf.eventually (Metric.ball_mem_nhds y (by positivity : 0 < ε / 4))).exists
    let v := ∑ i ∈ S, lp.single 2 i (y i)
    have htail : ‖y - v‖ < ε / 4 := by
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev, v] using hS
    have hfin : Tendsto (fun n => ⟪x n, v⟫_ℂ) atTop (𝓝 ⟪y, v⟫_ℂ) := by
      simp only [v, inner_sum, lp.inner_single_right]
      exact tendsto_finset_sum S (fun i _ => (hpoint i).inner tendsto_const_nhds)
    filter_upwards [hfin.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 2))] with n hn
    have hm : ‖⟪x n, v⟫_ℂ - ⟪y, v⟫_ℂ‖ < ε / 2 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hn
    have hxn : ‖⟪x n, y - v⟫_ℂ‖ ≤ ‖y - v‖ := by
      simpa only [hx, one_mul] using norm_inner_le_norm (x n) (y - v)
    have hyn : ‖⟪y, y - v⟫_ℂ‖ ≤ ‖y - v‖ := by
      simpa only [hy, one_mul] using norm_inner_le_norm y (y - v)
    have hid : ⟪x n, y⟫_ℂ - ⟪y, y⟫_ℂ =
        (⟪x n, v⟫_ℂ - ⟪y, v⟫_ℂ) + (⟪x n, y - v⟫_ℂ - ⟪y, y - v⟫_ℂ) := by
      simp only [inner_sub_right]
      ring
    rw [dist_eq_norm, hid]
    have hb := norm_add_le (⟪x n, v⟫_ℂ - ⟪y, v⟫_ℂ)
      (⟪x n, y - v⟫_ℂ - ⟪y, y - v⟫_ℂ)
    have hc := norm_sub_le ⟪x n, y - v⟫_ℂ ⟪y, y - v⟫_ℂ
    linarith
  have hsq : Tendsto (fun n => ‖x n - y‖ ^ (2 : ℕ)) atTop (𝓝 0) := by
    have hn (n : ℕ) : ‖x n - y‖ ^ (2 : ℕ) = 2 - 2 * (⟪x n, y⟫_ℂ).re := by
      have h := norm_sub_sq (𝕜 := ℂ) (x n) y
      simp only [hx, hy, one_pow] at h
      change ‖x n - y‖ ^ 2 = 1 - 2 * (⟪x n, y⟫_ℂ).re + 1 at h
      linarith
    simp_rw [hn]
    have hre : (⟪y, y⟫_ℂ).re = 1 := by
      simp [inner_self_eq_norm_sq_to_K, hy]
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).sub ((Complex.continuous_re.tendsto _).comp hi |>.const_mul 2)
    simpa only [Function.comp_def, hre, mul_one, sub_self] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hsq

end Cloning.GeneralCoherent
