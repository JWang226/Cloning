import Cloning.TensorGibbsTruncation

/-! Vector approximation for a literal contraction yields trace-norm
approximation for its actual trace-repaired CPTP channel. Finite positive
mixtures retain a concrete weighted error bound. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.InfiniteTraceClass
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem QuantumChannel.ofContraction_pure_error (V : H →L[ℂ] K)
    (hV : ∀ x, ‖V x‖ ≤ ‖x‖) (σ : DensityState K)
    (x : H) (y : K) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖(QuantumChannel.ofContraction V hV σ).toLinearMap (vectorProjector x) - vectorProjector y‖ ≤
      4 * ‖V x - y‖ := by
  have hpos : 0 ≤ (vectorProjector x).1 :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (InnerProductSpace.isPositive_rankOne_self x)
  have hr := QuantumChannel.ofContraction_repair_error V hV σ (vectorProjector x) hpos
  rw [conjugationLinearMap_vectorProjector, traceCLM_vectorProjector, traceCLM_vectorProjector,
    Complex.ofReal_re, Complex.ofReal_re, hx, one_pow] at hr
  have hn : ‖V x‖ ≤ 1 := (hV x).trans_eq hx
  have hd : 1 - ‖V x‖ ≤ ‖V x-y‖ := by
    simpa only [hy, norm_sub_rev y] using norm_sub_norm_le y (V x)
  have he : 1 - ‖V x‖^2 ≤ 2 * ‖V x-y‖ := by nlinarith [sq_nonneg (1-‖V x‖)]
  have hp := norm_vectorProjector_sub_le (V x) y
  rw [hy] at hp
  have hp' : ‖vectorProjector (V x)-vectorProjector y‖ ≤ 2*‖V x-y‖ :=
    hp.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have ht := norm_sub_le_norm_sub_add_norm_sub
    ((QuantumChannel.ofContraction V hV σ).toLinearMap (vectorProjector x))
    (vectorProjector (V x)) (vectorProjector y)
  rw [hr] at ht
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual finite mixtures follow from actual vector errors, including the
fallback trace of vectors which leave the compression subspace. -/
theorem QuantumChannel.ofContraction_mixture_error (V : H →L[ℂ] K)
    (hV : ∀ x, ‖V x‖ ≤ ‖x‖) (σ : DensityState K)
    (x : ι → H) (y : ι → K) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ‖(QuantumChannel.ofContraction V hV σ).toLinearMap
        (frameMatrix x (Matrix.diagonal (fun i => (a i : ℂ)))) -
      frameMatrix y (Matrix.diagonal (fun i => (a i : ℂ)))‖ ≤
        4 * ∑ i, a i * ‖V (x i) - y i‖ := by
  rw [frameMatrix_diagonal, frameMatrix_diagonal]
  simp only [map_sum, map_smul]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖(a i : ℂ) • (QuantumChannel.ofContraction V hV σ).toLinearMap (vectorProjector (x i)) -
        (a i : ℂ) • vectorProjector (y i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, a i * (4 * ‖V (x i) - y i‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← smul_sub, norm_smul, Complex.norm_of_nonneg (ha i)]
      exact mul_le_mul_of_nonneg_left (QuantumChannel.ofContraction_pure_error V hV σ _ _ (hx i) (hy i)) (ha i)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

end Cloning.InfiniteTraceClass
